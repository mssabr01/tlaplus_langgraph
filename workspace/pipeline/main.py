"""TLA+ Specification Pipeline - LangGraph orchestration using Claude Code SDK."""

import json
import logging
import os
import sys

from langgraph.graph import StateGraph, END
from state import PipelineState
from agents import (
    agent1_doc_to_informal,
    agent2_formalize,
    validate_spec,
    generate_invariants,
    model_check,
    agent3_review,
)

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(name)s] %(message)s")
logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

MAX_REVISIONS = 3            # Semantic revision iterations (full loop)
MAX_VALIDATION_RETRIES = 2   # Syntax-fix attempts before moving on
MAX_TLC_RETRIES = 2          # Model-check fix attempts before review


# ---------------------------------------------------------------------------
# Documentation & exemplar loaders
# ---------------------------------------------------------------------------

def load_documentation(docs_path: str) -> str:
    """Load documentation from a file or directory (recursive).

    If docs_path is a directory, all .md/.txt/.rst files are concatenated
    with file-path headers so the agent knows what came from where.
    """
    if os.path.isfile(docs_path):
        with open(docs_path) as f:
            return f.read()

    if not os.path.isdir(docs_path):
        raise FileNotFoundError(f"Documentation path not found: {docs_path}")

    parts: list[str] = []
    extensions = {".md", ".txt", ".rst", ".html"}

    for root, _dirs, files in sorted(os.walk(docs_path)):
        for fname in sorted(files):
            if os.path.splitext(fname)[1].lower() in extensions:
                fpath = os.path.join(root, fname)
                rel = os.path.relpath(fpath, docs_path)
                with open(fpath) as f:
                    content = f.read()
                parts.append(f"--- FILE: {rel} ---\n{content}")

    if not parts:
        raise ValueError(f"No documentation files found in {docs_path}")

    logger.info(f"Loaded {len(parts)} documentation files from {docs_path}")
    return "\n\n".join(parts)


def load_exemplars(exemplar_dir: str) -> str:
    """Load .tla exemplar files from a directory for few-shot guidance."""
    if not os.path.isdir(exemplar_dir):
        return ""

    parts: list[str] = []
    for fname in sorted(os.listdir(exemplar_dir)):
        if fname.endswith(".tla"):
            fpath = os.path.join(exemplar_dir, fname)
            with open(fpath) as f:
                content = f.read()
            parts.append(f"--- EXEMPLAR: {fname} ---\n{content}")

    if parts:
        logger.info(f"Loaded {len(parts)} exemplar specs from {exemplar_dir}")
    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Routing functions
# ---------------------------------------------------------------------------

def route_after_validation(state: PipelineState) -> str:
    """After validation: syntax errors route back to Agent 2 for fixes."""
    if state.get("validation_error"):
        if state.get("validation_retries", 0) < MAX_VALIDATION_RETRIES:
            logger.info("Routing back to formalize for syntax fix")
            return "formalize"
        else:
            logger.warning("Max validation retries exceeded. Proceeding to invariants.")
            return "generate_invariants"
    return "generate_invariants"


def route_after_model_check(state: PipelineState) -> str:
    """After TLC: if counterexample found, can loop back to formalize."""
    stats = state.get("tlc_stats") or {}

    if stats.get("counterexample") or not stats.get("success", True):
        # TLC found issues — route to review so agent can decide
        # whether it's a spec bug or invariant bug
        return "review"

    # TLC passed clean — still go to review for semantic check
    return "review"


def route_after_review(state: PipelineState) -> str:
    """After review: loop back if issues found, within revision limits."""
    feedback = state.get("review_feedback", "")

    if "APPROVED" in feedback.upper():
        logger.info("Spec approved by reviewer.")
        return END

    if state.get("revision_count", 0) >= MAX_REVISIONS:
        logger.warning("Max revisions reached. Outputting current spec.")
        return END

    feedback_lower = feedback.lower()
    conceptual_keywords = [
        "missing_behavior", "missing_invariant",
        "liveness_gap", "abstraction",
    ]

    if any(kw in feedback_lower for kw in conceptual_keywords):
        logger.info("Conceptual issue found. Routing back to Agent 1.")
        return "informal_spec"

    if "counterexample_issue" in feedback_lower or "wrong_invariant" in feedback_lower:
        logger.info("Invariant/counterexample issue. Routing back to formalize.")
        return "formalize"

    if "state_explosion_risk" in feedback_lower:
        logger.info("State explosion risk. Routing back to formalize.")
        return "formalize"

    if "cfg_mismatch" in feedback_lower:
        logger.info("CFG mismatch. Routing back to invariant generation.")
        return "generate_invariants"

    # Default: route to formalize for generic fixes
    logger.info("Generic issue. Routing back to formalize.")
    return "formalize"


# ---------------------------------------------------------------------------
# Build the graph
# ---------------------------------------------------------------------------

def build_graph() -> StateGraph:
    """Build the LangGraph pipeline.

    Flow:
        informal_spec -> formalize -> validate -> generate_invariants -> model_check -> review
                            ^            ^              ^                                |
                            |            |              |                                |
                            +------------+--------------+--------------------------------+
                                    (conditional feedback loops)
    """
    graph = StateGraph(PipelineState)

    # Nodes
    graph.add_node("informal_spec", agent1_doc_to_informal)
    graph.add_node("formalize", agent2_formalize)
    graph.add_node("validate", validate_spec)
    graph.add_node("generate_invariants", generate_invariants)
    graph.add_node("model_check", model_check)
    graph.add_node("review", agent3_review)

    # Edges
    graph.set_entry_point("informal_spec")
    graph.add_edge("informal_spec", "formalize")
    graph.add_edge("formalize", "validate")

    graph.add_conditional_edges("validate", route_after_validation, {
        "formalize": "formalize",
        "generate_invariants": "generate_invariants",
    })

    graph.add_edge("generate_invariants", "model_check")

    graph.add_conditional_edges("model_check", route_after_model_check, {
        "review": "review",
    })

    graph.add_conditional_edges("review", route_after_review, {
        "informal_spec": "informal_spec",
        "formalize": "formalize",
        "generate_invariants": "generate_invariants",
        END: END,
    })

    return graph.compile()


# ---------------------------------------------------------------------------
# Output writing
# ---------------------------------------------------------------------------

def write_outputs(state: PipelineState, output_path: str):
    """Write all pipeline outputs to the output directory."""
    os.makedirs(output_path, exist_ok=True)

    with open(os.path.join(output_path, "informal_spec.md"), "w") as f:
        f.write(state.get("informal_spec", ""))

    with open(os.path.join(output_path, "Spec.tla"), "w") as f:
        f.write(state.get("formal_spec", ""))

    if state.get("cfg_content"):
        with open(os.path.join(output_path, "Spec.cfg"), "w") as f:
            f.write(state["cfg_content"])

    if state.get("review_feedback"):
        with open(os.path.join(output_path, "review.md"), "w") as f:
            f.write(state["review_feedback"])

    if state.get("tlc_result"):
        with open(os.path.join(output_path, "tlc_output.txt"), "w") as f:
            f.write(state["tlc_result"])

    # Write revision history
    history = state.get("revision_history", [])
    if history:
        history_dir = os.path.join(output_path, "history")
        os.makedirs(history_dir, exist_ok=True)

        for entry in history:
            rev = entry.get("revision", 0)
            rev_dir = os.path.join(history_dir, f"rev_{rev}")
            os.makedirs(rev_dir, exist_ok=True)

            if entry.get("informal_spec"):
                with open(os.path.join(rev_dir, "informal_spec.md"), "w") as f:
                    f.write(entry["informal_spec"])

            if entry.get("formal_spec"):
                with open(os.path.join(rev_dir, "Spec.tla"), "w") as f:
                    f.write(entry["formal_spec"])

            if entry.get("cfg_content"):
                with open(os.path.join(rev_dir, "Spec.cfg"), "w") as f:
                    f.write(entry["cfg_content"])

            if entry.get("review_feedback"):
                with open(os.path.join(rev_dir, "review.md"), "w") as f:
                    f.write(entry["review_feedback"])

            # Write stats as JSON
            meta = {
                "revision": rev,
                "tlc_stats": entry.get("tlc_stats"),
                "counterexample": entry.get("counterexample"),
            }
            with open(os.path.join(rev_dir, "meta.json"), "w") as f:
                json.dump(meta, f, indent=2)

    logger.info(f"Outputs written to {output_path}/")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def run_pipeline(
    docs_path: str,
    output_path: str = "./specs",
    exemplar_dir: str = "./exemplars",
):
    """Run the TLA+ specification pipeline."""

    documentation = load_documentation(docs_path)
    exemplars = load_exemplars(exemplar_dir)

    initial_state: PipelineState = {
        "documentation": documentation,
        "exemplars": exemplars,
        "informal_spec": "",
        "invariants": [],
        "cfg_content": "",
        "formal_spec": "",
        "validation_error": None,
        "validation_retries": 0,
        "tlc_result": None,
        "tlc_stats": None,
        "counterexample": None,
        "review_feedback": None,
        "revision_count": 0,
        "revision_history": [],
    }

    app = build_graph()

    logger.info("Starting TLA+ specification pipeline")
    final_state = app.invoke(initial_state)

    write_outputs(final_state, output_path)

    return final_state


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python main.py <docs_path> [output_path] [exemplar_dir]")
        print("  docs_path:     Path to documentation file or directory")
        print("  output_path:   Where to write specs (default: ./specs)")
        print("  exemplar_dir:  Directory with .tla exemplar files (default: ./exemplars)")
        sys.exit(1)

    docs = sys.argv[1]
    output = sys.argv[2] if len(sys.argv) > 2 else "./specs"
    exemplars = sys.argv[3] if len(sys.argv) > 3 else "./exemplars"

    run_pipeline(docs, output, exemplars)
