"""TLA+ Specification Pipeline - LangGraph orchestration using Claude Code SDK."""

import logging
import sys
import os

from langgraph.graph import StateGraph, END
from state import PipelineState
from agents import (
    agent1_doc_to_informal,
    agent2_formalize,
    validate_spec,
    agent3_review,
)

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(name)s] %(message)s")
logger = logging.getLogger(__name__)

MAX_REVISIONS = 3
MAX_VALIDATION_RETRIES = 2


# ---------------------------------------------------------------------------
# Routing functions
# ---------------------------------------------------------------------------

def route_after_validation(state: PipelineState) -> str:
    """After validation: if syntax errors, send back to Agent 2 for fixes."""
    if state.get("validation_error"):
        if state.get("revision_count", 0) < MAX_VALIDATION_RETRIES:
            # Feed the error back as review feedback for Agent 2
            state["review_feedback"] = (
                f"SYNTAX ERROR - fix this before review:\n{state['validation_error']}"
            )
            return "formalize"
        else:
            logger.error("Max validation retries exceeded. Proceeding with errors.")
            return "review"
    return "review"


def route_after_review(state: PipelineState) -> str:
    """After review: if issues found and under revision limit, loop back."""
    feedback = state.get("review_feedback", "")

    if "APPROVED" in feedback.upper():
        logger.info("Spec approved by reviewer.")
        return END

    if state.get("revision_count", 0) < MAX_REVISIONS:
        feedback_lower = feedback.lower()
        conceptual_keywords = [
            "missing_behavior", "missing_invariant",
            "liveness_gap", "abstraction",
        ]
        if any(kw in feedback_lower for kw in conceptual_keywords):
            logger.info("Conceptual issue found. Routing back to Agent 1.")
            return "informal_spec"
        else:
            logger.info("Formalization issue found. Routing back to Agent 2.")
            return "formalize"

    logger.warning("Max revisions reached. Outputting current spec.")
    return END


# ---------------------------------------------------------------------------
# Build the graph
# ---------------------------------------------------------------------------

def build_graph() -> StateGraph:
    graph = StateGraph(PipelineState)

    # Nodes
    graph.add_node("informal_spec", agent1_doc_to_informal)
    graph.add_node("formalize", agent2_formalize)
    graph.add_node("validate", validate_spec)
    graph.add_node("review", agent3_review)

    # Edges
    graph.set_entry_point("informal_spec")
    graph.add_edge("informal_spec", "formalize")
    graph.add_edge("formalize", "validate")

    graph.add_conditional_edges("validate", route_after_validation, {
        "formalize": "formalize",
        "review": "review",
    })

    graph.add_conditional_edges("review", route_after_review, {
        "informal_spec": "informal_spec",
        "formalize": "formalize",
        END: END,
    })

    return graph.compile()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def run_pipeline(docs_path: str, output_path: str = "./specs"):
    """Run the TLA+ specification pipeline."""

    with open(docs_path) as f:
        documentation = f.read()

    initial_state: PipelineState = {
        "documentation": documentation,
        "informal_spec": "",
        "formal_spec": "",
        "validation_error": None,
        "review_feedback": None,
        "revision_count": 0,
    }

    app = build_graph()

    logger.info("Starting TLA+ specification pipeline")
    final_state = app.invoke(initial_state)

    # Write outputs
    os.makedirs(output_path, exist_ok=True)

    with open(os.path.join(output_path, "informal_spec.md"), "w") as f:
        f.write(final_state["informal_spec"])

    with open(os.path.join(output_path, "Spec.tla"), "w") as f:
        f.write(final_state["formal_spec"])

    if final_state.get("review_feedback"):
        with open(os.path.join(output_path, "review.md"), "w") as f:
            f.write(final_state["review_feedback"])

    logger.info(f"Pipeline complete. Outputs written to {output_path}/")
    return final_state


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python main.py <docs_path> [output_path]")
        print("  docs_path:   Path to project documentation (markdown, txt, etc.)")
        print("  output_path: Where to write specs (default: ./specs)")
        sys.exit(1)

    docs = sys.argv[1]
    output = sys.argv[2] if len(sys.argv) > 2 else "./specs"

    run_pipeline(docs, output)