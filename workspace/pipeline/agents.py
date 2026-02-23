"""Agent definitions for the TLA+ specification pipeline.

Large content (docs, specs) is written to /tmp/pipeline_workspace/ so that
prompts stay under the ~80K char OS ARG_MAX limit. Each agent gets a short
prompt referencing file paths, plus allowed_tools=["Read"] so it can read them.
"""

import os
import re
import logging

from claude_sdk import call_claude_code
from tlc_tools import parse_spec, translate_pluscal, run_tlc
from state import PipelineState

logger = logging.getLogger(__name__)

# Shared workspace for writing files that agents will read
AGENT_WORKSPACE = "/tmp/pipeline_workspace"
os.makedirs(AGENT_WORKSPACE, exist_ok=True)


def _write_agent_file(name: str, content: str) -> str:
    """Write content to a file in the agent workspace, return its path."""
    path = os.path.join(AGENT_WORKSPACE, name)
    with open(path, "w") as f:
        f.write(content)
    return path

# ---------------------------------------------------------------------------
# System prompts
# ---------------------------------------------------------------------------

AGENT1_SYSTEM = """\
You are a formal methods expert specializing in TLA+ and PlusCal.
Your job is to read project documentation and produce an INFORMAL specification
that maps cleanly to a model-checkable PlusCal spec.

## What to identify

For each concern, provide a clearly labeled markdown section:

### 1. Scope & Abstraction Level
- State the SINGLE protocol concern this spec targets
  (e.g., "swap correctness", "oracle update liveness", "fee accounting").
- List which details are essential vs. which can be safely abstracted to
  nondeterministic choice. Justify each abstraction.
- State the number and roles of concurrent actors to model (keep it minimal:
  typically 2-3 processes).

### 2. State Variables
- Name each variable, its type, and its finite domain.
- Every integer variable MUST have an explicit upper bound (e.g., 0..MAX_BALANCE).
- Use sets/enumerations rather than unbounded naturals wherever possible.

### 3. Constants
- List every tunable parameter as a CONSTANT with a small default value
  suitable for model checking (e.g., NumProcesses = 2, MaxTokens = 3).

### 4. Initial State Predicate

### 5. Actions (state transitions)
- For each action: name, precondition, effect, atomicity boundary.
- Mark which actions should have weak/strong fairness.

### 6. Safety Invariants
- TypeOK: the type-correctness invariant constraining all variable domains.
  THIS IS MANDATORY — always include it.
- Domain-specific safety properties (e.g., "total supply is conserved").
- For each invariant, explain why it must hold.

### 7. Liveness Properties
- Progress guarantees from the documentation.
- Which fairness assumptions they require.

### 8. Symmetry Opportunities
- Identify sets of interchangeable values (e.g., process IDs, token addresses)
  that TLC can exploit via symmetry reduction.

Be precise about concurrency and shared-state access patterns.
Keep the model SMALL — prefer fewer variables and actions over completeness.
A spec that TLC can check in <100k states is far more useful than an exhaustive
spec that explodes."""

AGENT2_SYSTEM = """\
You are a TLA+/PlusCal expert who writes formally correct, model-checkable
specifications. Given an informal specification, produce a complete PlusCal
specification embedded in a TLA+ module.

## Hard Requirements

1. Use PlusCal c-syntax.
2. EXTENDS: include Integers, FiniteSets, Sequences, TLC as needed.
3. CONSTANTS: declare every tunable parameter. Add a comment with the
   recommended small value for model checking (e.g., \\* default: 2).
4. ALL integer ranges must be bounded: use 0..MAX_X, never Nat or Int.
5. NEVER use unbounded Seq(S) — use BoundedSeq(S, MaxLen) or fixed-length
   tuples/functions.
6. Write the PlusCal algorithm with proper labels for atomicity.
7. Use `with` blocks for nondeterministic choice from finite sets.

## Invariants (after the PlusCal translation markers)

8. ALWAYS define a TypeOK operator that constrains every variable to its
   finite domain. This is the single most important invariant.
9. Define each safety invariant as a named TLA+ operator.
10. Define liveness properties using temporal operators ([]<>, <>[], etc.).

## State Explosion Prevention

11. Use SYMMETRY sets for interchangeable constants (process IDs, tokens).
12. Prefer model values over integers for identifiers.
13. Minimize the number of labels — each label is a state; merge sequential
    assignments under one label when atomicity allows.
14. Avoid auxiliary variables that only exist for bookkeeping.
15. If you need a counter, bound it tightly (0..2 not 0..100).

## Output

Output ONLY the complete .tla file content. No markdown fences, no explanation.
The spec MUST parse with SANY and translate with the PlusCal translator.

{exemplar_section}"""

AGENT3_SYSTEM = """\
You are a verification engineer reviewing a TLA+ formal specification
against the original project documentation AND model-checking results.

## Review Categories

For each issue found, output:
- SEVERITY: critical / major / minor
- CATEGORY: one of the categories below
- DESCRIPTION: clear description
- SUGGESTION: specific fix

### Categories

1. missing_behavior — actions in the docs not captured in the spec
2. extra_behavior — the spec allows behaviors the docs forbid
3. wrong_invariant — an invariant that doesn't match documented requirements
4. missing_invariant — a documented requirement not captured as an invariant
5. liveness_gap — progress properties from docs not specified
6. abstraction — important details abstracted away that matter
7. state_explosion_risk — unbounded types, missing symmetry, unnecessary
   variables/labels that will cause TLC to blow up
8. missing_type_invariant — variables without TypeOK coverage
9. cfg_mismatch — the .cfg file doesn't match the spec's invariants/properties
10. counterexample_issue — TLC found a counterexample that reveals a real bug
    vs. a spec modeling error

## TLC Results Review

If TLC results are provided:
- If a counterexample was found, analyze whether it reveals a real protocol
  bug or a spec modeling error. Suggest the appropriate fix.
- If state space is large (>100k states), suggest specific reductions
  (symmetry, smaller constants, fewer processes, merging labels).
- If TLC succeeded, note which invariants were verified and at what scale.

## Verdict

If the spec is correct and complete: output "APPROVED" with justification.
Otherwise, list all issues."""

INVARIANT_AGENT_SYSTEM = """\
You are a TLA+ invariant specialist. Given a formal PlusCal/TLA+ specification
and its informal description, your job is to:

1. Generate a complete TypeOK invariant covering EVERY variable in the spec.
   - Each variable must be constrained to its exact finite domain.
   - Use set membership (\\in), function spaces (->), and bounded ranges.

2. Extract or generate safety invariants from the informal spec.
   - Conservation laws (e.g., total supply is constant).
   - Ordering constraints (e.g., monotonically increasing timestamps).
   - Access control (e.g., only owner can modify).

3. Extract or generate liveness properties.
   - Progress: every pending request is eventually served.
   - Termination: the protocol eventually reaches a stable state.

4. Generate a TLC .cfg file with:
   - SPECIFICATION Spec
   - All INVARIANT declarations (TypeOK first, then safety invariants)
   - All PROPERTY declarations (liveness/temporal)
   - CONSTANT assignments using small finite values for model checking
   - SYMMETRY sets where applicable

## Output Format

Output two clearly separated sections:

### INVARIANTS
```tla
TypeOK == ...

SafetyInvariant1 == ...
```

### CFG
```
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT SafetyInvariant1
PROPERTY LivenessProperty1
CONSTANTS
  NumProcesses = 2
  MaxBalance = 3
SYMMETRY SymmetrySet
```

Output ONLY these two sections. No other commentary."""

CFG_AGENT_SYSTEM = """\
You are a TLC configuration specialist. Given a TLA+ specification and a list
of invariant/property names, produce a correct .cfg file for TLC model checking.

Requirements:
- SPECIFICATION Spec (or the correct spec name from the module)
- List all INVARIANT names (TypeOK first)
- List all PROPERTY names (temporal/liveness)
- Set all CONSTANTS to small finite values suitable for model checking:
  - Process counts: 2-3
  - Balance/amount ranges: 0..3 or 0..5
  - Sequence bounds: 2-3
- Use MODEL VALUES for identifier sets (tokens, addresses)
- Define SYMMETRY sets for interchangeable model values
- CONSTANT definitions should use = for simple values, <- for model value sets

Output ONLY the .cfg file content."""


# ---------------------------------------------------------------------------
# Helper: parse TLC output for stats and counterexamples
# ---------------------------------------------------------------------------

def parse_tlc_output(raw_output: str) -> dict:
    """Extract structured information from TLC's raw output."""
    result = {
        "success": False,
        "states_found": None,
        "distinct_states": None,
        "depth": None,
        "counterexample": None,
        "violated_invariant": None,
        "error_message": None,
    }

    if "Model checking completed" in raw_output:
        result["success"] = True

    # Extract state counts
    m = re.search(r"(\d+) states generated, (\d+) distinct states found", raw_output)
    if m:
        result["states_found"] = int(m.group(1))
        result["distinct_states"] = int(m.group(2))

    m = re.search(r"The depth of the complete state graph search is (\d+)", raw_output)
    if m:
        result["depth"] = int(m.group(1))

    # Check for invariant violations
    m = re.search(r"Invariant (\w+) is violated", raw_output)
    if m:
        result["violated_invariant"] = m.group(1)
        result["success"] = False

    # Extract counterexample trace
    if "Error: " in raw_output or "is violated" in raw_output:
        # Capture everything from the error to the end or next section
        trace_match = re.search(
            r"(Error:.*?(?:State \d+:.*?)*)(?:\n\n|\Z)",
            raw_output,
            re.DOTALL,
        )
        if trace_match:
            result["counterexample"] = trace_match.group(1).strip()
        result["success"] = False

    if "Error: " in raw_output and not result.get("counterexample"):
        error_match = re.search(r"Error: (.+?)(?:\n|$)", raw_output)
        if error_match:
            result["error_message"] = error_match.group(1)

    return result


# ---------------------------------------------------------------------------
# Agent node functions
# ---------------------------------------------------------------------------

def agent1_doc_to_informal(state: PipelineState) -> PipelineState:
    """Agent 1: Documentation -> Informal specification."""
    logger.info("Agent 1: Generating informal specification from documentation")

    docs_path = _write_agent_file("documentation.md", state["documentation"])

    feedback_line = ""
    if state.get("review_feedback"):
        fb_path = _write_agent_file("review_feedback.md", state["review_feedback"])
        feedback_line = f"\n- Review feedback to address: {fb_path}"

    counterexample_line = ""
    if state.get("counterexample"):
        ce_path = _write_agent_file("counterexample.txt", state["counterexample"])
        counterexample_line = f"\n- TLC counterexample trace: {ce_path}"

    prompt = f"""\
Read the project documentation at {docs_path} and produce a complete informal
TLA+ specification following the structure in your system prompt.

Focus on producing a spec that TLC can model-check with small constants
(2-3 processes, balances 0..3).{feedback_line}{counterexample_line}

Output ONLY the informal specification content. Do not include any commentary
about reading files."""

    state["informal_spec"] = call_claude_code(
        prompt=prompt,
        system_prompt=AGENT1_SYSTEM,
        max_turns=5,
        cwd=AGENT_WORKSPACE,
        allowed_tools=["Read"],
    )

    logger.info("Agent 1: Informal specification complete")
    return state


def agent2_formalize(state: PipelineState) -> PipelineState:
    """Agent 2: Informal spec -> Formal PlusCal/TLA+."""
    logger.info("Agent 2: Formalizing specification")

    # Build exemplar section if examples are available
    exemplar_section = ""
    if state.get("exemplars"):
        exemplar_section = (
            f"## Reference Examples\n\n"
            f"Study these well-written PlusCal specs for style and idiom guidance:\n\n"
            f"{state['exemplars']}"
        )

    system = AGENT2_SYSTEM.format(exemplar_section=exemplar_section)

    # Write large content to files
    informal_path = _write_agent_file("informal_spec.md", state["informal_spec"])

    extra_files = ""
    if state.get("review_feedback"):
        fb_path = _write_agent_file("review_feedback.md", state["review_feedback"])
        extra_files += f"\n- Review feedback to address: {fb_path}"
    if state.get("validation_error"):
        ve_path = _write_agent_file("validation_error.txt", state["validation_error"])
        extra_files += f"\n- Syntax error to fix: {ve_path}"
    if state.get("counterexample"):
        ce_path = _write_agent_file("counterexample.txt", state["counterexample"])
        extra_files += (
            f"\n- TLC counterexample trace: {ce_path}"
            f"\n  Fix the spec so this trace is either impossible (if it's a real bug) "
            f"or the invariant is corrected (if it's a modeling error)."
        )

    prompt = f"""\
Read the informal specification at {informal_path} and convert it into a complete,
syntactically valid PlusCal specification in a TLA+ module.{extra_files}

Output ONLY the complete .tla file content. No markdown fences, no explanation,
no commentary about reading files."""

    state["formal_spec"] = call_claude_code(
        prompt=prompt,
        system_prompt=system,
        max_turns=5,
        cwd=AGENT_WORKSPACE,
        allowed_tools=["Read"],
    )

    logger.info("Agent 2: Formal specification complete")
    return state


def validate_spec(state: PipelineState) -> PipelineState:
    """Validation node: Run PlusCal translator and SANY parser."""
    logger.info("Validator: Checking spec syntax")

    spec = state["formal_spec"]

    # PlusCal translation (if spec contains PlusCal)
    if "algorithm" in spec.lower() or "fair algorithm" in spec.lower():
        success, output = translate_pluscal(spec)
        if not success:
            state["validation_error"] = f"PlusCal translation failed:\n{output}"
            state["validation_retries"] = state.get("validation_retries", 0) + 1
            logger.warning("Validator: PlusCal translation failed")
            return state
        spec = output
        state["formal_spec"] = spec

    # SANY parse check
    success, output = parse_spec(spec)
    if not success:
        state["validation_error"] = f"SANY parse failed:\n{output}"
        state["validation_retries"] = state.get("validation_retries", 0) + 1
        logger.warning("Validator: SANY parse failed")
        return state

    state["validation_error"] = None
    logger.info("Validator: Spec is syntactically valid")
    return state


def generate_invariants(state: PipelineState) -> PipelineState:
    """Invariant agent: Generate TypeOK, safety invariants, liveness props, and .cfg."""
    logger.info("Invariant Agent: Generating invariants and TLC config")

    # Write large content to files
    informal_path = _write_agent_file("informal_spec.md", state["informal_spec"])
    formal_path = _write_agent_file("formal_spec.tla", state["formal_spec"])

    extra_files = ""
    if state.get("review_feedback"):
        fb_path = _write_agent_file("review_feedback.md", state["review_feedback"])
        extra_files = f"\n- Previous review feedback: {fb_path}"

    prompt = f"""\
Read the formal PlusCal/TLA+ specification at {formal_path} and the informal
description at {informal_path}. Generate all invariants and a TLC .cfg file
following the format in your system prompt.{extra_files}

Output ONLY the INVARIANTS and CFG sections. No other commentary."""

    output = call_claude_code(
        prompt=prompt,
        system_prompt=INVARIANT_AGENT_SYSTEM,
        max_turns=5,
        cwd=AGENT_WORKSPACE,
        allowed_tools=["Read"],
    )

    # Parse the invariants and cfg sections from output
    invariant_names = []
    cfg_content = ""

    # Extract invariant names (TypeOK and others)
    for match in re.finditer(r"^(\w+)\s*==", output, re.MULTILINE):
        invariant_names.append(match.group(1))

    # Extract CFG section
    cfg_match = re.search(r"### CFG\s*\n```\s*\n(.*?)```", output, re.DOTALL)
    if cfg_match:
        cfg_content = cfg_match.group(1).strip()
    else:
        # Try without markdown fences
        cfg_match = re.search(r"SPECIFICATION\s+\w+.*", output, re.DOTALL)
        if cfg_match:
            cfg_content = cfg_match.group(0).strip()

    # Extract invariant TLA+ definitions and append to formal spec if not already present
    inv_match = re.search(r"### INVARIANTS\s*\n```(?:tla)?\s*\n(.*?)```", output, re.DOTALL)
    if inv_match:
        inv_definitions = inv_match.group(1).strip()
        # Check if invariants already exist in spec
        if "TypeOK" not in state["formal_spec"]:
            # Insert before the final ====
            spec = state["formal_spec"]
            if "====" in spec:
                spec = spec.rsplit("====", 1)[0] + "\n" + inv_definitions + "\n\n===="
            else:
                spec += "\n\n" + inv_definitions
            state["formal_spec"] = spec

    state["invariants"] = invariant_names
    state["cfg_content"] = cfg_content

    logger.info(f"Invariant Agent: Generated {len(invariant_names)} invariants")
    return state


def model_check(state: PipelineState) -> PipelineState:
    """TLC model-checking node: Run TLC and capture results."""
    logger.info("TLC: Running model checker")

    spec = state["formal_spec"]
    cfg = state.get("cfg_content", "")

    if not cfg:
        logger.warning("TLC: No .cfg content available, skipping model check")
        state["tlc_result"] = "SKIPPED: No .cfg file generated"
        state["tlc_stats"] = None
        state["counterexample"] = None
        return state

    # Run TLC with the spec and cfg
    success, raw_output = run_tlc(spec, cfg)

    state["tlc_result"] = raw_output

    # Parse structured results
    stats = parse_tlc_output(raw_output)
    state["tlc_stats"] = stats

    if stats.get("counterexample"):
        state["counterexample"] = stats["counterexample"]
        logger.warning(
            f"TLC: Invariant '{stats.get('violated_invariant', '?')}' violated. "
            f"Counterexample captured."
        )
    else:
        state["counterexample"] = None

    if stats["success"]:
        logger.info(
            f"TLC: Model checking passed. "
            f"{stats.get('distinct_states', '?')} distinct states, "
            f"depth {stats.get('depth', '?')}"
        )
    else:
        logger.warning(f"TLC: Model checking failed. Output: {raw_output[:500]}")

    return state


def agent3_review(state: PipelineState) -> PipelineState:
    """Agent 3: Review formal spec against documentation and TLC results."""
    logger.info("Agent 3: Reviewing formal spec")

    # Write large content to files
    docs_path = _write_agent_file("documentation.md", state["documentation"])
    formal_path = _write_agent_file("formal_spec.tla", state["formal_spec"])

    extra_files = ""
    if state.get("cfg_content"):
        cfg_path = _write_agent_file("spec.cfg", state["cfg_content"])
        extra_files += f"\n- TLC configuration: {cfg_path}"
    if state.get("tlc_result"):
        tlc_path = _write_agent_file("tlc_output.txt", state["tlc_result"])
        extra_files += f"\n- TLC output: {tlc_path}"
    if state.get("tlc_stats"):
        stats = state["tlc_stats"]
        extra_files += (
            f"\n- TLC stats: {stats.get('distinct_states', '?')} distinct states, "
            f"depth {stats.get('depth', '?')}, success={stats.get('success', '?')}"
        )
    if state.get("counterexample"):
        ce_path = _write_agent_file("counterexample.txt", state["counterexample"])
        extra_files += f"\n- COUNTEREXAMPLE found: {ce_path}"

    prompt = f"""\
Review the TLA+ formal specification at {formal_path} against the original
documentation at {docs_path}.{extra_files}

Follow the review categories in your system prompt. Output your review with
severity, category, description, and suggestion for each issue found.
End with APPROVED or a list of all issues. No commentary about reading files."""

    review = call_claude_code(
        prompt=prompt,
        system_prompt=AGENT3_SYSTEM,
        max_turns=5,
        cwd=AGENT_WORKSPACE,
        allowed_tools=["Read"],
    )

    # Save revision history
    history_entry = {
        "revision": state.get("revision_count", 0),
        "informal_spec": state.get("informal_spec", ""),
        "formal_spec": state.get("formal_spec", ""),
        "cfg_content": state.get("cfg_content", ""),
        "review_feedback": review,
        "tlc_stats": state.get("tlc_stats"),
        "counterexample": state.get("counterexample"),
    }
    history = state.get("revision_history", [])
    history.append(history_entry)
    state["revision_history"] = history

    state["review_feedback"] = review
    state["revision_count"] = state.get("revision_count", 0) + 1

    logger.info(f"Agent 3: Review complete (revision {state['revision_count']})")
    return state
