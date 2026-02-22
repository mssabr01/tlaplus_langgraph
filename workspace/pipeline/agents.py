"""Agent definitions for the TLA+ specification pipeline."""

from claude_sdk import call_claude_code
from tlc_tools import parse_spec, translate_pluscal, run_tlc
from state import PipelineState

import logging

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# System prompts for each agent role
# ---------------------------------------------------------------------------

AGENT1_SYSTEM = """You are a formal methods expert specializing in TLA+ and PlusCal.
Your job is to read project documentation and produce an INFORMAL specification
using concepts that map cleanly to TLA+/PlusCal.

You must identify and clearly define:
- State variables and their types/domains
- Initial state predicates
- Actions (state transitions) and their preconditions/effects
- Safety invariants (properties that must always hold)
- Liveness properties (properties that must eventually hold)
- Fairness conditions (weak/strong fairness on actions)

Output a structured informal spec in markdown with clear sections for each of the above.
Be precise about concurrency, atomicity boundaries, and shared state."""

AGENT2_SYSTEM = """You are a TLA+/PlusCal expert who writes formally correct specifications.
Given an informal specification, produce a complete, syntactically valid PlusCal
specification embedded in a TLA+ module.

Requirements:
- Use PlusCal algorithm syntax (either p-syntax or c-syntax, prefer c-syntax)
- Include all necessary EXTENDS (Integers, Sequences, FiniteSets, TLC as needed)
- Define CONSTANTS with clear descriptions
- Write the PlusCal algorithm with proper labels for atomicity
- Define all invariants as TLA+ operators after the PlusCal block
- Include a .cfg section or comment describing the model checking configuration
- The spec MUST parse cleanly with SANY and translate with the PlusCal translator

Output ONLY the complete .tla file content, no markdown fences or explanation."""

AGENT3_SYSTEM = """You are a verification engineer reviewing a TLA+ formal specification
against the original project documentation.

Your job is to find:
1. Missing behaviors: actions in the docs not captured in the spec
2. Extra behaviors: the spec allows behaviors the docs forbid
3. Incorrect invariants: invariants that don't match documented requirements
4. Missing invariants: documented requirements not captured as invariants
5. Liveness gaps: progress properties from docs not specified
6. Abstraction issues: the spec abstracts away details that matter

For each issue found, output:
- SEVERITY: critical / major / minor
- CATEGORY: missing_behavior | extra_behavior | wrong_invariant | missing_invariant | liveness_gap | abstraction
- DESCRIPTION: clear description of the issue
- SUGGESTION: specific fix recommendation

If the spec is correct, output "APPROVED" with a brief justification."""

# ---------------------------------------------------------------------------
# Agent node functions (called by LangGraph)
# ---------------------------------------------------------------------------

def agent1_doc_to_informal(state: PipelineState) -> PipelineState:
    """Agent 1: Read documentation, produce informal specification."""
    logger.info("Agent 1: Generating informal specification from documentation")

    prompt = f"""Analyze the following project documentation and produce a complete
informal TLA+ specification.

{state['documentation']}

{"Previous review feedback to address:" + chr(10) + state['review_feedback'] if state.get('review_feedback') else ""}"""

    state["informal_spec"] = call_claude_code(
        prompt=prompt,
        system_prompt=AGENT1_SYSTEM,
        max_turns=3,
    )

    logger.info("Agent 1: Informal specification complete")
    return state


def agent2_formalize(state: PipelineState) -> PipelineState:
    """Agent 2: Convert informal spec to formal PlusCal/TLA+."""
    logger.info("Agent 2: Formalizing specification")

    prompt = f"""Convert the following informal specification into a complete,
syntactically valid PlusCal specification in a TLA+ module.

INFORMAL SPECIFICATION:
{state['informal_spec']}

{"Previous review feedback to address:" + chr(10) + state['review_feedback'] if state.get('review_feedback') else ""}"""

    formal_spec = call_claude_code(
        prompt=prompt,
        system_prompt=AGENT2_SYSTEM,
        max_turns=3,
    )

    state["formal_spec"] = formal_spec
    logger.info("Agent 2: Formal specification complete")
    return state


def validate_spec(state: PipelineState) -> PipelineState:
    """Validation node: Run SANY parser and PlusCal translator."""
    logger.info("Validator: Checking spec syntax with SANY and PlusCal translator")

    spec = state["formal_spec"]

    # Try PlusCal translation first (if spec contains PlusCal)
    if "algorithm" in spec.lower() or "fair algorithm" in spec.lower():
        success, output = translate_pluscal(spec)
        if not success:
            state["validation_error"] = f"PlusCal translation failed:\n{output}"
            logger.warning("Validator: PlusCal translation failed")
            return state
        # Use the translated version going forward
        spec = output
        state["formal_spec"] = spec

    # Parse check
    success, output = parse_spec(spec)
    if not success:
        state["validation_error"] = f"SANY parse failed:\n{output}"
        logger.warning("Validator: SANY parse failed")
        return state

    state["validation_error"] = None
    logger.info("Validator: Spec is syntactically valid")
    return state


def agent3_review(state: PipelineState) -> PipelineState:
    """Agent 3: Review formal spec against documentation."""
    logger.info("Agent 3: Reviewing formal spec against documentation")

    prompt = f"""Review this TLA+ formal specification against the original documentation.

DOCUMENTATION:
{state['documentation']}

FORMAL SPECIFICATION:
{state['formal_spec']}"""

    review = call_claude_code(
        prompt=prompt,
        system_prompt=AGENT3_SYSTEM,
        max_turns=3,
    )

    state["review_feedback"] = review
    state["revision_count"] = state.get("revision_count", 0) + 1
    logger.info(f"Agent 3: Review complete (revision {state['revision_count']})")
    return state