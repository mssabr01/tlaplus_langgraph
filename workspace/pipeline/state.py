"""Pipeline state definition for the TLA+ specification workflow."""

from typing import TypedDict, Optional


class PipelineState(TypedDict):
    # ── Inputs ──────────────────────────────────────────────────────────
    documentation: str  # Raw project documentation (may be multi-file)
    exemplars: str  # Optional: well-written PlusCal specs for few-shot guidance

    # ── Agent 1 output ──────────────────────────────────────────────────
    informal_spec: str  # Structured informal specification (markdown)

    # ── Invariant agent output ──────────────────────────────────────────
    invariants: list[str]  # Named invariant operators extracted/generated
    cfg_content: str  # Generated TLC .cfg file content

    # ── Agent 2 output ──────────────────────────────────────────────────
    formal_spec: str  # PlusCal/TLA+ specification

    # ── Validation (syntax) ─────────────────────────────────────────────
    validation_error: Optional[str]
    validation_retries: int  # Syntax-fix attempts (separate from semantic revisions)

    # ── TLC model checking ──────────────────────────────────────────────
    tlc_result: Optional[str]  # Raw TLC output
    tlc_stats: Optional[dict]  # Parsed: states explored, depth, time, etc.
    counterexample: Optional[str]  # TLC counterexample trace (if invariant violated)

    # ── Agent 3 (review) output ─────────────────────────────────────────
    review_feedback: Optional[str]
    revision_count: int  # Semantic revision iterations

    # ── History ─────────────────────────────────────────────────────────
    revision_history: list[dict]  # List of {revision, informal_spec, formal_spec, feedback}
