"""Pipeline state definition for the TLA+ specification workflow."""

from typing import TypedDict, Optional


class PipelineState(TypedDict):
    # Inputs
    documentation: str

    # Agent 1 output
    informal_spec: str

    # Agent 2 output
    formal_spec: str

    # Validation
    validation_error: Optional[str]

    # Agent 3 output
    review_feedback: Optional[str]
    revision_count: int