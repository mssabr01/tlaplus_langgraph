# TLA+ Exemplar Specs

Place well-written `.tla` PlusCal specifications in this directory.
They will be loaded as few-shot examples for Agent 2 (the formalizer).

Good exemplars should demonstrate:
- Proper PlusCal c-syntax with correct label placement
- Tight `TypeOK` invariants covering all variables
- Bounded integer ranges (0..MAX_X, never Nat)
- SYMMETRY sets for interchangeable constants
- Small, model-checkable state spaces
- Clear separation of safety invariants and liveness properties
- A matching .cfg section or comments describing TLC configuration

Suggested sources:
- Lamport's TLA+ Examples repository: https://github.com/tlaplus/Examples
- Hillel Wayne's Practical TLA+: https://learntla.com
- Markus Kuppe's TLA+ Community Modules examples
