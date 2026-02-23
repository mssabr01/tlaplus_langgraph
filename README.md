# TLA+ Specification Pipeline

LLM-driven pipeline that ingests protocol documentation, generates formal TLA+/PlusCal specifications, model-checks them with TLC, and iteratively refines until invariants hold and the spec is semantically correct.

## Architecture

```
docs/ ──→ Agent 1 ──→ Agent 2 ──→ Validator ──→ Invariant Agent ──→ TLC ──→ Reviewer
          (informal)   (formal)    (SANY/pcal)   (TypeOK + .cfg)    (check)   (semantic)
              ↑            ↑            ↑               ↑                        |
              └────────────┴────────────┴───────────────┴────────────────────────┘
                                    feedback loops
```

Six pipeline nodes, orchestrated by LangGraph:

| Node | Role | Tool |
|------|------|------|
| `informal_spec` | Docs → structured informal spec with scope, variables, invariants, symmetry | Claude |
| `formalize` | Informal spec → PlusCal in TLA+ module | Claude |
| `validate` | Syntax check via SANY parser + PlusCal translator | `pcal`, `sany` |
| `generate_invariants` | TypeOK + safety/liveness invariants + `.cfg` file | Claude |
| `model_check` | Run TLC, capture state counts, counterexamples | `tlc` |
| `review` | Semantic review against docs + TLC results, route feedback | Claude |

### Routing logic

- **Validation fails** → back to `formalize` (up to 2 retries)
- **TLC finds counterexample** → `review` decides if spec bug or invariant bug
- **Review finds conceptual gap** → back to `informal_spec`
- **Review finds formalization issue** → back to `formalize`
- **Review finds cfg mismatch** → back to `generate_invariants`
- **Review approves** → done

Maximum 3 full revision loops. All intermediate artifacts saved to `history/`.

### File-based prompt delivery

All large content (documentation, specs, feedback) is written to `/tmp/pipeline_workspace/` as files. Each Claude sub-agent receives a short prompt referencing file paths and uses the `Read` tool to access them. System prompts are also written to files. This avoids the OS ARG_MAX (~2MB) limit on subprocess CLI arguments that the Claude Agent SDK uses internally.

## Setup

### Authentication

The pipeline uses your Claude subscription quota via OAuth — not the paid API. Authenticate inside the container once; credentials persist via a Docker volume:

```bash
docker compose run --rm tla-agent claude auth login
```

### Docker

```bash
# Build and run the pipeline
docker compose run --rm tla-agent

# Open a shell for debugging
docker compose run --rm tla-agent bash
```

The compose service mounts `./specs` for output, `./workspace/pipeline` for live code reload, and a named volume for Claude auth persistence.

### Running directly (without Docker)

Requires Python 3.12+, Java 21+, Node.js 22+, and `tla2tools.jar` on the classpath.

```bash
pip install -r requirements.txt
python workspace/pipeline/main.py <docs_path> [output_path] [exemplar_dir]
```

### Environment variables

| Variable | Default | Description |
|----------|---------|-------------|
| `CLAUDE_MODEL` | `claude-sonnet-4-5` | Model for sub-agents |
| `CLAUDE_MAX_RETRIES` | `5` | Retry attempts on rate limit / empty response |
| `CLAUDE_RETRY_DELAY` | `60` | Base delay (seconds) between retries (multiplied by attempt) |
| `TLC_TIMEOUT` | `300` | TLC model checker timeout (seconds) |

## Output

```
specs/
  informal_spec.md     # Structured informal specification
  Spec.tla             # Formal PlusCal/TLA+ specification
  Spec.cfg             # TLC configuration (constants, invariants, symmetry)
  review.md            # Final review feedback
  tlc_output.txt       # Raw TLC output
  history/             # Every revision's artifacts
    rev_0/
      informal_spec.md
      Spec.tla
      Spec.cfg
      review.md
      meta.json        # TLC stats, counterexample
    rev_1/
      ...
```

## State Explosion Prevention

The pipeline is specifically designed to produce specs TLC can check with small state spaces. Key mechanisms:

1. **Agent 1** must declare a single protocol concern per spec, bound all integer domains, and identify symmetry sets
2. **Agent 2** is instructed to never use `Nat`/`Int` (only `0..MAX_X`), avoid unbounded `Seq`, minimize labels, and use symmetry
3. **Invariant Agent** generates `TypeOK` covering every variable and produces `.cfg` with small constants (2-3 processes, 0..3 balances)
4. **Reviewer** flags `state_explosion_risk` as a review category, triggering a rework

## Exemplars

Place well-written `.tla` files in `workspace/exemplars/`. These are loaded as few-shot examples for the formalization agent. Good exemplars demonstrate idiomatic PlusCal, tight TypeOK, bounded ranges, and symmetry usage.

See `workspace/exemplars/README.md` for sourcing suggestions.

## Evaluation Framework

The eval harness measures spec quality across three tiers:

### Tier 1 — Binary pass/fail (automated)

- SANY parses the spec
- PlusCal translates
- TLC runs to completion
- TypeOK holds
- All declared invariants hold

### Tier 2 — Quantitative metrics (automated)

- Distinct states explored (lower = better)
- State graph depth
- TLC wall-clock time
- Number of invariants/properties checked
- Revision count to convergence

### Tier 3 — Mutation detection (the north star)

Known-bug mutant specs have intentional flaws (missing constant-product check, negative balances, free tokens). The eval runs TLC on each mutant with the generated invariants. **Detection rate** — the fraction of mutants caught — is the primary quality metric.

A spec that passes Tier 1 but catches 0/3 mutants has weak invariants. A spec that catches 3/3 mutants actually protects against the bugs it claims to prevent.

### Running evals

```bash
# After pipeline generates specs:
python workspace/evals/run_eval.py ./specs ./workspace/evals/uniswap_swap
```

### Overall score

Weighted: 40% Tier 1 (all pass = 1.0) + 20% Tier 2 (state efficiency vs 100k target) + 40% Tier 3 (mutation detection rate).

### Adding eval cases

```
workspace/evals/
  your_protocol/
    docs/              # Minimal docs for this concern
    checklist.json     # Required/optional invariants + known bugs
    known_bugs/        # Mutant .tla specs with intentional flaws
      bug_name.tla
    expected/          # Optional: reference correct specs
```

`checklist.json` structure:

```json
{
  "name": "Protocol Concern Name",
  "required_invariants": [
    {"name": "TypeOK", "description": "...", "category": "type_safety"},
    {"name": "SafetyProp", "description": "...", "category": "safety"}
  ],
  "known_bugs": [
    {
      "file": "known_bugs/missing_check.tla",
      "description": "What's wrong with this mutant",
      "should_violate": "SafetyProp"
    }
  ],
  "tlc_constraints": {
    "max_states": 200000,
    "max_time_seconds": 120
  }
}
```

## Project Structure

```
├── .gitignore
├── README.md
├── Dockerfile
├── compose.yml
├── requirements.txt
└── workspace/
    ├── pipeline/
    │   ├── state.py          # PipelineState TypedDict
    │   ├── agents.py         # Agent prompts + node functions
    │   ├── main.py           # LangGraph orchestration + CLI
    │   ├── claude_sdk.py     # Claude Agent SDK wrapper (retry, monkey-patches)
    │   └── tlc_tools.py      # SANY, PlusCal, TLC subprocess wrappers
    ├── docs/                 # Input documentation
    ├── exemplars/            # Few-shot .tla reference specs
    └── evals/
        ├── run_eval.py       # Evaluation harness
        └── uniswap_swap/     # Example eval case
            ├── checklist.json
            └── known_bugs/
```
