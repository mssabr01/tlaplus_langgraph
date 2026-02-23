#!/usr/bin/env python3
"""Evaluation harness for TLA+ specification pipeline.

Measures spec quality across three tiers:
  1. Binary pass/fail (syntax, translation, model-checkability)
  2. Quantitative metrics (state count, depth, invariant coverage)
  3. Mutation detection (does the spec catch known bugs?)

Usage:
    python evals/run_eval.py <spec_dir> <eval_case_dir>

    spec_dir:       Directory containing pipeline output (Spec.tla, Spec.cfg, etc.)
    eval_case_dir:  Directory containing the eval case (checklist.json, known_bugs/, etc.)

Example:
    python evals/run_eval.py ./specs ./evals/uniswap_swap
"""

import json
import os
import re
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path

# Add pipeline to path so we can import tlc_tools
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "pipeline"))

from tlc_tools import parse_spec, translate_pluscal, run_tlc


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class TierOneResults:
    """Binary pass/fail checks."""
    sany_parses: bool = False
    pluscal_translates: bool = False  # N/A if no PlusCal
    tlc_runs: bool = False
    type_ok_holds: bool = False
    all_invariants_hold: bool = False
    errors: list[str] = field(default_factory=list)

    @property
    def all_pass(self) -> bool:
        return (self.sany_parses and self.tlc_runs
                and self.type_ok_holds and self.all_invariants_hold)


@dataclass
class TierTwoResults:
    """Quantitative metrics."""
    distinct_states: int | None = None
    states_generated: int | None = None
    depth: int | None = None
    tlc_time_seconds: float | None = None
    invariant_count: int = 0
    property_count: int = 0
    invariants_checked: list[str] = field(default_factory=list)
    properties_checked: list[str] = field(default_factory=list)
    revision_count: int | None = None  # From pipeline history if available


@dataclass
class MutantResult:
    """Result of running TLC on a single mutant spec."""
    mutant_file: str = ""
    expected_violation: str = ""
    actual_violation: str | None = None
    detected: bool = False
    error: str | None = None


@dataclass
class TierThreeResults:
    """Mutation detection results."""
    mutants_tested: int = 0
    mutants_detected: int = 0
    detection_rate: float = 0.0
    checklist_coverage: float = 0.0
    required_invariants_present: list[str] = field(default_factory=list)
    required_invariants_missing: list[str] = field(default_factory=list)
    mutant_results: list[MutantResult] = field(default_factory=list)


@dataclass
class EvalReport:
    """Complete evaluation report."""
    eval_case: str = ""
    spec_dir: str = ""
    timestamp: str = ""
    tier1: TierOneResults = field(default_factory=TierOneResults)
    tier2: TierTwoResults = field(default_factory=TierTwoResults)
    tier3: TierThreeResults = field(default_factory=TierThreeResults)

    @property
    def overall_score(self) -> float:
        """Weighted score: 40% tier1, 20% tier2 (state efficiency), 40% tier3."""
        t1 = 1.0 if self.tier1.all_pass else 0.0
        # State efficiency: 1.0 if under target, scaling down above
        t2 = 0.0
        if self.tier2.distinct_states is not None and self.tier2.distinct_states > 0:
            target = 100_000
            t2 = min(1.0, target / self.tier2.distinct_states)
        t3 = self.tier3.detection_rate if self.tier3.mutants_tested > 0 else 0.0
        return 0.4 * t1 + 0.2 * t2 + 0.4 * t3


# ---------------------------------------------------------------------------
# TLC output parsing (mirrors agents.py but standalone)
# ---------------------------------------------------------------------------

def parse_tlc_output(raw: str) -> dict:
    result = {
        "success": "Model checking completed" in raw,
        "states_found": None,
        "distinct_states": None,
        "depth": None,
        "violated_invariant": None,
    }

    m = re.search(r"(\d+) states generated, (\d+) distinct states found", raw)
    if m:
        result["states_found"] = int(m.group(1))
        result["distinct_states"] = int(m.group(2))

    m = re.search(r"The depth of the complete state graph search is (\d+)", raw)
    if m:
        result["depth"] = int(m.group(1))

    m = re.search(r"Invariant (\w+) is violated", raw)
    if m:
        result["violated_invariant"] = m.group(1)
        result["success"] = False

    return result


# ---------------------------------------------------------------------------
# Tier 1: Binary checks
# ---------------------------------------------------------------------------

def run_tier1(spec_path: str, cfg_path: str) -> TierOneResults:
    """Run binary pass/fail checks."""
    results = TierOneResults()

    with open(spec_path) as f:
        spec = f.read()

    # SANY parse
    success, output = parse_spec(spec)
    results.sany_parses = success
    if not success:
        results.errors.append(f"SANY: {output[:200]}")
        return results

    # PlusCal translation (if applicable)
    if "algorithm" in spec.lower():
        success, output = translate_pluscal(spec)
        results.pluscal_translates = success
        if not success:
            results.errors.append(f"PlusCal: {output[:200]}")
            return results
        spec = output  # Use translated version

    # TLC run
    if not os.path.exists(cfg_path):
        results.errors.append("No .cfg file found")
        return results

    with open(cfg_path) as f:
        cfg = f.read()

    start = time.time()
    success, raw_output = run_tlc(spec, cfg)
    elapsed = time.time() - start

    parsed = parse_tlc_output(raw_output)
    results.tlc_runs = parsed["success"]

    if not parsed["success"]:
        violated = parsed.get("violated_invariant")
        if violated:
            results.errors.append(f"Invariant {violated} violated")
            if violated == "TypeOK":
                results.type_ok_holds = False
            results.all_invariants_hold = False
        else:
            results.errors.append(f"TLC error: {raw_output[:300]}")
    else:
        results.type_ok_holds = True
        results.all_invariants_hold = True

    return results


# ---------------------------------------------------------------------------
# Tier 2: Quantitative metrics
# ---------------------------------------------------------------------------

def run_tier2(spec_path: str, cfg_path: str) -> TierTwoResults:
    """Collect quantitative metrics from TLC."""
    results = TierTwoResults()

    with open(spec_path) as f:
        spec = f.read()

    if "algorithm" in spec.lower():
        success, output = translate_pluscal(spec)
        if success:
            spec = output

    if not os.path.exists(cfg_path):
        return results

    with open(cfg_path) as f:
        cfg = f.read()

    # Extract invariant/property names from cfg
    for line in cfg.splitlines():
        line = line.strip()
        if line.startswith("INVARIANT"):
            name = line.split(None, 1)[1].strip() if len(line.split()) > 1 else ""
            if name:
                results.invariants_checked.append(name)
        elif line.startswith("PROPERTY"):
            name = line.split(None, 1)[1].strip() if len(line.split()) > 1 else ""
            if name:
                results.properties_checked.append(name)

    results.invariant_count = len(results.invariants_checked)
    results.property_count = len(results.properties_checked)

    # Run TLC and collect stats
    start = time.time()
    success, raw_output = run_tlc(spec, cfg)
    elapsed = time.time() - start

    results.tlc_time_seconds = round(elapsed, 2)

    parsed = parse_tlc_output(raw_output)
    results.distinct_states = parsed.get("distinct_states")
    results.states_generated = parsed.get("states_found")
    results.depth = parsed.get("depth")

    # Check for pipeline revision history
    spec_dir = os.path.dirname(spec_path)
    history_dir = os.path.join(spec_dir, "history")
    if os.path.isdir(history_dir):
        results.revision_count = len(os.listdir(history_dir))

    return results


# ---------------------------------------------------------------------------
# Tier 3: Mutation detection + checklist coverage
# ---------------------------------------------------------------------------

def run_tier3(
    spec_path: str,
    cfg_path: str,
    checklist: dict,
    known_bugs_dir: str,
) -> TierThreeResults:
    """Run mutation detection and check property coverage."""
    results = TierThreeResults()

    # --- Checklist coverage ---
    with open(spec_path) as f:
        spec_text = f.read()

    if os.path.exists(cfg_path):
        with open(cfg_path) as f:
            cfg_text = f.read()
    else:
        cfg_text = ""

    combined = spec_text + "\n" + cfg_text

    required = checklist.get("required_invariants", [])
    for inv in required:
        name = inv["name"]
        # Check if invariant is defined in spec OR referenced in cfg
        if re.search(rf"\b{name}\b", combined):
            results.required_invariants_present.append(name)
        else:
            results.required_invariants_missing.append(name)

    total_required = len(required)
    if total_required > 0:
        results.checklist_coverage = len(results.required_invariants_present) / total_required

    # --- Mutation detection ---
    known_bugs = checklist.get("known_bugs", [])
    if not known_bugs or not os.path.isdir(known_bugs_dir):
        return results

    for bug in known_bugs:
        mutant_file = os.path.join(
            os.path.dirname(known_bugs_dir.rstrip("/")),
            bug["file"],
        )
        if not os.path.exists(mutant_file):
            results.mutant_results.append(MutantResult(
                mutant_file=bug["file"],
                expected_violation=bug["should_violate"],
                error=f"File not found: {mutant_file}",
            ))
            continue

        with open(mutant_file) as f:
            mutant_spec = f.read()

        # Build a cfg that checks the expected invariant
        mutant_cfg = f"SPECIFICATION Spec\nINVARIANT {bug['should_violate']}\n"

        # Add constants from the checklist constraints or main cfg
        constraints = checklist.get("tlc_constraints", {})
        mutant_cfg += f"CONSTANT MaxBalance = {constraints.get('max_states', 3)}\n"

        # If there's a cfg in the known_bugs dir, use that instead
        mutant_cfg_path = os.path.join(known_bugs_dir, "Spec.cfg")
        if os.path.exists(mutant_cfg_path):
            with open(mutant_cfg_path) as f:
                base_cfg = f.read()
            # Ensure the target invariant is checked
            if bug["should_violate"] not in base_cfg:
                base_cfg += f"\nINVARIANT {bug['should_violate']}\n"
            mutant_cfg = base_cfg

        success, raw_output = run_tlc(mutant_spec, mutant_cfg)
        parsed = parse_tlc_output(raw_output)

        mr = MutantResult(
            mutant_file=bug["file"],
            expected_violation=bug["should_violate"],
        )

        if parsed.get("violated_invariant"):
            mr.actual_violation = parsed["violated_invariant"]
            mr.detected = True
        elif not parsed["success"]:
            # TLC failed for other reasons — might still count
            mr.error = raw_output[:200]
            mr.detected = False
        else:
            # TLC passed — mutant was NOT detected (bad)
            mr.detected = False

        results.mutant_results.append(mr)

    results.mutants_tested = len(results.mutant_results)
    results.mutants_detected = sum(1 for m in results.mutant_results if m.detected)
    if results.mutants_tested > 0:
        results.detection_rate = results.mutants_detected / results.mutants_tested

    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run_eval(spec_dir: str, eval_case_dir: str) -> EvalReport:
    """Run full evaluation."""
    report = EvalReport(
        eval_case=os.path.basename(eval_case_dir),
        spec_dir=spec_dir,
        timestamp=time.strftime("%Y-%m-%d %H:%M:%S"),
    )

    spec_path = os.path.join(spec_dir, "Spec.tla")
    cfg_path = os.path.join(spec_dir, "Spec.cfg")
    checklist_path = os.path.join(eval_case_dir, "checklist.json")
    known_bugs_dir = os.path.join(eval_case_dir, "known_bugs")

    if not os.path.exists(spec_path):
        print(f"ERROR: {spec_path} not found")
        return report

    # Load checklist
    checklist = {}
    if os.path.exists(checklist_path):
        with open(checklist_path) as f:
            checklist = json.load(f)

    # Run tiers
    print("=== Tier 1: Binary Pass/Fail ===")
    report.tier1 = run_tier1(spec_path, cfg_path)
    print(f"  SANY parses:         {report.tier1.sany_parses}")
    print(f"  PlusCal translates:  {report.tier1.pluscal_translates}")
    print(f"  TLC runs:            {report.tier1.tlc_runs}")
    print(f"  TypeOK holds:        {report.tier1.type_ok_holds}")
    print(f"  All invariants hold: {report.tier1.all_invariants_hold}")
    if report.tier1.errors:
        for e in report.tier1.errors:
            print(f"  ERROR: {e}")

    print("\n=== Tier 2: Quantitative Metrics ===")
    report.tier2 = run_tier2(spec_path, cfg_path)
    print(f"  Distinct states:  {report.tier2.distinct_states}")
    print(f"  States generated: {report.tier2.states_generated}")
    print(f"  Depth:            {report.tier2.depth}")
    print(f"  TLC time (s):     {report.tier2.tlc_time_seconds}")
    print(f"  Invariants:       {report.tier2.invariant_count} {report.tier2.invariants_checked}")
    print(f"  Properties:       {report.tier2.property_count} {report.tier2.properties_checked}")

    print("\n=== Tier 3: Mutation Detection ===")
    report.tier3 = run_tier3(spec_path, cfg_path, checklist, known_bugs_dir)
    print(f"  Checklist coverage:  {report.tier3.checklist_coverage:.0%}")
    print(f"  Present:  {report.tier3.required_invariants_present}")
    print(f"  Missing:  {report.tier3.required_invariants_missing}")
    print(f"  Mutants tested:   {report.tier3.mutants_tested}")
    print(f"  Mutants detected: {report.tier3.mutants_detected}")
    print(f"  Detection rate:   {report.tier3.detection_rate:.0%}")
    for mr in report.tier3.mutant_results:
        status = "CAUGHT" if mr.detected else "MISSED"
        print(f"    [{status}] {mr.mutant_file}: expected={mr.expected_violation}, "
              f"actual={mr.actual_violation or 'none'}")

    print(f"\n=== Overall Score: {report.overall_score:.2f} ===")

    # Write report
    report_path = os.path.join(spec_dir, "eval_report.json")
    with open(report_path, "w") as f:
        json.dump(asdict(report), f, indent=2)
    print(f"\nReport saved to {report_path}")

    return report


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python run_eval.py <spec_dir> <eval_case_dir>")
        print("  spec_dir:      Directory with Spec.tla and Spec.cfg (pipeline output)")
        print("  eval_case_dir: Directory with checklist.json and known_bugs/")
        sys.exit(1)

    run_eval(sys.argv[1], sys.argv[2])
