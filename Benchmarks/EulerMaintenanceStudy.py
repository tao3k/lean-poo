#!/usr/bin/env python3
"""Inventory a pinned, read-only Euler reference and a checked local client fixture.
This is a lexical source study, not an upstream migration or runtime benchmark.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess

PIN = "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"
ROOT = Path(__file__).resolve().parents[1]
SOURCE = "Euler/PacketInitializedSpatialBudget.lean"
FIELDS = ["background", "background_derivative", "residual_bound", "drift_bound"]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_lines(text):
    # These selected fixtures contain no nested comments or comment delimiters
    # in strings. Count nonblank, noncomment lines in the declared source formatting.
    text = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
    return sum(bool(line.split("--", 1)[0].strip()) for line in text.splitlines())


def section(text, name):
    return text.split(f"-- STUDY-{name}-BEGIN\n", 1)[1].split(
        f"-- STUDY-{name}-END", 1)[0]


def arguments(text):
    # Top-level lexical argument groups, with parenthesized proofs/expressions
    # counted as one. This deliberately does not infer implicit Lean arguments.
    groups, start, depth = [], 0, 0
    for i, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced source call")
        elif char.isspace() and depth == 0:
            if text[start:i].strip():
                groups.append(text[start:i].strip())
            start = i + 1
    if depth:
        raise ValueError("Unbalanced source call")
    if text[start:].strip():
        groups.append(text[start:].strip())
    return groups


def followup(reference, common, calls):
    access = ROOT / "LeanPoo/Functional/Access.lean"
    fixture = ROOT / "Tests/FunctionalAccess.lean"
    assembly = ROOT / "LeanPoo/Functional/Assembly.lean"
    text = fixture.read_text()
    positional = text.split("-- ACCESS-POSITIONAL-BEGIN\n", 1)[1].split("-- ACCESS-POSITIONAL-END", 1)[0]
    named = text.split("-- ACCESS-NAMED-BEGIN\n", 1)[1].split("-- ACCESS-NAMED-END", 1)[0]
    expressions = re.findall(r":= (retained[.0-9]+)", positional)
    if expressions != ["retained.2.1", "retained.2.2.1"]:
        raise ValueError("Unexpected positional comparison fixture")
    theorem_path = reference / "Euler/PacketInitializedCorrectionNorms.lean"
    theorem_source = theorem_path.read_text()
    declarations = theorem_source.split("variable ", 1)[1].split("\ninclude ", 1)[0]
    groups = arguments(declarations)
    declared = []
    for group in groups:
        if group.startswith(("(", "{")) and ":" in group:
            declared.extend(group[1:].split(":", 1)[0].split())
    if not set(common) <= set(declared):
        raise ValueError("Common parameters missing from source variable declarations")
    ambient = re.findall(r"\[([^\]]+)\]", declarations)
    for call in calls:
        if not re.search(r"^theorem " + re.escape(call["callee"]) + r"\b", theorem_source, re.M):
            raise ValueError("Expected proof-valued source entry")
    helper = "def fromProof" + assembly.read_text().split("def fromProof", 1)[1].split("/-- Adapt a factory", 1)[0]
    return {
        "access_fixture": {"file": "Tests/FunctionalAccess.lean", "sha256": sha256(fixture),
                           "positional_read_before": expressions[0], "positional_read_after": expressions[1],
                           "positional_consumer_expression_edits": 1, "named_consumer_expression_edits": 0,
                           "positional_read_definition_code_lines": code_lines(positional.split("private def positionalAfter", 1)[0]),
                           "generic_named_read_definition_code_lines": code_lines(named),
                           "scope": "one residual access while inserting derivative; checklist/provider changes excluded"},
        "additional_shared_cost": {"access_file": "LeanPoo/Functional/Access.lean", "sha256": sha256(access),
                                   "access_code_lines_including_proofs": code_lines(access.read_text()),
                                   "proof_adapter_and_equation_code_lines": code_lines(helper),
                                   "proof_adapter_source_sha256": sha256(assembly)},
        "context_adapter_ledger": {"theorem_file": "Euler/PacketInitializedCorrectionNorms.lean", "sha256": sha256(theorem_path),
                                   "one_to_one_common_context_field_slots": len(common),
                                   "ambient_typeclass_declarations": ambient,
                                   "implicit_period_and_instance_closure": "not elaborated; full dependent context remains unverified",
                                   "proof_valued_source_entries": len(calls),
                                   "adapter_entries_if_each_original_theorem_is_retained": len(calls),
                                   "explicit_argument_groups_retained_by_adapters": sum(c["explicit_argument_groups"] for c in calls),
                                   "nonprefix_argument_groups": sum(c["explicit_argument_groups"] for c in calls) - len(common) * len(calls),
                                   "scope": "conditional one-to-one context model, not a compiled Euler context/adapter implementation"}
    }


def study(reference):
    actual = subprocess.check_output(
        ["git", "-C", str(reference), "rev-parse", "HEAD"], text=True).strip()
    if actual != PIN:
        raise ValueError(f"Expected reference pin {PIN}, got {actual}")
    if subprocess.check_output(
            ["git", "-C", str(reference), "status", "--porcelain=v1"], text=True):
        raise ValueError("Reference checkout must be clean")
    path = reference / SOURCE
    source = path.read_text()
    calls, args = [], []
    for field in FIELDS:
        match = re.search(r"^  " + field + r" t := (.*?)(?=\n  [^ \n]|\n\n)",
                          source, re.M | re.S)
        if match is None:
            raise ValueError(f"Missing source field {field}")
        groups = arguments(match[1])
        first = source.count("\n", 0, match.start()) + 1
        calls.append({"field": field, "callee": groups[0], "first_line": first,
                      "last_line": first + len(match[1].splitlines()) - 1,
                      "explicit_argument_groups": len(groups) - 1})
        args.append(groups[1:])
    common = []
    for column in zip(*args):
        if len(set(column)) != 1:
            break
        common.append(column[0])
    fixture_path = ROOT / "Tests/FunctionalMaintenance.lean"
    fixture = fixture_path.read_text()
    manual = section(fixture, "MANUAL")
    checklist = section(fixture, "CHECKLIST")
    before, after = code_lines(manual), code_lines(checklist)
    library = ROOT / "LeanPoo/Functional/Requirements.lean"
    overhead = code_lines(library.read_text())
    savings = before - after
    return {
        "schema": "lean-poo.euler-maintenance.v2",
        "evidence_boundary": "pinned lexical inventory plus kernel-checked generic client comparison; no upstream integration",
        "reference": {"repository": "openai/NavierStokesAndEuler", "commit": actual,
                      "file": SOURCE, "sha256": sha256(path), "calls": calls,
                      "common_explicit_prefix": common,
                      "common_arguments_per_call": len(common),
                      "common_argument_occurrences": len(common) * len(calls),
                      "duplicate_occurrences_beyond_first_call": len(common) * (len(calls) - 1)},
        "local_client": {"file": "Tests/FunctionalMaintenance.lean", "sha256": sha256(fixture_path),
                         "semantic_contract": "same_client",
                         "manual_code_lines": before, "checklist_code_lines": after,
                         "common_interface_code_lines": code_lines(section(fixture, "COMMON")),
                         "saved_client_code_lines": savings,
                         "client_code_reduction_percent": round(100 * savings / before, 2),
                         "manual_require_statements": manual.count("← require provider"),
                         "checklist_prepare_calls": checklist.count("Requirements.prepare provider"),
                         "manual_owned_prepared_fields": 5, "checklist_owned_prepared_fields": 0,
                         "new_checklist_declaration_included": True},
        "shared_cost": {"file": "LeanPoo/Functional/Requirements.lean", "sha256": sha256(library),
                        "code_lines_including_kernel_proofs": overhead,
                        "toy_source_break_even_consumers": math.ceil(overhead / savings),
                        "scope": "count entire Requirements module once; Assembly/provider/context/domain code and reference adapters excluded"},
        "forecast": {"upstream_net_lines_removed": None, "maintenance_hours_saved": None,
                     "consumer_common_context_slots_if_adapted": len(calls),
                     "adapter_common_arguments_still_required": len(common) * len(calls),
                     "scope": "hypothetical consumer surface only; adapters preserve existing upstream signatures; no net-source or labor claim"},
        "followup": followup(reference, common, calls),
        "validation": "Run lake env lean Tests/FunctionalMaintenance.lean and Tests/FunctionalAccess.lean separately; this script does not certify Lean proofs."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT / ".data/NavierStokesAndEuler")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipt = study(args.reference)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"common_arguments_per_call": receipt["reference"]["common_arguments_per_call"],
                      "source_calls": len(receipt["reference"]["calls"]),
                      "local_client": receipt["local_client"], "shared_cost": receipt["shared_cost"]},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
