#!/usr/bin/env python3
"""Read-only source census and lexical call-site inventory, not an impact proof."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"
DEFINITION = "Euler/PacketInitializedCorrectionNorms.lean"
NAMES = ["initializedCorrection_background", "initializedCorrection_background_derivative",
         "initializedCorrection_drift", "initializedCorrection_residual"]
CANDIDATES = ["SourceCoefficientAgreement", "initializedCorrectionData", "velocityMap"]


def git(reference, *args):
    return subprocess.check_output(["git", "-C", str(reference), *args])


def observation_bridge(reference):
    relative = "Euler/PacketInitializedResidualEquation.lean"
    raw = (reference / relative).read_bytes()
    text = raw.decode()
    names = ["toFieldTower_eq_of_path_eq", "initializedNormalizedField_path_eq",
             "initializedNormalizedField_tower_eq", "initializedCorrectionData_eq_coordinate"]
    declarations = {}
    for name in names:
        rows = [i for i, row in enumerate(text.splitlines(), 1)
                if re.match(r"theorem " + re.escape(name) + r"\b", row)]
        if len(rows) != 1:
            raise ValueError(f"Expected one declaration of {name}")
        declarations[name] = rows[0]
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(),
            "declarations": declarations,
            "scope": "Existing source bridge: path equality implies field-tower equality; correction-data equality is used by the residual identity",
            "external_lean_compilation": False,
            "proposed_contract": "Different representation families, fixed context/key/public observation family, pointwise observation equality on declared consumer keys",
            "euler_adapter_implemented": False}


def study(reference):
    if git(reference, "rev-parse", "HEAD").decode().strip() != PIN:
        raise ValueError("Reference pin mismatch")
    if git(reference, "status", "--porcelain=v1"):
        raise ValueError("Reference must remain clean")
    files = sorted(p for p in git(reference, "ls-files", "-z").decode().split("\0")
                   if p.endswith(".lean"))
    lines, groups, digest = 0, Counter(), hashlib.sha256()
    mentions = {name: [] for name in NAMES}
    candidates = {name: {"files": 0, "occurrences": 0, "sample": []} for name in CANDIDATES}
    for relative in files:
        raw = (reference / relative).read_bytes()
        digest.update(relative.encode() + b"\0" + hashlib.sha256(raw).digest())
        text = raw.decode()
        rows = text.splitlines()
        lines += len(rows)
        groups[relative.split("/", 1)[0]] += 1
        for name, item in candidates.items():
            count = len(re.findall(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text))
            if count:
                item["files"] += 1
                item["occurrences"] += count
                if len(item["sample"]) < 3:
                    item["sample"].append({"file": relative, "occurrences": count})
        if relative == DEFINITION:
            continue
        for name in NAMES:
            pattern = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
            matches = [i for i, row in enumerate(rows, 1) if pattern.search(row)]
            if matches:
                mentions[name].append({"file": relative, "lines": matches})
    local = ["LeanPoo/Functional/View.lean", "Tests/FunctionalView.lean",
             "LeanPoo/Functional/Observation.lean", "Tests/FunctionalObservation.lean"]
    return {
        "schema": "lean-poo.euler-change-surface.v2",
        "reference": {"repository": "openai/NavierStokesAndEuler", "commit": PIN,
                      "tracked_lean_files": len(files), "physical_lines": lines,
                      "files_by_top_level": dict(sorted(groups.items())),
                      "source_manifest_sha256": digest.hexdigest(),
                      "scope": "Git-tracked .lean files only; dependencies/generated/untracked files excluded"},
        "lexical_mentions": mentions,
        "candidate_interfaces": candidates,
        "candidate_limit": "All identifier-text occurrences, including defining files/comments; prioritization only, not evidence of interchangeable providers or C4 benefit",
        "mention_limit": "Identifier-text rows outside defining file, including possible comments; not elaborated references, dependency closure, or affected-file count",
        "observation_bridge": observation_bridge(reference),
        "local_contract": {"files": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in local},
                           "scope": "Exact factory agreement for View; pointwise public observation equality for Observation, allowing different representation types; both source preparations successful; fixed Context/Key/public observation types",
                           "runtime_benchmark": False},
        "unmeasured": {"actual_euler_consumers_migrated": 0, "net_lines_saved": None,
                       "maintenance_hours_saved": None, "affected_euler_consumers_avoided": None},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT / ".data/NavierStokesAndEuler")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = study(args.reference)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"files": result["reference"]["tracked_lean_files"],
                      "lines": result["reference"]["physical_lines"],
                      "lexical_sites": {k: sum(len(p["lines"]) for p in v)
                                        for k, v in result["lexical_mentions"].items()}}))


if __name__ == "__main__":
    main()
