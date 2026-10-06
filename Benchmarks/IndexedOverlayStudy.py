#!/usr/bin/env python3
"""Alternating list/indexed retained overlay workloads, internal runtime timers."""
import argparse
import hashlib
import json
from pathlib import Path
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ["LeanPoo/Functional/IndexedOverlay.lean", "LeanPoo/Functional/Overlay.lean",
           "Benchmarks/IndexedOverlayScale.lean", "Benchmarks/IndexedOverlayStudy.py"]
CASES = [("small", 8, 8), ("distinct", 1024, 1024), ("repeated", 2048, 256)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    samples = []
    for case, count, width in CASES:
        for repetition in range(4):
            pair = []
            for variant in (["list", "indexed"] if repetition % 2 == 0 else ["indexed", "list"]):
                print(f"INDEXED-OVERLAY-RUN case={case} repeat={repetition} variant={variant}", flush=True)
                result = subprocess.run(["lake", "env", "lean", "--run", "Benchmarks/IndexedOverlayScale.lean",
                                         variant, str(count), str(width)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=60, check=True)
                cells = dict(cell.split("=", 1) for cell in result.stdout.strip().split())
                sample = {k: (v if k in ["variant", "oracle_parity"] else int(v)) for k, v in cells.items()}
                assert sample["oracle_parity"] == "true"
                assert sample["count"] == count and sample["width"] == width
                sample.update(case=case, repeat=repetition)
                pair.append(sample)
                samples.append(sample)
                print(json.dumps(sample), flush=True)
            assert all(pair[0][key] == pair[1][key] for key in
                       ["count", "width", "queries", "stored", "checksum", "oracle_parity"])
    medians = {}
    for case, _, _ in CASES:
        medians[case] = {variant: {key: statistics.median(s[key] for s in samples
                                  if s["case"] == case and s["variant"] == variant)
                                  for key in ["construct_ns", "query_ns"]}
                         for variant in ["list", "indexed"]}
    args.output.write_text(json.dumps(dict(schema="lean-poo.indexed-overlay-study.v1",
        engine="Lean --run interpreter; internal monotonic construction/query timers",
        repeats=4, alternating_order=True, samples=samples, medians=medians,
        matched_semantic_controls=True,
        scope="Local selected Nat-key workloads; excludes imports, input construction, independent scalar oracle, graph/registry/preparation and end-to-end Euler proofs; no native-code or allocation claim",
        source_sha256={p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}), indent=2)+"\n")
    print("INDEXED-OVERLAY-STUDY-OK " + json.dumps(medians), flush=True)


if __name__ == "__main__":
    main()
