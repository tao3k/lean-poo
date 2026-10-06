#!/usr/bin/env python3
"""Alternating list/indexed retained registry workloads, internal runtime timers."""
import argparse
import hashlib
import json
from pathlib import Path
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ["LeanPoo/Functional/IndexedRegistry.lean", "LeanPoo/Functional/Overlay.lean", "LeanPoo/Functional/IndexedOverlay.lean", "LeanPoo/Functional/RegistryBatch.lean",
           "Benchmarks/IndexedRegistryScale.lean", "Benchmarks/IndexedRegistryStudy.py", "lakefile.toml", "lean-toolchain"]
CASES = [("small", 8, 8, 8), ("distinct", 4096, 1024, 64), ("repeated", 4096, 256, 16)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--engine", choices=["interpreter", "native"], default="interpreter")
    parser.add_argument("--policy", choices=["latest", "retained"], default="latest")
    args = parser.parse_args()
    native = ROOT / ".lake/build/bin/indexedRegistryScale"
    if args.engine == "native" and not native.is_file():
        parser.error("Build the executable first: lake build indexedRegistryScale")
    launch = [str(native)] if args.engine == "native" else ["lake", "env", "lean", "--run", "Benchmarks/IndexedRegistryScale.lean"]
    samples = []
    for case, count, width, chunk in CASES:
        for repetition in range(4):
            pair = []
            for variant in (["list", "indexed"] if repetition % 2 == 0 else ["indexed", "list"]):
                print(f"INDEXED-REGISTRY-RUN case={case} repeat={repetition} variant={variant}", flush=True)
                result = subprocess.run([*launch, variant, str(count), str(width), str(chunk), args.policy], cwd=ROOT,
                                        text=True, capture_output=True, timeout=60, check=True)
                cells = dict(cell.split("=", 1) for cell in result.stdout.strip().split())
                sample = {k: (v if k in ["variant", "policy", "oracle_parity"] else int(v)) for k, v in cells.items()}
                assert sample["oracle_parity"] == "true"
                assert sample["count"] == count and sample["width"] == width and sample["policy"] == args.policy
                sample.update(case=case, repeat=repetition)
                pair.append(sample)
                samples.append(sample)
                print(json.dumps(sample), flush=True)
            assert all(pair[0][key] == pair[1][key] for key in
                       ["count", "width", "chunk", "batches", "queries", "checksum", "retained", "saved_checksum", "policy", "oracle_parity"])
    medians = {}
    for case, _, _, _ in CASES:
        medians[case] = {variant: {key: statistics.median(s[key] for s in samples
                                  if s["case"] == case and s["variant"] == variant)
                                  for key in ["construct_ns", "query_ns"]}
                         for variant in ["list", "indexed"]}
    args.output.write_text(json.dumps(dict(schema="lean-poo.indexed-registry-study.v1",
        engine=args.engine, retention_policy=args.policy,
        native_binary_sha256=hashlib.sha256(native.read_bytes()).hexdigest() if args.engine == "native" else None,
        timers="Internal monotonic construction/query timers; runtime startup excluded",
        repeats=4, alternating_order=True, samples=samples, medians=medians,
        matched_semantic_controls=True,
        scope="Local selected Nat-key workloads; excludes imports, input construction, independent scalar oracle, initial name registration, graph/order/preparation and end-to-end Euler proofs; retained policy includes keeping every intermediate snapshot alive across timed updates and queries; no allocation-byte or universal speedup claim",
        source_sha256={p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}), indent=2)+"\n")
    print("INDEXED-REGISTRY-STUDY-OK " + json.dumps(medians), flush=True)


if __name__ == "__main__":
    main()
