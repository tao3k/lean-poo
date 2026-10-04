#!/usr/bin/env python3
"""Compare warm check orchestration; preserve the same Lean files and targets."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
TARGETS = ["LeanPoo.C4.Merge", "LeanPoo.C4.Precedence", "LeanPoo.C4.Suffix",
           "LeanPoo.C4.GraphCertificate", "LeanPoo.C4.VerifiedOrder", "LeanPoo.C4.Renaming"]
FILES = ["Tests/ReusableContracts.lean", "Tests/C4Renaming.lean"]


def run(command, env=None):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    elapsed = time.monotonic() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
    if result.returncode:
        print(result.stdout, result.stderr, flush=True)
        raise SystemExit(result.returncode)
    return elapsed, cpu, result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    # Preparation is common to both variants and reported separately. Warm-cache
    # measurements start only after all selected targets have built successfully.
    print("CHECK-STARTUP-PREPARE", flush=True)
    run(["lake", "build", *TARGETS])
    wall, cpu, lean_path = run(["lake", "env", "printenv", "LEAN_PATH"])
    bin_wall, bin_cpu, lean_bin = run(["lake", "env", "which", "lean"])
    env = os.environ.copy()
    env["LEAN_PATH"] = lean_path.strip()
    samples = []
    for repetition in range(args.repeats):
        for case in ["cached-builds", "lean-checks"]:
            outputs = {}
            variants = ["baseline", "shared"] if repetition % 2 == 0 else ["shared", "baseline"]
            for variant in variants:
                if case == "cached-builds":
                    commands = [["lake", "build", target] for target in TARGETS] if variant == "baseline" else [["lake", "build", *TARGETS]]
                else:
                    commands = [["lake", "env", "lean", file] for file in FILES] if variant == "baseline" else [[lean_bin.strip(), file] for file in FILES]
                total_wall = total_cpu = 0.0
                output = []
                for command in commands:
                    print(f"CHECK-STARTUP-RUN repeat={repetition} case={case} variant={variant} target={command[-1]}", flush=True)
                    elapsed, used_cpu, transcript = run(command, env if variant == "shared" and case == "lean-checks" else None)
                    total_wall += elapsed
                    total_cpu += used_cpu
                    output.append(transcript)
                outputs[variant] = output
                sample = dict(repeat=repetition, case=case, variant=variant,
                              wall_seconds=total_wall, cpu_seconds=total_cpu)
                samples.append(sample)
                print(json.dumps(sample), flush=True)
            if case == "lean-checks" and outputs["baseline"] != outputs["shared"]:
                raise SystemExit("Lean check transcripts differ")
    medians = {}
    for case in ["cached-builds", "lean-checks"]:
        medians[case] = {}
        for variant in ["baseline", "shared"]:
            selected = [s for s in samples if s["case"] == case and s["variant"] == variant]
            medians[case][variant] = {key: statistics.median(s[key] for s in selected)
                                     for key in ["wall_seconds", "cpu_seconds"]}
    receipt = dict(targets=TARGETS, files=FILES, repeats=args.repeats,
                   shared_environment_preparation=dict(wall_seconds=wall + bin_wall, cpu_seconds=cpu + bin_cpu),
                   samples=samples, medians=medians,
                   source_sha256={file: hashlib.sha256((ROOT / file).read_bytes()).hexdigest() for file in FILES})
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print("CHECK-STARTUP-OK " + json.dumps(medians), flush=True)


if __name__ == "__main__":
    main()
