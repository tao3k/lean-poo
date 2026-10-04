#!/usr/bin/env python3
"""Paired warm serial/parallel checks on identical source-owned Lean atoms."""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FILES = ['Examples/ContextualFactories.lean', 'Examples/SharedFamily.lean',
         'Tests/FunctionalRegistry.lean', 'Tests/FunctionalReindex.lean',
         'Tests/C4Relabeling.lean', 'Tests/ReusableContracts.lean',
         'Tests/FunctionalRequirements.lean', 'Tests/FunctionalObservation.lean']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats', type=int, default=2)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('--repeats must be positive')
    samples = []
    with tempfile.TemporaryDirectory(prefix='lean-poo-check-atoms-') as temporary:
        receipt = Path(temporary) / 'sample.json'
        for repetition in range(args.repeats):
            transcripts = {}
            variants = [1, 4] if repetition % 2 == 0 else [4, 1]
            for jobs in variants:
                print(f'CHECK-ATOMS-STUDY-RUN repeat={repetition} jobs={jobs}', flush=True)
                before = resource.getrusage(resource.RUSAGE_CHILDREN)
                started = time.monotonic()
                subprocess.run([sys.executable, 'tools/check_atoms.py', '--jobs', str(jobs),
                                '--receipt', str(receipt), '--files', *FILES],
                               cwd=ROOT, check=True, timeout=180)
                elapsed = time.monotonic() - started
                after = resource.getrusage(resource.RUSAGE_CHILDREN)
                cpu = after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
                result = json.loads(receipt.read_text())
                assert not result['failures'] and result['selected_files'] == len(FILES)
                transcripts[jobs] = {r['file']: (r['transcript_sha256'], r['source_sha256'], r['returncode'])
                                     for r in result['results']}
                samples.append(dict(repeat=repetition, jobs=jobs, wall_seconds=elapsed,
                                    cpu_seconds=cpu, atoms=result))
                print(json.dumps(dict(repeat=repetition, jobs=jobs, wall_seconds=elapsed,
                                      cpu_seconds=cpu)), flush=True)
            if transcripts[1] != transcripts[4]:
                raise SystemExit('Serial/parallel Lean transcripts or source identity differ')
    medians = {str(jobs): {key: statistics.median(s[key] for s in samples if s['jobs'] == jobs)
                          for key in ['wall_seconds', 'cpu_seconds']} for jobs in [1, 4]}
    source_files = ['tools/check_atoms.py', 'Justfile', 'Benchmarks/CheckAtomsStudy.py', *FILES]
    result = dict(schema='lean-poo.check-atoms-study.v1', files=FILES, repeats=args.repeats,
                  samples=samples, medians=medians, transcript_parity=True,
                  scope='Warm selected eight-file corpus in one prepared Lake environment; excludes initial library build, diagnostics, docs, CI setup and runner queues; not a full-gate or CI speedup estimate',
                  source_sha256={file: hashlib.sha256((ROOT / file).read_bytes()).hexdigest()
                                 for file in source_files})
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('CHECK-ATOMS-STUDY-OK ' + json.dumps(medians), flush=True)


if __name__ == '__main__':
    main()
