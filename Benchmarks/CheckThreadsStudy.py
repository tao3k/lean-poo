#!/usr/bin/env python3
"""Matched full atom inventory: fixed file concurrency, Lean default/one thread."""
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=12)
    parser.add_argument('--repeats', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1 or args.repeats < 1:
        parser.error('jobs/repeats must be positive')
    samples = []
    with tempfile.TemporaryDirectory(prefix='lean-poo-check-threads-') as temporary:
        path = Path(temporary) / 'atoms.json'
        for repeat in range(args.repeats):
            controls = {}
            for threads in ([None, 1] if repeat % 2 == 0 else [1, None]):
                label = 'default' if threads is None else 'one'
                print(f'CHECK-THREADS-RUN repeat={repeat} variant={label} jobs={args.jobs}', flush=True)
                command = [sys.executable, 'tools/check_atoms.py', '--jobs', str(args.jobs), '--receipt', str(path)]
                if threads is not None:
                    command += ['--lean-threads', str(threads)]
                before = resource.getrusage(resource.RUSAGE_CHILDREN)
                start = time.monotonic()
                subprocess.run(command, cwd=ROOT, check=True, timeout=180)
                after = resource.getrusage(resource.RUSAGE_CHILDREN)
                receipt = json.loads(path.read_text())
                assert not receipt['failures']
                assert receipt['selected_files'] == receipt['inventory_files']
                controls[label] = {r['file']: (r['source_sha256'], r['transcript_sha256'], r['returncode'])
                                   for r in receipt['results']}
                samples.append(dict(repeat=repeat, variant=label, wall_seconds=time.monotonic()-start,
                                    cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                                    atoms=receipt))
            assert controls['default'] == controls['one'], 'Source/transcript/status parity changed'
    medians = {label: {field: statistics.median(s[field] for s in samples if s['variant'] == label)
                       for field in ['wall_seconds', 'cpu_seconds']} for label in ['default', 'one']}
    files = ['tools/check_atoms.py', 'Justfile', 'Benchmarks/CheckThreadsStudy.py']
    files += [r['file'] for r in samples[0]['atoms']['results']]
    result = dict(schema='lean-poo.check-threads-study.v1', jobs=args.jobs, repeats=args.repeats,
                  samples=samples, medians=medians, transcript_parity=True,
                  source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files},
                  scope='Full canonical warm atom inventory, alternating internal-thread variants at fixed file-worker count; '
                        'excludes library preparation, diagnostics, docs, native checks and CI setup/queues',
                  limits=['Two alternating pairs are local measurements, not a confidence interval or full-gate speedup',
                          'Default Lean internal thread count is not measured; one explicitly requests -j 1',
                          'All timeout/memory/allocation arguments retained; no skipped file or cached test acceptance'])
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('CHECK-THREADS-STUDY-OK '+json.dumps(medians), flush=True)


if __name__ == '__main__':
    main()
