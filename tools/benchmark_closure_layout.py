#!/usr/bin/env python3
"""Bounded independent trials; compare variants only within one runtime."""
import argparse
import hashlib
import json
import platform
import subprocess
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--kind', choices=['lean', 'scheme'], default='scheme')
parser.add_argument('--binary', required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
binary = Path(args.binary).resolve()
rows = []
version_command = (['lake','env','lean','--version'] if args.kind == 'lean' else
                   ['gxi','-e','(displayln (list (gerbil-version-string) (system-version-string)))'])
toolchain = subprocess.check_output(version_command,cwd=root,text=True).strip()
if args.kind == 'lean':
    source_names = ['LeanPoo/Functional/IncrementalClosure.lean', 'LeanPoo/Functional/ChunkedClosure.lean',
                    'LeanPoo/Functional/ClosureCosts.lean', 'LeanPoo/Functional/ClosureScenarios.lean',
                    'Benchmarks/ClosureLayoutScale.lean', str(Path(__file__).relative_to(root))]
else:
    source_names = ['closure.ss', 't/closure-scale-benchmark.ss', str(Path(__file__).relative_to(root))]
source_hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in source_names}
variants = [('append', 'owned'), ('chunked', 'owned')]
if args.kind == 'scheme':
    variants.insert(0, ('append', 'copied'))
cases = [('diamond', 256, 16), ('diamond', 1024, 16), ('dense', 64, 16), ('dense', 256, 16),
         ('ring', 1024, 16), ('skewed', 128, 64), ('gated', 1024, 16), ('quorum', 256, 16)]
for family, size, width in cases:
    for seed in ['true', 'false']:
        for trial in range(3):
            for queue, state in variants:
                command = ([str(binary), queue, family, str(size), str(width), seed] if args.kind == 'lean'
                           else [str(binary), '-:max-heap=1G', queue, state, family, str(size), str(width), seed, '5'])
                row = dict(family=family, n=size, width=width, seed=seed, trial=trial, queue=queue, state=state)
                started = time.monotonic()
                try:
                    completed = subprocess.run(command, capture_output=True, text=True, timeout=20)
                    row.update(status='pass' if completed.returncode == 0 else 'failed', exit=completed.returncode,
                               stdout=completed.stdout.strip(), stderr=completed.stderr.strip())
                    if completed.returncode == 0:
                        for key, value in (part.split('=', 1) for part in completed.stdout.split()):
                            row[key] = int(value) if value.isdigit() else value
                        if row.get('oracle_parity') != 'true':
                            row['status'] = 'failed_oracle_receipt'
                except subprocess.TimeoutExpired as exc:
                    row.update(status='timeout', deadline_seconds=20,
                               stdout=(exc.stdout or b'').decode(), stderr=(exc.stderr or b'').decode())
                row['process_wall_seconds'] = time.monotonic()-started
                rows.append(row)
                payload = dict(schema=1, runtime=args.kind, toolchain=toolchain, platform=platform.platform(), machine=platform.machine(),
                               binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(), source_sha256=source_hashes,
                               source_base=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
                               deadline_seconds=20, trials=3, rows=rows)
                Path(args.output).write_text(json.dumps(payload, indent=2)+'\n')
            print(f'{family}/{size}/{seed}/{trial}: '+','.join(r['status'] for r in rows[-len(variants):]), flush=True)
if any(row['status'] != 'pass' for row in rows):
    raise SystemExit('Nonpassing rows retained in receipt')
print(f'LAYOUT-BENCHMARK-OK rows={len(rows)}')
