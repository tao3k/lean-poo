#!/usr/bin/env python3
"""Paired complete-path measurements; preserve every timeout/failure row."""
import argparse
import hashlib
import json
import platform
import subprocess
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--output', required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
binary = root / '.lake/build/bin/cyclicClosureScale'
rows = []
for family, size in [(f, 64) for f in ['chain', 'reverse', 'fanout', 'shared', 'ring', 'quorum']] + [('chain', 256), ('chain', 1024)]:
    for trial in range(3):
        for variant in ['reference', 'worklist', 'retained-index']:
            command = [str(binary), variant, family, str(size)]
            begin = time.monotonic()
            row = dict(family=family, n=size, trial=trial, variant=variant)
            try:
                result = subprocess.run(command, capture_output=True, text=True, timeout=20)
                row.update(status='pass' if result.returncode == 0 else 'failed', exit=result.returncode,
                           stdout=result.stdout.strip(), stderr=result.stderr.strip())
                if result.returncode == 0:
                    row.update({k: int(v) if v.isdigit() else v for k, v in
                                (field.split('=', 1) for field in result.stdout.split())})
            except subprocess.TimeoutExpired as exc:
                row.update(status='timeout', deadline_seconds=20, stdout=(exc.stdout or b'').decode(), stderr=(exc.stderr or b'').decode())
            row['process_wall_seconds'] = time.monotonic()-begin
            rows.append(row)
            print(f'{family}/{size}/{variant}/{trial}: {row["status"]}', flush=True)
            # Save after every run, retaining partial/negative evidence.
            sources = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in
                       [root/'LeanPoo/Functional/IncrementalClosure.lean', root/'LeanPoo/Functional/PositiveEquations.lean', root/'LeanPoo/Prototype/FiniteClosure.lean', root/'Benchmarks/CyclicClosureScale.lean']}
            payload = dict(schema=1, platform=platform.platform(), machine=platform.machine(),
                           lean=subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root, text=True).strip(),
                           binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(), source_sha256=sources,
                           deadline_seconds=20, trials=3, rows=rows)
            Path(args.output).write_text(json.dumps(payload, indent=2)+'\n')
print('Complete; query_ns excludes process startup; retained-index reports setup_ns separately.')
