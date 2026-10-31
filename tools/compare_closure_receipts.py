#!/usr/bin/env python3
"""Independent executable parity evidence; not a Scheme translation proof."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--lean', type=Path, required=True)
parser.add_argument('--scheme', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
lean = json.loads(args.lean.read_text())
scheme = json.loads(args.scheme.read_text())
assert len(lean['rows']) == 96 and len(scheme['rows']) == 144
assert all(row['status'] == 'pass' for row in lean['rows']+scheme['rows'])
assert all(row['peak_frames'] <= row['n'] for row in scheme['rows'])
fields = ['pops','evals','nodes','writes','pushes','edges','queue_pairs']
def key(row):
    return (row['family'], row['n'], row['width'], str(row['seed']).replace('#t','true').replace('#f','false'), row['trial'], row['queue'])
peers = {key(row): row for row in scheme['rows'] if row['state'] == 'owned'}
assert len(peers) == 96
for row in lean['rows']:
    peer = peers[key(row)]
    for field in fields:
        assert row[field] == peer[field], (key(row), field, row[field], peer[field])
args.output.write_text(json.dumps(dict(schema=1, scheme_peak_bound_checks=144, observations=96, fields=fields, assertions=96*len(fields),
    lean_receipt_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
    scheme_receipt_sha256=hashlib.sha256(args.scheme.read_bytes()).hexdigest(),
    scheme_source_sha256=scheme['source_sha256'], status='pass',
    boundary='Finite executable controls; no formal Scheme translation or compiler correctness claim.'),indent=2)+'\n')
print('CLOSURE-CROSS-COUNTS-OK observations=96 assertions=672')
