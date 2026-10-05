#!/usr/bin/env python3
"""Paired native retained-key-index study, with construction cost recorded."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/keyIndexScale'
SOURCES = ['LeanPoo/Functional/KeyIndex.lean', 'LeanPoo/Functional/ScopedTransaction.lean',
           'LeanPoo/Functional/TransactionCheck.lean', 'LeanPoo/Functional/IndexedTransaction.lean',
           'LeanPoo/Functional/IndexedRegistry.lean', 'LeanPoo/Functional/RegistryTransaction.lean',
           'LeanPoo/Functional/RegistryBatch.lean', 'LeanPoo/Functional/IndexedOverlay.lean',
           'LeanPoo/Functional/Requirements.lean', 'LeanPoo/Functional/Assembly.lean',
           'Benchmarks/KeyIndexScale.lean', 'Benchmarks/KeyIndexStudy.py', 'lakefile.toml', 'lean-toolchain']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not BINARY.is_file():
        raise SystemExit('Build keyIndexScale before this study')
    samples, medians = [], {}
    for requests in [8, 512]:
        for mode in ['outside', 'keys', 'early', 'late', 'unknown']:
            groups = {'list': [], 'indexed': []}
            for pair in range(4):
                controls = []
                for variant in (['list', 'indexed'] if pair % 2 == 0 else ['indexed', 'list']):
                    result = subprocess.run([str(BINARY), variant, mode, '4096', str(requests), '16'],
                                            cwd=ROOT, capture_output=True, text=True, timeout=30, check=True)
                    row = dict(part.split('=', 1) for part in result.stdout.strip().split())
                    for key in ['count', 'requests', 'chunk', 'batches', 'checksum', 'compile_ns', 'query_ns']:
                        row[key] = int(row[key])
                    assert row['variant'] == variant and row['mode'] == mode and row['oracle_parity'] == 'true'
                    assert (row['count'], row['requests'], row['chunk']) == (4096, requests, 16)
                    controls.append({k: v for k, v in row.items() if k not in ['variant', 'compile_ns', 'query_ns']})
                    row['total_ns'] = row['compile_ns'] + row['query_ns']
                    groups[variant].append(row)
                    samples.append(dict(pair=pair, **row))
                    print(f'KEY-STUDY requests={requests} {mode} pair={pair} {variant} query_ns={row["query_ns"]}', flush=True)
                assert controls[0] == controls[1], 'Matched scalar outcomes differ'
            medians[f'{requests}/{mode}'] = {
                variant: {key: statistics.median(row[key] for row in rows)
                          for key in ['compile_ns', 'query_ns', 'total_ns']} for variant, rows in groups.items()}
    receipt = {'schema': 'lean-poo.key-index-study.v1', 'engine': 'native', 'alternating_pairs': 4,
               'host': {'system': platform.system(), 'machine': platform.machine()},
               'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
               'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest(),
               'samples': samples, 'medians': medians, 'matched_controls': True,
               'scope': 'Index construction recorded separately; query includes complete consumer preparation/impact/preflight/fallback. Graph/ancestry/registration/conversion/inputs/factory bodies/oracle/build excluded',
               'limits': ['Four local pairs per workload; no universal crossover', 'Outside/early scopes can amortize no key-index benefit',
                          'Total is per-sample compile+query, not process latency', 'Raw edit histories still scanned; collisions/copies remain',
                          'No allocated-byte/peak-memory/whole Euler/maintenance savings measured']}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(medians))


if __name__ == '__main__':
    main()
