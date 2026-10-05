#!/usr/bin/env python3
"""Paired native cached-preparation study, with common initial setup recorded."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/cachedPreparationScale'
SOURCES = ['LeanPoo/Functional/CachedPreparation.lean', 'LeanPoo/Functional/CertifiedRequirements.lean',
           'LeanPoo/Functional/KeyIndex.lean', 'LeanPoo/Functional/ScopedTransaction.lean',
           'LeanPoo/Functional/TransactionCheck.lean', 'LeanPoo/Functional/IndexedTransaction.lean',
           'LeanPoo/Functional/IndexedRegistry.lean', 'LeanPoo/Functional/RegistryTransaction.lean',
           'LeanPoo/Functional/RegistryBatch.lean', 'LeanPoo/Functional/IndexedOverlay.lean',
           'LeanPoo/Functional/Requirements.lean', 'LeanPoo/Functional/Assembly.lean',
           'Benchmarks/CachedPreparationScale.lean', 'Benchmarks/CachedPreparationStudy.py', 'lakefile.toml', 'lean-toolchain']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not BINARY.is_file():
        raise SystemExit('Build cachedPreparationScale before this study')
    samples, medians = [], {}
    for requests in [8, 512]:
        for mode in ['outside', 'keys', 'early', 'late', 'unknown']:
            groups = {'indexed': [], 'cached': []}
            for pair in range(4):
                controls = []
                for variant in (['indexed', 'cached'] if pair % 2 == 0 else ['cached', 'indexed']):
                    result = subprocess.run([str(BINARY), variant, mode, '4096', str(requests), '16'],
                                            cwd=ROOT, capture_output=True, text=True, timeout=30, check=True)
                    row = dict(part.split('=', 1) for part in result.stdout.strip().split())
                    for key in ['count', 'requests', 'chunk', 'batches', 'checksum', 'setup_ns', 'query_ns']:
                        row[key] = int(row[key])
                    assert row['variant'] == variant and row['mode'] == mode and row['oracle_parity'] == 'true'
                    assert (row['count'], row['requests'], row['chunk']) == (4096, requests, 16)
                    controls.append({k: v for k, v in row.items() if k not in ['variant', 'setup_ns', 'query_ns']})
                    row['total_ns'] = row['setup_ns'] + row['query_ns']
                    groups[variant].append(row)
                    samples.append(dict(pair=pair, **row))
                    print(f'CACHE-STUDY requests={requests} {mode} pair={pair} {variant} query_ns={row["query_ns"]}', flush=True)
                assert controls[0] == controls[1], 'Matched scalar outcomes differ'
            medians[f'{requests}/{mode}'] = {
                variant: {key: statistics.median(row[key] for row in rows)
                          for key in ['setup_ns', 'query_ns', 'total_ns']} for variant, rows in groups.items()}
    receipt = {'schema': 'lean-poo.cached-preparation-study.v1', 'engine': 'native', 'alternating_pairs': 4,
               'host': {'system': platform.system(), 'machine': platform.machine()},
               'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
               'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest(),
               'samples': samples, 'medians': medians, 'matched_controls': True,
               'scope': 'Both variants materialize the same certified tuple/key index in an IO cell before query timing; common setup including cell creation/read recorded separately. Query compares re-preparation versus cached reuse, including impact/preflight/fallback/forget. Graph/ancestry/registration/conversion/inputs/factory bodies/oracle/build excluded',
               'limits': ['Four local pairs per workload; no universal crossover', 'Positive overlap follows full preparation; prior joint proof is not reused',
                          'Total is common setup+query, not one-use comparison or process latency', 'Raw edit histories still scanned; collisions/copies remain',
                          'Native Claim=True isolates cache/preparation overhead; kernel proofs cover arbitrary joint Claims', 'No allocated-byte/peak-memory/whole Euler/maintenance savings measured']}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(medians))


if __name__ == '__main__':
    main()
