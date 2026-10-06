#!/usr/bin/env python3
"""Matched native retained-result-index study, retaining setup and collision costs."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/resultIndexScale'
SOURCES = sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'LeanPoo').rglob('*.lean')) + [
    'Benchmarks/ResultIndexScale.lean', 'Benchmarks/ResultIndexStudy.py', 'LeanPoo.lean',
    'lakefile.toml', 'lean-toolchain', 'Justfile', 'tools/check_gate.py', '.github/workflows/ci.yml']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not BINARY.is_file():
        raise SystemExit('Build resultIndexScale first')
    samples, medians = [], {}
    for keys in [8, 64]:
        for reads in [1, 4096]:
            for mode in ['head', 'tail', 'cycle']:
                for hashing in ['uniform', 'collision']:
                    groups = {'list': [], 'indexed': []}
                    for pair in range(4):
                        controls = []
                        variants = ['list', 'indexed'] if pair % 2 == 0 else ['indexed', 'list']
                        for variant in variants:
                            result = subprocess.run([str(BINARY), variant, mode, hashing, str(keys), str(reads), '17'],
                                                    cwd=ROOT, capture_output=True, text=True, timeout=10, check=True)
                            row = dict(part.split('=', 1) for part in result.stdout.strip().split())
                            for field in ['keys', 'reads', 'seed', 'checksum', 'setup_ns', 'query_ns']:
                                row[field] = int(row[field])
                            assert (row['variant'], row['mode'], row['hashing'], row['oracle_parity']) == (variant, mode, hashing, 'true')
                            assert (row['keys'], row['reads'], row['seed']) == (keys, reads, 17)
                            expected = sum(18 + (0 if mode == 'head' else keys-1 if mode == 'tail' else i % keys)
                                           for i in range(reads)) % (2**64)
                            assert row['checksum'] == expected
                            controls.append({k: v for k, v in row.items() if k not in ['variant', 'setup_ns', 'query_ns']})
                            row['total_ns'] = row['setup_ns'] + row['query_ns']
                            groups[variant].append(row)
                            samples.append(dict(pair=pair, **row))
                            print(f'RESULT-INDEX-STUDY keys={keys} reads={reads} mode={mode} hashing={hashing} '
                                  f'pair={pair} variant={variant} query_ns={row["query_ns"]}', flush=True)
                        assert controls[0] == controls[1], 'Matched controls differ'
                    medians[f'{keys}/{reads}/{mode}/{hashing}'] = {
                        variant: {field: statistics.median(row[field] for row in rows)
                                  for field in ['setup_ns', 'query_ns', 'total_ns']}
                        for variant, rows in groups.items()}
    receipt = {
        'schema': 'lean-poo.result-index-study.v1', 'engine': 'native', 'alternating_pairs': 4,
        'host': {'system': platform.system(), 'machine': platform.machine()},
        'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
        'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest(),
        'samples': samples, 'medians': medians, 'matched_controls': True,
        'scope': 'Both variants build identical immutable UInt64 data from runtime seed and keys. Indexed additionally '
                 'builds a dependent hash table. Both materialize data/table Option in the same IO-cell shape before query '
                 'timing. Setup/query separately recorded. Query includes identical schedule, IO checksum loop and '
                 'noinline named lookup; independent Nat oracle runs after timing and Python independently checks checksum.',
        'limits': ['Four alternating local pairs, no confidence interval, universal speedup or crossover estimate',
                   'Synthetic immutable Nat-key UInt64 values; not Euler analysis or heterogeneous application performance',
                   'Uniform uses key-as-hash; collision uses zero hash for every key; both same lawful key equality',
                   'One-query/head/collision controls retained; index setup/storage costs remain',
                   'Total is setup plus query, excluding process startup, IO checksum-cell creation and post-timing oracle',
                   'Named value lookup only; projected tuple construction, observers and dependency caches not measured',
                   'No allocated-byte/peak-memory, external net code or maintenance-hours gain measured']}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print('RESULT-INDEX-STUDY-OK samples=' + str(len(samples)), flush=True)


if __name__ == '__main__':
    main()
