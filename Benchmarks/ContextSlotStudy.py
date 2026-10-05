#!/usr/bin/env python3
"""Matched native built-data cache study, including cheap and all-miss controls."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/contextSlotScale'
SOURCES = sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'LeanPoo').rglob('*.lean')) + [
    'Benchmarks/ContextSlotScale.lean', 'Benchmarks/ContextSlotStudy.py', 'LeanPoo.lean',
    'lakefile.toml', 'lean-toolchain', 'Justfile', 'tools/check_gate.py', '.github/workflows/ci.yml']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not BINARY.is_file():
        raise SystemExit('Build contextSlotScale first')
    samples, medians = [], {}
    for keys in [8, 32]:
        for work in [0, 1024]:
            for mode in ['hit', 'miss', 'blocks']:
                groups = {'uncached': [], 'cached': []}
                for pair in range(4):
                    controls = []
                    variants = ['uncached', 'cached'] if pair % 2 == 0 else ['cached', 'uncached']
                    for variant in variants:
                        result = subprocess.run([str(BINARY), variant, mode, str(work), str(keys), '256'],
                                                cwd=ROOT, capture_output=True, text=True, timeout=30, check=True)
                        row = dict(part.split('=', 1) for part in result.stdout.strip().split())
                        for field in ['work', 'keys', 'reads', 'checksum', 'expected_hits', 'reused', 'setup_ns', 'query_ns']:
                            row[field] = int(row[field])
                        assert row['variant'] == variant and row['mode'] == mode and row['oracle_parity'] == 'true'
                        assert (row['work'], row['keys'], row['reads']) == (work, keys, 256)
                        expected_hits = {'hit': 256, 'miss': 0, 'blocks': 224}[mode]
                        assert row['expected_hits'] == expected_hits
                        assert row['reused'] == (expected_hits if variant == 'cached' else 0)
                        controls.append({k: v for k, v in row.items()
                                         if k not in ['variant', 'reused', 'setup_ns', 'query_ns']})
                        row['total_ns'] = row['setup_ns'] + row['query_ns']
                        groups[variant].append(row)
                        samples.append(dict(pair=pair, **row))
                        print(f'CONTEXT-STUDY keys={keys} work={work} mode={mode} pair={pair} '
                              f'{variant} query_ns={row["query_ns"]}', flush=True)
                    assert controls[0] == controls[1], 'Matched outcomes differ'
                medians[f'{keys}/{work}/{mode}'] = {
                    variant: {field: statistics.median(row[field] for row in rows)
                              for field in ['setup_ns', 'query_ns', 'total_ns']}
                    for variant, rows in groups.items()}
    receipt = {
        'schema': 'lean-poo.context-slot-study.v1', 'engine': 'native', 'alternating_pairs': 4,
        'host': {'system': platform.system(), 'machine': platform.machine()},
        'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
        'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest(),
        'samples': samples, 'medians': medians, 'matched_controls': True,
        'scope': 'Both variants prepare identical certified factories and materialize the same warm context=7 '
                 'snapshot in an IO cell before query timing. Setup is recorded separately. Query includes '
                 'the same IO state loop, result construction, checksumming and uncached dependency builds '
                 'or cache read/build/replacement. Independent scalar recurrence and policy oracle run after timing.',
        'limits': ['Four local pairs per workload; no universal speedup or crossover',
                   'Claim=True isolates native data-cache overhead; kernel tests cover dependent joint Claims',
                   'Synthetic UInt64 recurrence includes factory loop allocation; not Euler analytical computation',
                   'Cached path also compares context and tracks hits; negative/cheap workloads retained',
                   'Total is common warm setup plus query, not process startup or a cold one-use comparison',
                   'Output constructor still executes each request; observation/project/reindex not benchmarked',
                   'No allocated-byte/peak-memory, external code reduction or maintenance savings measured']}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(medians))


if __name__ == '__main__':
    main()
