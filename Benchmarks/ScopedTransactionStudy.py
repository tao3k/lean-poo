#!/usr/bin/env python3
"""Paired native full/scoped consumer preparation; no application-speed claim."""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/scopedTransactionScale'
SOURCES = ['LeanPoo/Functional/ScopedTransaction.lean', 'LeanPoo/Functional/TransactionCheck.lean',
           'LeanPoo/Functional/IndexedTransaction.lean', 'LeanPoo/Functional/IndexedRegistry.lean',
           'LeanPoo/Functional/RegistryTransaction.lean', 'LeanPoo/Functional/RegistryBatch.lean',
           'LeanPoo/Functional/IndexedOverlay.lean', 'LeanPoo/Functional/Requirements.lean',
           'LeanPoo/Functional/Assembly.lean', 'Benchmarks/ScopedTransactionScale.lean',
           'Benchmarks/ScopedTransactionStudy.py', 'lakefile.toml', 'lean-toolchain']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not BINARY.is_file():
        raise SystemExit('Build scopedTransactionScale before the study')
    samples = []
    medians = {}
    for mode in ['outside', 'keys', 'positive', 'unknown']:
        groups = {'full': [], 'scoped': []}
        for pair in range(4):
            controls = []
            for variant in (['full', 'scoped'] if pair % 2 == 0 else ['scoped', 'full']):
                result = subprocess.run([str(BINARY), variant, mode, '4096', '32', '16'],
                                        cwd=ROOT, capture_output=True, text=True, timeout=30, check=True)
                row = dict(part.split('=', 1) for part in result.stdout.strip().split())
                for key in ['count', 'width', 'chunk', 'batches', 'checksum', 'elapsed_ns']:
                    row[key] = int(row[key])
                assert row['variant'] == variant and row['mode'] == mode and row['oracle_parity'] == 'true'
                assert (row['count'], row['width'], row['chunk']) == (4096, 32, 16)
                controls.append({k: v for k, v in row.items() if k not in ['variant', 'elapsed_ns']})
                groups[variant].append(row['elapsed_ns'])
                samples.append(dict(pair=pair, **row))
                print(f'SCOPED-STUDY {mode} pair={pair} variant={variant} elapsed_ns={row["elapsed_ns"]}', flush=True)
            assert controls[0] == controls[1], 'Matched outcome controls differ'
        medians[mode] = {variant: statistics.median(times) for variant, times in groups.items()}
    receipt = {'schema': 'lean-poo.scoped-transaction-study.v1', 'engine': 'native', 'alternating_pairs': 4,
               'host': {'system': platform.system(), 'machine': platform.machine()},
               'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES},
               'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest(),
               'samples': samples, 'median_elapsed_ns': medians, 'matched_controls': True,
               'scope': 'Single consumer preparation including impact scan and relevant branch; graph/index/registration/conversion/inputs/imports/build/factory execution/oracle excluded',
               'limits': ['Four local alternating pairs, not a universal crossover', 'Positive branch incurs impact scan before full update',
                          'Consumer-only view; no updated registry returned', 'No allocated-byte/peak-memory/whole Euler/maintenance saving measurement']}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(medians))


if __name__ == '__main__':
    main()
