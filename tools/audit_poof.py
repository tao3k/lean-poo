#!/usr/bin/env python3
"""Bind manually reviewed paper coverage to exact local source identities.

Generation requires the original local paper. CI checks the saved identity and
local evidence files without downloading or integrating reference repositories.
Neither mode infers semantic completeness from filenames, hashes or markers.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / 'docs/audits/poof/requirements-v1.json'
RECEIPT = ROOT / 'docs/audits/poof/receipt-v1.json'
STATUSES = {'lean_translation', 'partial', 'not_implemented', 'discussion', 'future_proposal'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def config_rows():
    config = json.loads(CONFIG.read_text())
    if config['schema'] != 'lean-poo.poof-requirements.v1':
        raise ValueError('Expected requirements v1')
    rows = config['rows']
    starts = [row['start_line'] for row in rows]
    if not rows or starts[0] != 1 or starts != sorted(set(starts)):
        raise ValueError('Review intervals must start at 1 and strictly increase')
    if len({row['id'] for row in rows}) != len(rows):
        raise ValueError('Duplicate review unit')
    for row in rows:
        if row['status'] not in STATUSES or not row['boundary']:
            raise ValueError('Unknown status or missing scope boundary')
        if row['status'] == 'lean_translation' and not (row['implementation'] and row['checks']):
            raise ValueError('Translated construction needs implementation and control references')
        for name in row['implementation'] + row['checks']:
            path = ROOT / name
            if not path.is_file() or not path.resolve().is_relative_to(ROOT):
                raise ValueError(f'Missing or nonlocal evidence: {name}')
    return config


def evidence(config):
    names = sorted({name for row in config['rows'] for name in row['implementation'] + row['checks']})
    result = {}
    for name in names:
        path = ROOT / name
        lines = path.read_text().splitlines()
        result[name] = {
            'sha256': sha(path), 'physical_lines': len(lines),
            'unsafe_declaration_lines': [i for i, line in enumerate(lines, 1)
                                         if re.match(r'^unsafe (def|abbrev)', line)],
            'guard_lines': [i for i, line in enumerate(lines, 1) if line.startswith('#guard ')],
            'eval_lines': [i for i, line in enumerate(lines, 1) if line.startswith('#eval ')],
        }
    return result


def outline_sha(headings):
    return hashlib.sha256(json.dumps(headings, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_inventory():
    return sorted(str(path.relative_to(ROOT)) for top in ['LeanPoo', 'Tests', 'Examples']
                  for path in (ROOT / top).rglob('*.lean'))


def assign_headings(config, headings, line_count):
    rows = config['rows']
    if rows[-1]['start_line'] > line_count:
        raise ValueError('Review extends past paper')
    assigned = []
    for heading in headings:
        eligible = [row for row in rows if row['start_line'] <= heading['line']]
        row = eligible[-1]
        assigned.append(dict(heading, review_unit=row['id'], status=row['status']))
    if len({heading['line'] for heading in assigned}) != len(assigned):
        raise ValueError('Duplicate heading identity')
    return assigned


def generate(paper):
    config = config_rows()
    if sha(paper) != config['paper_sha256']:
        raise ValueError('Paper changed: review before updating the pin')
    commit = subprocess.check_output(['git', '-C', str(paper.parent), 'rev-parse', 'HEAD'], text=True).strip()
    if commit != config['paper_commit']:
        raise ValueError('Unexpected paper checkout commit')
    lines = paper.read_text().splitlines()
    headings = [{'line': i, 'source': line} for i, line in enumerate(lines, 1)
                if re.match(r'^@(section|subsection|subsubsection)\b', line)]
    if not headings:
        raise ValueError('No paper headings')
    if outline_sha(headings) != config['outline_sha256']:
        raise ValueError('Unexpected reviewed outline')
    return {
        'schema': 'lean-poo.poof-audit.v1',
        'baseline_commit': config['baseline_commit'],
        'paper': {'repository': 'metareflection/poof', 'file': 'poof.scrbl',
                  'commit': commit, 'sha256': sha(paper), 'physical_lines': len(lines)},
        'requirements_sha256': sha(CONFIG), 'audit_tool_sha256': sha(Path(__file__)),
        'review_units': config['rows'], 'headings': assign_headings(config, headings, len(lines)),
        'unit_status_counts': dict(sorted(Counter(row['status'] for row in config['rows']).items())),
        'local_evidence': evidence(config), 'source_file_inventory': source_inventory(),
        'whole_paper_implemented': False,
        'limits': ['Statuses are manually reviewed, not inferred semantic proofs',
                   'Heading coverage means all outline entries are assigned, not all behaviors reproduced',
                   'Guard/eval lines are lexical markers, not execution receipts; printed values need expected-value assertions',
                   'Original Scheme/Racket evaluation and cross-language differential checks not performed',
                   'Local translation, formal correspondence, unsafe execution and paper proposals remain distinct',
                   'C4, proof reuse and OpenAI reference audits do not substitute for missing paper cases'],
    }


def check():
    config = config_rows()
    receipt = json.loads(RECEIPT.read_text())
    if receipt['schema'] != 'lean-poo.poof-audit.v1' or receipt['whole_paper_implemented'] is not False:
        raise ValueError('Unexpected receipt schema or completeness claim')
    if receipt['requirements_sha256'] != sha(CONFIG) or receipt['audit_tool_sha256'] != sha(Path(__file__)):
        raise ValueError('Audit instructions changed: regenerate after review')
    if receipt['review_units'] != config['rows'] or receipt['local_evidence'] != evidence(config):
        raise ValueError('Local source or reviewed scope changed: re-audit before regenerating')
    if receipt['baseline_commit'] != config['baseline_commit'] or receipt['source_file_inventory'] != source_inventory():
        raise ValueError('Baseline or source inventory changed: re-audit coverage')
    for name in ['commit', 'sha256']:
        if receipt['paper'][name] != config['paper_' + name]:
            raise ValueError('Saved paper identity differs from reviewed pin')
    headings = [{'line': h['line'], 'source': h['source']} for h in receipt['headings']]
    if outline_sha(headings) != config['outline_sha256']:
        raise ValueError('Saved outline differs from the reviewed paper')
    if receipt['headings'] != assign_headings(config, headings, receipt['paper']['physical_lines']):
        raise ValueError('Heading coverage changed')
    counts = dict(sorted(Counter(row['status'] for row in config['rows']).items()))
    if receipt['unit_status_counts'] != counts:
        raise ValueError('Status counts changed')
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper', type=Path)
    parser.add_argument('--output', type=Path, default=RECEIPT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        result = check()
    else:
        if not args.paper:
            parser.error('Generation requires --paper pointing to the reviewed local poof.scrbl')
        result = generate(args.paper)
        args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print('POOF-AUDIT-OK ' + json.dumps({'review_units': len(result['review_units']),
          'headings': len(result['headings']), 'local_files': len(result['local_evidence']),
          'whole_paper_implemented': False, 'mode': 'saved-local-check' if args.check else 'original-paper-generation'}))


if __name__ == '__main__':
    main()
