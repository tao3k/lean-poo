#!/usr/bin/env python3
"""Parse every maintained Org file with Pandoc, without installing an editor.

Pandoc supplies the full Org reader; this module only enumerates the existing
scope and delegates to it. Parsing is not Org execution, link-target validation,
or an assertion of an identical Emacs AST. The independent paper audit stays in
just check-docs. JSON is discarded, not saved as a generated repository artifact.
"""
from pathlib import Path
import subprocess
import sys

try:
    from .process_guard import collect
except ImportError:
    from process_guard import collect

ROOT = Path(__file__).resolve().parents[1]


def org_documents(root):
    """Retain the four indexes and every recursive docs/*.org input exactly."""
    if not (root / 'docs').is_dir():
        raise FileNotFoundError(root / 'docs')
    return [root / name for name in ('README.org', 'Examples/README.org',
            'Tests/README.org', 'Benchmarks/README.org')] + sorted((root / 'docs').rglob('*.org'))


def parse_documents(paths, command='pandoc', seconds=90):
    """Use independent file scopes and the existing bounded process-group guard."""
    command = [command, '--sandbox', '--from=org', '--to=json', '--file-scope',
               '--output=/dev/null', *map(str, paths)]
    process = subprocess.Popen(command, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True)
    code, _ = collect(process, lambda line: sys.stdout.buffer.write(line), seconds)
    return code


def main():
    """Require all maintained inputs and propagate every reader failure/timeout."""
    paths = org_documents(ROOT)
    print(f'ORG-PARSE files={len(paths)} reader=pandoc', flush=True)
    code = parse_documents(paths)
    if code == 0:
        print(f'ORG-OK files={len(paths)}', flush=True)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
