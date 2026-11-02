"""Org reader integration controls, explicitly required by just check-docs.

Core supervision discovery has no document-tool dependency. All reader controls
run in the docs job, where the official parser is installed, rather than causing
duplicate downloads in the library job. No controls are skipped.
"""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.check_docs import org_documents, parse_documents


class OrgReaderTests(unittest.TestCase):
    def test_scope_keeps_all_indexes_and_recursive_documents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'docs/nested').mkdir(parents=True)
            (root / 'docs/root.org').touch()
            (root / 'docs/nested/child.org').touch()
            (root / 'docs/nested/ignored.md').touch()
            self.assertEqual([str(path.relative_to(root)) for path in org_documents(root)],
                ['README.org', 'Examples/README.org', 'Tests/README.org',
                 'Benchmarks/README.org', 'docs/nested/child.org', 'docs/root.org'])
            self.assertNotEqual(parse_documents([root / 'missing.org']), 0)

    def test_missing_document_directory_is_not_an_empty_success(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                org_documents(Path(directory))

    def test_reader_parses_body_structure_without_executing_source(self):
        with tempfile.TemporaryDirectory() as directory:
            page = Path(directory) / 'fixture.org'
            page.write_text("""#+TITLE: Parser fixture
* Header
:PROPERTIES:
:ID: reader-fixture
:END:
A [[https://example.com][link]].
- first
- second

| key | value |
|-----+-------|
| a   | 1     |

#+begin_src python
raise RuntimeError('source must never execute')
#+end_src
""")
            result = subprocess.run(['pandoc', '--sandbox', '--from=org', '--to=json',
                                     '--file-scope', str(page)], capture_output=True,
                                    text=True, check=True, timeout=5)
            document = json.loads(result.stdout)
            blocks = [block['t'] for block in document['blocks']]
            for tag in ('Header', 'Para', 'BulletList', 'Table', 'CodeBlock'):
                self.assertIn(tag, blocks)
            self.assertIn('Link', result.stdout)
            self.assertEqual(parse_documents([page]), 0)


if __name__ == '__main__':
    unittest.main()
