"""Fail closed when source identity or cross-language evidence is incomplete."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from tools import poof_source_check as source


class SourceCheckTests(unittest.TestCase):
    def test_reader_respects_comments_strings_and_nested_delimiters(self):
        text = '@;@Checks[(ignored)]\n@Definitions[(define x "[;]") #| [ #| ] |# ] |#\n (list [1 2])]'
        extracted = list(source.blocks(text))
        self.assertEqual(len(extracted), 1)
        self.assertEqual(extracted[0][:2], ('Definitions', 2))
        with self.assertRaisesRegex(ValueError, 'Unclosed'):
            list(source.blocks('@Checks[(unfinished)'))

    def test_corrupted_and_missing_fixture_blocks_are_rejected(self):
        saved = json.loads(source.SOURCE_CODE.read_text())
        source.source_code()
        for change, reason in [('code', 'code hash'), ('count', 'block count')]:
            damaged = copy.deepcopy(saved)
            if change == 'code':
                damaged['blocks'][0]['code'] += '\n'
            else:
                damaged['blocks'].pop()
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'fixture.json'
                path.write_text(json.dumps(damaged))
                with self.assertRaisesRegex(ValueError, reason):
                    source.source_code(fixture=path)

    def test_mismatch_omission_and_duplicate_are_rejected(self):
        mapped = [{'source_line': 1}, {'source_line': 2}]
        actual = [{'line': 1, 'kind': 'value', 'canonical': [1]},
                  {'line': 2, 'kind': 'value', 'canonical': {'symbol': 'a'}}]
        rows = [{'line': entry['line'], 'canonical': entry['canonical']} for entry in actual]
        source.compare_checks(actual, rows, mapped)
        mismatch = copy.deepcopy(rows)
        mismatch[1]['canonical'] = {'symbol': 'b'}
        with self.assertRaisesRegex(ValueError, 'mismatch at paper line 2'):
            source.compare_checks(actual, mismatch, mapped)
        for incomplete in [rows[:-1], [rows[0], rows[0]]]:
            with self.assertRaisesRegex(ValueError, 'each of the 24 checks once'):
                source.compare_checks(actual, incomplete, mapped)
        with self.assertRaisesRegex(ValueError, 'Source differential receipt'):
            source.compare_checks([actual[0], actual[0]], rows, mapped)


if __name__ == '__main__':
    unittest.main()
