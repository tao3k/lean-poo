"""Reject drift that could silently weaken a saved paper audit."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import audit_poof


class PoofAuditTests(unittest.TestCase):
    def setUp(self):
        self.receipt = json.loads(audit_poof.RECEIPT.read_text())

    def check_bad_receipt(self, receipt, reason):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'receipt.json'
            path.write_text(json.dumps(receipt))
            with patch.object(audit_poof, 'RECEIPT', path):
                with self.assertRaisesRegex(ValueError, reason):
                    audit_poof.check()

    def test_removed_outline_entry_is_rejected(self):
        audit_poof.check()
        changed = copy.deepcopy(self.receipt)
        changed['headings'].pop()
        self.check_bad_receipt(changed, 'Saved outline differs')

    def test_changed_local_evidence_is_rejected(self):
        changed = copy.deepcopy(self.receipt)
        name = next(iter(changed['local_evidence']))
        changed['local_evidence'][name]['sha256'] = '0' * 64
        self.check_bad_receipt(changed, 'Local source or reviewed scope changed')

    def test_removed_source_check_is_rejected(self):
        mapping = copy.deepcopy(self.receipt['source_checks'])
        mapping['paper_checks'].pop()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'checks.json'
            path.write_text(json.dumps(mapping))
            with patch.object(audit_poof, 'CHECKS', path):
                with self.assertRaisesRegex(ValueError, 'Source check coverage changed'):
                    audit_poof.check()

    def test_removed_closure_requirement_is_rejected(self):
        closure = copy.deepcopy(self.receipt['construction_closure'])
        closure['requirements'].pop()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'closure.json'
            path.write_text(json.dumps(closure))
            with patch.object(audit_poof, 'CLOSURE', path):
                with self.assertRaisesRegex(ValueError, 'Construction closure coverage changed'):
                    audit_poof.check()

    def test_unreviewed_original_paper_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            paper = Path(directory) / 'poof.scrbl'
            paper.write_text('@section{Unreviewed replacement}\n')
            with self.assertRaisesRegex(ValueError, 'Paper changed'):
                audit_poof.generate(paper)


if __name__ == '__main__':
    unittest.main()
