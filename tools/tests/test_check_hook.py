"""Hook progress must neither hide failures nor alter the checked command."""
import io
from pathlib import Path
import sys
import unittest

from tools.check_hook import progress_line, run_check, saved_check


class CheckHookTests(unittest.TestCase):
    def test_captured_command_keeps_diagnostics_and_failure(self):
        output, terminal = io.StringIO(), io.StringIO()
        command = [sys.executable, '-c',
                   'print("CHECK-GATE-START jobs=14"); '
                   'print("proof failure"); raise SystemExit(7)']
        self.assertEqual(run_check(command, output, terminal), 7)
        self.assertIn('proof failure', output.getvalue())
        self.assertIn('CHECK-GATE-START jobs=14', terminal.getvalue())

    def test_progress_requires_real_completion_and_reports_failures_immediately(self):
        self.assertEqual(progress_line('ordinary output\n', 3), (None, 3))
        self.assertEqual(progress_line('CHECK-ATOM-END a exit=0 wall=1s\n', 3), (None, 4))
        self.assertIn('completed: 25', progress_line('CHECK-ATOM-END a exit=0 wall=1s\n', 24)[0])
        self.assertIn('exit=9', progress_line('CHECK-ATOM-END a exit=9 wall=1s\n', 3)[0])

    def test_no_terminal_still_returns_the_actual_command_status(self):
        self.assertEqual(run_check([sys.executable, '-c', 'pass'], io.StringIO()), 0)

    def test_large_failure_keeps_complete_file_and_bounded_hook_output(self):
        summary = io.StringIO()
        command = [sys.executable, '-c',
                   'print("CHECK-GATE-START jobs=14"); '
                   'print("proof diagnostic " * 10000); raise SystemExit(7)']
        self.assertEqual(saved_check(command, summary), 7)
        text = summary.getvalue()
        path = Path(text.splitlines()[0].removeprefix('Full check transcript: '))
        try:
            self.assertIn('proof diagnostic ' * 10000, path.read_text())
            self.assertIn('CHECK-GATE-START jobs=14', text)
            self.assertLess(len(text), 1000)
        finally:
            path.unlink()


if __name__ == '__main__':
    unittest.main()
