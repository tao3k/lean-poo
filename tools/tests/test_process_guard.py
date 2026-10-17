"""Real recursive/forking failures cannot strand compiler groups or reader threads."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

from tools.process_guard import collect, kill_group


class ProcessGuardTests(unittest.TestCase):
    def start(self, program):
        return subprocess.Popen([sys.executable, '-u', '-c', program],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                start_new_session=True)

    def test_term_ignoring_recursion_is_bounded_and_reaped(self):
        before = {t.ident for t in threading.enumerate()}
        process = self.start('import signal\nsignal.signal(signal.SIGTERM,signal.SIG_IGN)\n'
                             'print("recursive-ready",flush=True)\nwhile True: pass\n')
        lines = []
        started = time.monotonic()
        code, _ = collect(process, lines.append, 0.2)
        self.assertEqual(code, 124)
        self.assertLess(time.monotonic() - started, 3)
        self.assertIn(b'recursive-ready\n', lines)
        with self.assertRaises(ProcessLookupError):
            os.kill(process.pid, 0)
        self.assertEqual({t.ident for t in threading.enumerate()}, before)

    def test_exited_leader_does_not_wait_for_descendant_pipe_eof(self):
        with tempfile.TemporaryDirectory() as temporary:
            marker = Path(temporary) / 'escaped-work'
            child = ('import signal,time,pathlib; '
                     'signal.signal(signal.SIGTERM,signal.SIG_IGN); '
                     f'time.sleep(0.8);pathlib.Path({str(marker)!r}).touch();time.sleep(5)')
            program = (f'import subprocess,sys; subprocess.Popen([sys.executable,"-c",{child!r}]); '
                       'print("leader-done",flush=True)')
            process = self.start(program)
            lines = []
            started = time.monotonic()
            code, _ = collect(process, lines.append, 2)
            self.assertEqual(code, 0)
            self.assertLess(time.monotonic() - started, 0.8)
            time.sleep(0.9)
            self.assertFalse(marker.exists(), 'descendant survived the exited group leader')
            self.assertIn(b'leader-done\n', lines)

    def test_completed_cleanup_never_signals_the_group_twice(self):
        process = self.start('print("done",flush=True)')
        self.assertEqual(collect(process, lambda _line: None, 2)[0], 0)
        with patch('tools.process_guard.os.killpg', side_effect=PermissionError('second signal')) as send:
            kill_group(process)
            send.assert_not_called()

    def test_output_failure_also_reaps_the_child(self):
        process = self.start('import time;print("ready",flush=True);time.sleep(5)')
        def refuse(_line):
            raise RuntimeError('broken output sink')
        with self.assertRaisesRegex(RuntimeError, 'broken output sink'):
            collect(process, refuse, 2)
        with self.assertRaises(ProcessLookupError):
            os.kill(process.pid, 0)
