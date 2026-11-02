"""Real recursive/forking failures cannot strand compiler groups or reader threads."""
import os
import selectors
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
    def start(self, program, pass_fds=()):
        """Own one process group, inheriting only explicit fixture-ready pipes."""
        return subprocess.Popen([sys.executable, '-u', '-c', program],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                start_new_session=True, pass_fds=pass_fds)

    def test_term_ignoring_recursion_is_bounded_and_reaped(self):
        before = {t.ident for t in threading.enumerate()}
        ready, notify = os.pipe()
        try:
            process = self.start('import signal,os,time\ntime.sleep(0.3)\n'
                                 'signal.signal(signal.SIGTERM,signal.SIG_IGN)\n'
                                 f'print("recursive-ready",flush=True)\nos.write({notify},b"R")\n'
                                 'while True: pass\n', pass_fds=(notify,))
        except BaseException:
            os.close(ready)
            raise
        finally:
            os.close(notify)
        try:
            # Establish the adversarial fixture BEFORE measuring its watchdog.
            # A separate fd leaves the actual stdout assertion to collect().
            with selectors.DefaultSelector() as selector:
                selector.register(ready, selectors.EVENT_READ)
                self.assertTrue(selector.select(2), 'recursive fixture did not become ready')
                self.assertEqual(os.read(ready, 1), b'R')
            lines = []
            started = time.monotonic()
            code, _ = collect(process, lines.append, 0.2)
        finally:
            os.close(ready)
            kill_group(process)
            process.wait(timeout=3)
            process.stdout.close()
        self.assertEqual(code, 124)
        self.assertLess(time.monotonic() - started, 3)
        self.assertIn(b'recursive-ready\n', lines)
        with self.assertRaises(ProcessLookupError):
            os.kill(process.pid, 0)
        self.assertEqual({t.ident for t in threading.enumerate()}, before)

    def test_startup_without_readiness_is_bounded_and_reaped(self):
        """The production watchdog also bounds a child that never becomes ready."""
        before = {t.ident for t in threading.enumerate()}
        process = self.start('import time\ntime.sleep(5)\n')
        lines = []
        started = time.monotonic()
        code, _ = collect(process, lines.append, 0.2)
        self.assertEqual(code, 124)
        self.assertLess(time.monotonic() - started, 3)
        self.assertEqual(lines, [])
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
