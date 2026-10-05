"""Gate admission: resource caps and real failing preparation/check processes."""
import contextlib
import io
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

from tools.check_gate import GIB, choose_jobs, execute


class CheckGateTests(unittest.TestCase):
    def test_auto_workers_obey_cpu_and_memory_caps(self):
        self.assertEqual(choose_jobs(12, 32 * GIB), 12)
        self.assertEqual(choose_jobs(64, 8 * GIB), 2)
        self.assertEqual(choose_jobs(2, 32 * GIB), 2)
        self.assertEqual(choose_jobs(12, None), 1)
        self.assertEqual(choose_jobs(None, 32 * GIB), 1)
        self.assertEqual(choose_jobs(12, 2 * GIB), 1)

    def test_failed_preparation_prevents_all_check_launches(self):
        with tempfile.TemporaryDirectory() as temporary:
            marker = Path(temporary) / 'launched'
            with contextlib.redirect_stdout(io.StringIO()):
                results = execute([('failed-build', [sys.executable, '-c', 'raise SystemExit(7)'])],
                                  [('must-not-run', [sys.executable, '-c', f'open({str(marker)!r},"w").close()'])])
            self.assertEqual([r['returncode'] for r in results], [7])
            self.assertFalse(marker.exists())

    def test_independent_phases_launch_concurrently(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'barrier.py'
            marker = Path(temporary) / 'started'
            source.write_text('import pathlib,time\n'
                              f'p=pathlib.Path({str(marker)!r})\n'
                              'with p.open("a") as f: f.write("started\\n")\n'
                              'deadline=time.monotonic()+5\n'
                              'while len(p.read_text().splitlines())<3:\n'
                              ' if time.monotonic()>deadline: raise SystemExit(8)\n'
                              ' time.sleep(0.01)\n')
            with contextlib.redirect_stdout(io.StringIO()):
                results = execute([], [(name, [sys.executable, str(source)]) for name in ['atoms', 'diagnostics', 'docs']])
            self.assertEqual([r['returncode'] for r in results], [0, 0, 0])
            self.assertEqual(marker.read_text().splitlines(), ['started'] * 3)

    def test_interruption_stops_active_phase_processes(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'waiting.py'
            marker = Path(temporary) / 'pids'
            source.write_text('import os,time\n'
                              f'with open({str(marker)!r},"a") as f: f.write(str(os.getpid())+"\\n")\n'
                              'print("phase-child-ready",flush=True)\ntime.sleep(20)\n')
            command = (
                'import signal; from tools.check_gate import execute,stop_children; '
                'signal.signal(signal.SIGTERM,stop_children); '
                f'command=[{sys.executable!r},{str(source)!r}]; '
                'execute([],[("a",command),("b",command),("c",command)])'
            )
            parent = subprocess.Popen([sys.executable, '-u', '-c', command],
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            try:
                while 'phase-child-ready' not in parent.stdout.readline():
                    if parent.poll() is not None:
                        self.fail('Gate exited before actual phase output')
                parent.terminate()
                parent.communicate(timeout=5)
                self.assertEqual(parent.returncode, 143)
                for pid in marker.read_text().splitlines():
                    with self.assertRaises(ProcessLookupError):
                        os.kill(int(pid), 0)
            finally:
                if parent.poll() is None:
                    parent.kill()
                    parent.wait()
                parent.stdout.close()

    def test_failed_check_or_launch_cannot_be_hidden_by_successful_siblings(self):
        with contextlib.redirect_stdout(io.StringIO()):
            results = execute([], [('good', [sys.executable, '-c', 'pass']),
                                   ('bad', [sys.executable, '-c', 'raise SystemExit(9)']),
                                   ('launch-error', ['/nonexistent-lean-poo-check'])])
        self.assertEqual(sorted(r['returncode'] for r in results), [0, 1, 9])
        self.assertEqual({r['name'] for r in results}, {'good', 'bad', 'launch-error'})


if __name__ == '__main__':
    unittest.main()
