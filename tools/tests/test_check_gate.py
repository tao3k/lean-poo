"""Gate admission: resource caps and real failing preparation/check processes."""
import contextlib
import io
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

from tools.check_gate import GIB, atom_checks, choose_jobs, execute, shard_concurrency
from tools.check_atoms import atom_phase, load_atoms, select_atoms


class CheckGateTests(unittest.TestCase):
    def test_supervised_units_cover_the_complete_inventory_once(self):
        inventory = load_atoms()
        units = atom_checks(4, '/tmp/atom-receipt')
        self.assertEqual([name for name, _ in units],
                         [f'shard-{index}' for index in range(12)] + ['scc', 'stress'])
        selected = []
        receipts = []
        for name, command in units:
            selected.extend(command[command.index('--files') + 1:command.index('--receipt')])
            receipts.append(command[command.index('--receipt') + 1])
            self.assertEqual(command[command.index('--jobs') + 1],
                             '1' if name == 'scc' else '2')
        self.assertCountEqual(selected, [a['file'] for a in inventory])
        self.assertEqual(len(selected), len(set(selected)))
        self.assertEqual(len(set(receipts)), len(units))
        for index, (_, command) in enumerate(units[:12]):
            files = command[command.index('--files') + 1:command.index('--receipt')]
            self.assertEqual(files, [a['file'] for a in select_atoms(inventory, index, 12)
                                     if atom_phase(a) == 'atoms'])
        scc = units[12][1]
        self.assertEqual(scc[scc.index('--files') + 1:scc.index('--receipt')],
                         ['Examples/ComponentRounds.lean'])
        stress = units[13][1]
        self.assertEqual(set(stress[stress.index('--files') + 1:stress.index('--receipt')]),
                         {a['file'] for a in inventory if a['command'][0] == 'timeout'
                          and a['file'] != 'Examples/ComponentRounds.lean'})

    def test_shards_share_the_worker_budget_instead_of_multiplying_it(self):
        for jobs in (1, 2, 3, 4, 8, 14):
            active, workers = shard_concurrency(jobs)
            self.assertGreaterEqual(active, 1)
            self.assertGreaterEqual(workers, 1)
            self.assertLessEqual(active * workers, jobs)
            for name, command in atom_checks(jobs):
                self.assertEqual(int(command[command.index('--jobs') + 1]),
                                 workers if name.startswith('shard-') else
                                 (min(2, jobs) if name == 'stress' else 1))

    def test_exclusive_checks_wait_and_still_run_after_a_check_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            marker = Path(temporary) / 'ordinary-finished'
            ordinary = f'from pathlib import Path; Path({str(marker)!r}).touch(); raise SystemExit(9)'
            completed = Path(temporary) / 'scc-finished'
            scc = (f'from pathlib import Path; assert Path({str(marker)!r}).exists(); '
                   f'Path({str(completed)!r}).touch(); raise SystemExit(7)')
            exclusive = f'from pathlib import Path; assert Path({str(completed)!r}).exists()'
            with contextlib.redirect_stdout(io.StringIO()):
                results = execute([], [('ordinary', [sys.executable, '-c', ordinary])],
                                  [('scc', [sys.executable, '-c', scc]),
                                   ('stress', [sys.executable, '-c', exclusive])])
            self.assertEqual([(r['name'], r['returncode']) for r in results],
                             [('ordinary', 9), ('scc', 7), ('stress', 0)])

    def test_auto_workers_obey_cpu_and_memory_caps(self):
        self.assertEqual(choose_jobs(12, 32 * GIB), 14)
        self.assertEqual(choose_jobs(12, 24 * GIB), 10)
        self.assertEqual(choose_jobs(8, 32 * GIB), 8)
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
                                  [('must-not-run', [sys.executable, '-c', f'open({str(marker)!r},"w").close()'])],
                                  [('deferred-must-not-run', [sys.executable, '-c', f'open({str(marker)!r},"w").close()'])])
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

    def test_independent_preparation_overlaps_but_checks_wait_for_all(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'prepare.py'
            markers = [Path(temporary) / name for name in ['library', 'types', 'supervision']]
            source.write_text('import pathlib,sys,time\n'
                              'markers=[pathlib.Path(p) for p in sys.argv[1:]]\n'
                              'markers[0].touch()\ndeadline=time.monotonic()+5\n'
                              'while not all(p.exists() for p in markers):\n'
                              ' if time.monotonic()>deadline: raise SystemExit(8)\n'
                              ' time.sleep(0.01)\n')
            preparations = [(path.name, [sys.executable, str(source), str(path),
                                        *[str(p) for p in markers if p != path]]) for path in markers]
            verify = 'from pathlib import Path; assert all(Path(p).exists() for p in ' + repr([str(p) for p in markers]) + ')'
            with contextlib.redirect_stdout(io.StringIO()):
                results = execute(preparations, [('checks', [sys.executable, '-c', verify])])
            self.assertEqual([r['returncode'] for r in results], [0, 0, 0, 0])

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
