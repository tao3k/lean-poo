"""Orchestration admission: partition coverage and real process failure status."""
import contextlib
import io
from pathlib import Path
import sys
import subprocess
import tempfile
import time
import unittest
import threading
from unittest.mock import patch

from tools.check_atoms import configure_limits, configure_threads, execute, execution_lanes, load_atoms, select_atoms


class CheckAtomsTests(unittest.TestCase):
    def test_deadline_lane_preserves_every_command_and_total_worker_ceiling(self):
        atoms = load_atoms()
        for jobs in (1, 2, 4, 14):
            lanes = execution_lanes(atoms, jobs)
            self.assertLessEqual(sum(workers for workers, _ in lanes), jobs)
            assigned = [atom for _, lane in lanes for atom in lane]
            self.assertCountEqual(assigned, atoms)
            if jobs > 1:
                self.assertLessEqual(lanes[0][0], 2)
                self.assertTrue(all(a['command'][0] == 'timeout' for a in lanes[0][1]))

    def test_deadline_jobs_actually_overlap_without_crowding_all_workers(self):
        atoms = [dict(file=f'bounded-{i}', command=['timeout', '30s']) for i in range(8)]
        atoms += [dict(file=f'ordinary-{i}', command=['lean']) for i in range(8)]
        lock = threading.Lock()
        active = [0, 0]
        peak = [0, 0]

        def fixture(atom):
            bounded = atom['command'][0] == 'timeout'
            with lock:
                active[0] += 1
                active[1] += int(bounded)
                peak[0] = max(peak[0], active[0])
                peak[1] = max(peak[1], active[1])
            time.sleep(0.02)
            with lock:
                active[0] -= 1
                active[1] -= int(bounded)
            return dict(file=atom['file'], returncode=0)

        with patch('tools.check_atoms.run_atom', fixture):
            results = execute(atoms, 4)
        self.assertEqual(peak[1], 2)
        self.assertLessEqual(peak[0], 4)
        self.assertCountEqual([r['file'] for r in results], [a['file'] for a in atoms])
        self.assertEqual(active, [0, 0])

    def test_every_inventory_file_runs_in_exactly_one_nonempty_shard(self):
        atoms = load_atoms()
        partitions = [select_atoms(atoms, index, 12) for index in range(12)]
        self.assertTrue(all(partitions))
        files = [atom['file'] for partition in partitions for atom in partition]
        self.assertEqual(len(files), len(set(files)))
        self.assertEqual(set(files), {atom['file'] for atom in atoms})
        bounded = [a for a in atoms if a['command'][0] == 'timeout']
        self.assertEqual(len(bounded), 42)
        for atom in bounded:
            self.assertIn('30s', atom['command'])
            self.assertIn('2048', atom['command'])
            self.assertIn('10000000', atom['command'])

    def test_thread_policy_preserves_inventory_and_bounded_arguments(self):
        atoms = load_atoms()
        changed = configure_threads(atoms, 1)
        self.assertEqual([a['file'] for a in atoms], [a['file'] for a in changed])
        for original, configured in zip(atoms, changed):
            command = list(configured['command'])
            position = command.index('lean') + 1
            self.assertEqual(command[position:position+2], ['-j', '1'])
            del command[position:position+2]
            self.assertEqual(command, original['command'])
        self.assertIs(configure_threads(atoms, None), atoms)
        with self.assertRaises(ValueError):
            configure_threads(atoms, 0)

    def test_every_atom_has_a_memory_and_allocation_budget(self):
        for atom in configure_limits(load_atoms()):
            self.assertTrue(any(arg.startswith('-M') for arg in atom['command']))
            self.assertTrue(any(arg.startswith('-T') for arg in atom['command']))
        bounded = dict(file='fixture',command=['lean','-M','512','-T','100','fixture'])
        self.assertEqual(configure_limits([bounded]), [bounded])

    def test_bad_or_empty_shard_and_unknown_file_fail(self):
        atoms = load_atoms()
        for index, count in [(-1, 12), (12, 12), (0, 0), (0, len(atoms) + 1)]:
            with self.assertRaises(ValueError):
                select_atoms(atoms, index, count)
        with self.assertRaises(ValueError):
            select_atoms(atoms, 0, 1, ['Tests/NotInInventory.lean'])

    def test_real_failure_timeout_and_launch_error_do_not_become_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'process.py'
            source.write_text('import sys,time\nprint("actual child output",flush=True)\n'
                              'if sys.argv[1] == "sleep": time.sleep(3)\n'
                              'else: sys.exit(int(sys.argv[1]))\n')
            atoms = [dict(file=str(source), recipe='supervisor-fixture',
                          command=[sys.executable, str(source), str(code)])
                     for code in (0, 7)]
            atoms.append(dict(file=str(source), recipe='supervisor-fixture',
                              command=['timeout', '0.1s', sys.executable, str(source), 'sleep']))
            atoms.append(dict(file=str(source), recipe='supervisor-fixture',
                              command=['/nonexistent-lean-poo-test-command']))
            with contextlib.redirect_stdout(io.StringIO()):
                results = execute(atoms, 2)
            self.assertEqual(sorted(r['returncode'] for r in results), [0, 1, 7, 124])
            self.assertEqual(len(results), len(atoms))
            self.assertEqual(len([r for r in results if r['returncode']]), 3)
            for result in results:
                if 'wall_seconds' in result:
                    self.assertGreaterEqual(result['cpu_seconds'], 0)
                    self.assertLess(result['cpu_seconds'], result['wall_seconds'] + 0.1)

    def test_interruption_exits_with_a_worker_blocked_on_progress_output(self):
        # A closed/undrained parent log must not make executor shutdown join forever.
        with tempfile.TemporaryDirectory() as temporary:
            ready = Path(temporary) / 'writer-ready'
            program = (
                'import signal,threading; from pathlib import Path; '
                'from concurrent.futures import ThreadPoolExecutor; '
                'from tools.check_atoms import emit,stop_children; '
                'signal.signal(signal.SIGTERM,stop_children); '
                f'ready=Path({str(ready)!r}); '
                'pool=ThreadPoolExecutor(max_workers=1); '
                'pool.submit(lambda: (ready.write_text("ready"),emit("x"*1048576))); '
                'signal.pause()'
            )
            child = subprocess.Popen([sys.executable, '-u', '-c', program],
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 3
                while not ready.exists() and time.monotonic() < deadline and child.poll() is None:
                    time.sleep(0.01)
                self.assertTrue(ready.exists(), 'Progress writer did not start')
                # Leave stdout unread so its worker cannot finish the 1 MiB write.
                child.terminate()
                self.assertEqual(child.wait(timeout=2), 143)
            finally:
                if child.poll() is None:
                    child.kill()
                    child.wait(timeout=2)
                child.stdout.close()

    def test_interruption_stops_children_and_prevents_queued_launches(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'sleep.py'
            marker = Path(temporary) / 'launches.txt'
            source.write_text('import time\n'
                              f'with open({str(marker)!r},"a") as f: f.write("launched\\n")\n'
                              'print("child-ready",flush=True)\ntime.sleep(20)\n')
            program = (
                'import signal; from tools.check_atoms import execute,stop_children; '
                'signal.signal(signal.SIGTERM,stop_children); '
                f'atom=dict(file={str(source)!r},recipe="fixture",command=[{sys.executable!r},{str(source)!r}]); '
                'execute([atom,atom,atom],1)'
            )
            child = subprocess.Popen([sys.executable, '-u', '-c', program],
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            try:
                while 'child-ready' not in child.stdout.readline():
                    if child.poll() is not None:
                        self.fail('Supervisor exited before actual child output')
                child.terminate()
                output, _ = child.communicate(timeout=5)
                self.assertEqual(child.returncode, 143)
                self.assertNotIn('child-ready', output)
                self.assertEqual(marker.read_text(), 'launched\n')
            finally:
                if child.poll() is None:
                    child.kill()
                    child.wait()
                child.stdout.close()


if __name__ == '__main__':
    unittest.main()
