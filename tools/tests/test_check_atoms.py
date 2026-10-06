"""Orchestration admission: partition coverage and real process failure status."""
import contextlib
import io
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

from tools.check_atoms import configure_threads, execute, load_atoms, select_atoms


class CheckAtomsTests(unittest.TestCase):
    def test_every_inventory_file_runs_in_exactly_one_nonempty_shard(self):
        atoms = load_atoms()
        partitions = [select_atoms(atoms, index, 12) for index in range(12)]
        self.assertTrue(all(partitions))
        files = [atom['file'] for partition in partitions for atom in partition]
        self.assertEqual(len(files), len(set(files)))
        self.assertEqual(set(files), {atom['file'] for atom in atoms})
        bounded = [a for a in atoms if a['command'][0] == 'timeout']
        self.assertEqual(len(bounded), 3)
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
