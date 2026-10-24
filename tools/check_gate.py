#!/usr/bin/env python3
"""Complete gate: shared preparation, independent checks, actual phase receipts."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import threading
import time

try:
    from .process_guard import kill_group
    from .check_atoms import atom_phase, load_atoms, phase_workers, select_atoms
except ImportError:
    from process_guard import kill_group
    from check_atoms import atom_phase, load_atoms, phase_workers, select_atoms

ROOT = Path(__file__).resolve().parents[1]
LOCK = threading.RLock()
ACTIVE = set()
STOPPING = threading.Event()
GIB = 1024 ** 3


def choose_jobs(cpus, memory_bytes):
    """Cap workers by CPU capacity and a conservative 2 GiB per process.
    On >=12 logical CPUs, two overlap slots are qualified; absolute cap is 14.
    Reserve 4 GiB for host/diagnostics; unknown memory permits one worker.
    This is physical-memory capacity, not a measurement of current free memory.
    """
    memory_cap = max(1, (memory_bytes - 4 * GIB) // (2 * GIB)) if memory_bytes else 1
    cpu_cap = (cpus + 2) if cpus and cpus >= 12 else (cpus or 1)
    return max(1, min(cpu_cap, 14, memory_cap))


def host_jobs():
    try:
        memory = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    except (ValueError, OSError):
        memory = None
    return choose_jobs(os.cpu_count(), memory)


def emit(message):
    with LOCK:
        print(message, flush=True)


def run_phase(name, command, seconds=300):
    emit(f'CHECK-PHASE-START {name}')
    started = time.monotonic()
    process = None
    try:
        with LOCK:
            if STOPPING.is_set():
                raise RuntimeError('Gate interrupted before phase launch')
            process = subprocess.Popen(command, cwd=ROOT, start_new_session=True)
            ACTIVE.add(process)
        try:
            code = process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            # Let nested atom supervisors kill their separately owned groups.
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                kill_group(process)
                process.wait()
            code = 124
        result = dict(name=name, command=command, returncode=code,
                      wall_seconds=time.monotonic() - started)
    except (OSError, RuntimeError) as error:
        result = dict(name=name, command=command, returncode=1,
                      wall_seconds=time.monotonic() - started, error=str(error))
    finally:
        if process is not None:
            # Always clean the group, including children of an exited leader.
            kill_group(process)
            process.wait()
            with LOCK:
                ACTIVE.discard(process)
    emit('CHECK-PHASE-END ' + json.dumps(result))
    return result


def stop_children(signum, frame):
    STOPPING.set()
    with LOCK:
        for process in ACTIVE:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
    raise SystemExit(128 + signum)


def shard_concurrency(jobs):
    """Share the automatic file budget between at most two active CI shards."""
    if jobs < 1:
        raise ValueError('Jobs must be positive')
    active = min(2, jobs)
    return active, jobs // active


def atom_checks(jobs, receipt=None):
    """Partition the complete canonical inventory into disjoint supervised units.

    Reuse CI's twelve source partitions instead of timing all ordinary files as
    one unit. Each shard retains the phase deadline and original file limits.
    Exclusive SCC/stress checks wait for every ordinary shard. Receipt paths are
    disjoint; the caller bounds simultaneous shards with shard_concurrency.
    """
    inventory = load_atoms()
    _, workers = shard_concurrency(jobs)
    units = [(f'shard-{index}', workers,
              [a for a in select_atoms(inventory, index, 12) if atom_phase(a) == 'atoms'])
             for index in range(12)]
    units.extend((phase, phase_workers(phase, jobs), [a for a in inventory if atom_phase(a) == phase])
                 for phase in ('scc', 'stress'))
    checks = []
    for name, workers, atoms in units:
        if not atoms:
            continue
        command = ['python3', 'tools/check_atoms.py', '--jobs', str(workers),
                   '--files', *[atom['file'] for atom in atoms]]
        if receipt:
            command.extend(['--receipt', str(Path(str(receipt) + '.' + name + '.json'))])
        checks.append((name, command))
    return checks


def execute(preparation, checks, deferred_checks=(), check_workers=None):
    """Run independent checks, then exclusive checks even after check failures."""
    results = []
    if preparation:
        # These phases are independent; library completion still gates atoms/native.
        with ThreadPoolExecutor(max_workers=len(preparation)) as pool:
            futures = [pool.submit(run_phase, name, command) for name, command in preparation]
            results.extend(task.result() for task in futures)
        if any(result['returncode'] for result in results):
            return results
    if checks:
        # Queue admission precedes run_phase, so waiting consumes no deadline.
        with ThreadPoolExecutor(max_workers=len(checks) if check_workers is None else check_workers) as pool:
            futures = [pool.submit(run_phase, name, command) for name, command in checks]
            results.extend(task.result() for task in futures)
    for name, command in deferred_checks:
        results.append(run_phase(name, command))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', default=os.environ.get('LEAN_POO_CHECK_JOBS', 'auto'))
    parser.add_argument('--receipt', type=Path, default=os.environ.get('LEAN_POO_CHECK_RECEIPT'))
    args = parser.parse_args()
    try:
        jobs = host_jobs() if args.jobs == 'auto' else int(args.jobs)
        if jobs < 1:
            raise ValueError()
    except ValueError:
        parser.error('--jobs must be auto or a positive integer')
    signal.signal(signal.SIGTERM, stop_children)
    signal.signal(signal.SIGINT, stop_children)
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    emit(f'CHECK-GATE-START jobs={jobs}')
    atoms = atom_checks(jobs, os.environ.get('LEAN_POO_ATOM_RECEIPT'))
    results = execute(
        [('library', ['lake', 'build', 'LeanPoo', 'LeanPoo:shared', 'Examples.Support.GeneralizedFork:dynlib', 'Examples', 'indexedRegistryScale', 'scopedTransactionScale', 'keyIndexScale', 'cachedPreparationScale', 'contextSlotScale', 'resultIndexScale', 'cyclicClosureScale', 'closureLayoutScale', 'hybridClosureScale']),
         ('supervision', ['python3', '-m', 'unittest', 'discover', '-s', 'tools/tests', '-p', 'test_*.py'])],
        [('types', ['lean', '-j', '2', 'LeanPoo/C4/Types.lean']),
         *[(name, command) for name, command in atoms if name.startswith('shard-')],
         ('diagnostics', ['just', '--set', 'lean', 'lean', '_check-diagnostics']),
         ('docs', ['just', 'check-docs']),
         ('native', ['just', '_check-native-registry', '_check-native-scoped', '_check-native-key-index', '_check-native-cached', '_check-native-context', '_check-native-result-index'])],
        [(name, command) for name, command in atoms if name in ('scc', 'stress')],
        check_workers=shard_concurrency(jobs)[0])
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt = dict(schema='lean-poo.check-gate.v1', jobs=jobs, phases=results,
                   wall_seconds=time.monotonic() - started,
                   cpu_seconds=after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
                   failures=[r['name'] for r in results if r['returncode']],
                   source_sha256={p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                                  for p in ['Justfile', 'lakefile.toml', 'tools/check_atoms.py', 'tools/check_gate.py']})
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    emit('CHECK-GATE-END ' + json.dumps(receipt))
    return 1 if receipt['failures'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
