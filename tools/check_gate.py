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

ROOT = Path(__file__).resolve().parents[1]
LOCK = threading.RLock()
ACTIVE = set()
STOPPING = threading.Event()
GIB = 1024 ** 3


def choose_jobs(cpus, memory_bytes):
    """Cap file workers by CPUs, 12, and a conservative 2 GiB per process.
    Reserve 4 GiB for host/diagnostics; unknown memory permits one worker.
    This is physical-memory capacity, not a measurement of current free memory.
    """
    memory_cap = max(1, (memory_bytes - 4 * GIB) // (2 * GIB)) if memory_bytes else 1
    return max(1, min(cpus or 1, 12, memory_cap))


def host_jobs():
    try:
        memory = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    except (ValueError, OSError):
        memory = None
    return choose_jobs(os.cpu_count(), memory)


def emit(message):
    with LOCK:
        print(message, flush=True)


def run_phase(name, command):
    emit(f'CHECK-PHASE-START {name}')
    started = time.monotonic()
    process = None
    try:
        with LOCK:
            if STOPPING.is_set():
                raise RuntimeError('Gate interrupted before phase launch')
            process = subprocess.Popen(command, cwd=ROOT, start_new_session=True)
            ACTIVE.add(process)
        code = process.wait()
        result = dict(name=name, command=command, returncode=code,
                      wall_seconds=time.monotonic() - started)
    except (OSError, RuntimeError) as error:
        result = dict(name=name, command=command, returncode=1,
                      wall_seconds=time.monotonic() - started, error=str(error))
    finally:
        if process is not None:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
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


def execute(preparation, checks):
    results = []
    if preparation:
        # These phases are independent; library completion still gates atoms/native.
        with ThreadPoolExecutor(max_workers=len(preparation)) as pool:
            futures = [pool.submit(run_phase, name, command) for name, command in preparation]
            results.extend(task.result() for task in futures)
        if any(result['returncode'] for result in results):
            return results
    with ThreadPoolExecutor(max_workers=len(checks)) as pool:
        futures = [pool.submit(run_phase, name, command) for name, command in checks]
        results.extend(task.result() for task in futures)
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
    results = execute(
        [('library', ['lake', 'build', 'LeanPoo', 'indexedRegistryScale', 'scopedTransactionScale', 'keyIndexScale', 'cachedPreparationScale', 'contextSlotScale', 'resultIndexScale']),
         ('supervision', ['python3', '-m', 'unittest', 'discover', '-s', 'tools/tests', '-p', 'test_*.py'])],
        [('types', ['lean', 'LeanPoo/C4/Types.lean']),
         ('atoms', ['python3', 'tools/check_atoms.py', '--jobs', str(jobs)]),
         ('diagnostics', ['just', '--set', 'lean', 'lean', '_check-diagnostics']),
         ('docs', ['just', 'check-docs']),
         ('native', ['just', '_check-native-registry', '_check-native-scoped', '_check-native-key-index', '_check-native-cached', '_check-native-context', '_check-native-result-index'])])
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
