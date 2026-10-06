#!/usr/bin/env python3
"""Run independent Lean files from the canonical Justfile recipes."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
RECIPES = ('_check-examples', '_check-contracts')
PRINT_LOCK = threading.Lock()
PROCESS_LOCK = threading.Lock()
ACTIVE = set()
STOPPING = threading.Event()


def emit(message):
    with PRINT_LOCK:
        print(message, flush=True)


def load_atoms():
    dump = json.loads(subprocess.check_output(
        ['just', '--dump', '--dump-format', 'json'], cwd=ROOT, text=True))
    atoms = []
    for recipe in RECIPES:
        for row in dump['recipes'][recipe]['body']:
            pieces = []
            for part in row:
                if isinstance(part, str):
                    pieces.append(part)
                elif part == [['variable', 'lean']]:
                    pieces.append('lean')
                else:
                    raise ValueError(f'Unsupported recipe expression in {recipe}: {part!r}')
            command = shlex.split(''.join(pieces))
            # Fail closed if the source-owned inventory grows shell operations.
            if not command or command[0] not in ('lean', 'timeout') or 'lean' not in command:
                raise ValueError(f'Unsupported atom in {recipe}: {command!r}')
            file = command[-1]
            if not file.endswith('.lean') or not (ROOT / file).is_file():
                raise ValueError(f'Invalid Lean file in {recipe}: {file}')
            if any(token in (';', '&&', '||', '|', '>') for token in command):
                raise ValueError(f'Shell operation in atom: {command!r}')
            atoms.append({'recipe': recipe, 'file': file, 'command': command})
    if len({a['file'] for a in atoms}) != len(atoms):
        raise ValueError('Duplicate Lean file in canonical atom inventory')
    return atoms


def select_atoms(atoms, shard, shards, files=None):
    if shards < 1 or shard < 0 or shard >= shards:
        raise ValueError('Shard must satisfy 0 <= shard < shards')
    if shards > len(atoms):
        raise ValueError('Shard count would create empty checks')
    selected = atoms[shard::shards]
    if files:
        requested = set(files)
        unknown = requested - {a['file'] for a in atoms}
        if unknown:
            raise ValueError(f'Unknown inventory files: {sorted(unknown)}')
        selected = [a for a in selected if a['file'] in requested]
    if not selected:
        raise ValueError('Empty atom selection')
    return selected



def configure_threads(atoms, threads):
    """Adjust only Lean's worker pool, retaining timeout/resource arguments."""
    if threads is None:
        return atoms
    if threads < 1:
        raise ValueError('Lean thread count must be positive')
    configured = []
    for atom in atoms:
        command = list(atom['command'])
        position = command.index('lean') + 1
        command[position:position] = ['-j', str(threads)]
        configured.append(dict(atom, command=command))
    return configured


def run_atom(atom):
    file = atom['file']
    emit(f'CHECK-ATOM-START {file}')
    started = time.monotonic()
    digest = hashlib.sha256()
    with PROCESS_LOCK:
        if STOPPING.is_set():
            raise RuntimeError('Check interrupted before launch')
        process = subprocess.Popen(atom['command'], cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        ACTIVE.add(process)
    try:
        for line in iter(process.stdout.readline, b''):
            digest.update(line)
            emit(f'[{file}] {line.decode(errors="replace").rstrip()}')
        code = process.wait()
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        process.stdout.close()
        with PROCESS_LOCK:
            ACTIVE.discard(process)
    elapsed = time.monotonic() - started
    emit(f'CHECK-ATOM-END {file} exit={code} wall={elapsed:.3f}s')
    return dict(file=file, recipe=atom['recipe'], command=atom['command'],
                returncode=code, wall_seconds=elapsed, transcript_sha256=digest.hexdigest(),
                source_sha256=hashlib.sha256((ROOT / file).read_bytes()).hexdigest())


def stop_children(signum, frame):
    STOPPING.set()
    with PROCESS_LOCK:
        for process in ACTIVE:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
    raise SystemExit(128 + signum)


def execute(atoms, jobs):
    if jobs < 1:
        raise ValueError('Jobs must be positive')
    results = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending = {pool.submit(run_atom, atom): atom for atom in atoms}
        for task in as_completed(pending):
            atom = pending[task]
            try:
                results.append(task.result())
            except Exception as error:
                # Launch/read failures are failed atoms, never missing successes.
                emit(f'CHECK-ATOM-ERROR {atom["file"]}: {error}')
                results.append(dict(file=atom['file'], returncode=1, error=str(error)))
    return sorted(results, key=lambda item: item['file'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--lean-threads', type=int)
    parser.add_argument('--shard', type=int, default=0)
    parser.add_argument('--shards', type=int, default=1)
    parser.add_argument('--files', nargs='+')
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    try:
        inventory = load_atoms()
        atoms = configure_threads(select_atoms(inventory, args.shard, args.shards, args.files), args.lean_threads)
        if args.jobs < 1:
            raise ValueError('Jobs must be positive')
    except (ValueError, subprocess.SubprocessError) as error:
        parser.error(str(error))
    if args.list:
        print(json.dumps(atoms, indent=2))
        return 0
    signal.signal(signal.SIGTERM, stop_children)
    signal.signal(signal.SIGINT, stop_children)
    started = time.monotonic()
    emit(f'CHECK-ATOMS-START files={len(atoms)} jobs={args.jobs} shard={args.shard}/{args.shards}')
    results = execute(atoms, args.jobs)
    failures = [r['file'] for r in results if r['returncode'] != 0]
    receipt = dict(schema='lean-poo.check-atoms.v1', jobs=args.jobs, shard=args.shard,
                   shards=args.shards, lean_threads=args.lean_threads, inventory_files=len(inventory), selected_files=len(atoms),
                   wall_seconds=time.monotonic() - started, failures=failures, results=results,
                   justfile_sha256=hashlib.sha256((ROOT / 'Justfile').read_bytes()).hexdigest())
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    emit(f'CHECK-ATOMS-END files={len(results)} failures={len(failures)} wall={receipt["wall_seconds"]:.3f}s')
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
