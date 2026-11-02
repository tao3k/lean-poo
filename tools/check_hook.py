#!/usr/bin/env python3
"""Run the complete gate, showing real progress despite hook output capture."""
import json
import subprocess
import sys
import tempfile
import time


def progress_line(line, completed):
    """Summarize actual gate events; never manufacture a periodic heartbeat."""
    if line.startswith('CHECK-ATOM-END '):
        completed += 1
        if completed % 25 == 0 or 'exit=0 ' not in line:
            return f'Lean files completed: {completed}; {line.rstrip()}', completed
    elif line.startswith('CHECK-PHASE-END '):
        result = json.loads(line.removeprefix('CHECK-PHASE-END '))
        return (f"Phase {result['name']}: exit={result['returncode']} "
                f"wall={result['wall_seconds']:.3f}s"), completed
    elif line.startswith('CHECK-GATE-END '):
        result = json.loads(line.removeprefix('CHECK-GATE-END '))
        return (f"Complete gate: {result['wall_seconds']:.3f}s, "
                f"workers={result['jobs']}, failures={result['failures']}"), completed
    elif line.startswith(('CHECK-GATE-START ', 'CHECK-PHASE-START ', 'CHECK-ATOMS-START ',
                          'CHECK-ATOMS-PHASE ')):
        return line.rstrip(), completed
    return None, completed


def run_check(command, output, progress=None):
    """Retain all diagnostics and the exact exit status, teeing concise events."""
    started = time.monotonic()
    completed = 0
    process = subprocess.Popen(command, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True)
    try:
        for line in process.stdout:
            output.write(line)
            output.flush()
            summary, completed = progress_line(line, completed)
            if summary and progress is not None:
                progress.write(f'[{time.monotonic() - started:.1f}s] {summary}\n')
                progress.flush()
        return process.wait()
    finally:
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        process.stdout.close()


def saved_check(command, summary, progress=None):
    """Keep the lossless transcript without replaying it through captured hooks."""
    with tempfile.NamedTemporaryFile(mode='w', prefix='lean-poo-check-',
                                     suffix='.log', delete=False) as transcript:
        message = f'Full check transcript: {transcript.name}\n'
        summary.write(message)
        summary.flush()
        if progress is not None and progress is not summary:
            progress.write(message)
            progress.flush()
        return run_check(command, transcript, progress if progress is not None else summary)


def main():
    # Hook runners capture stdout even when Git has a controlling terminal.
    # CI and detached invocations retain ordinary stdout without needing a tty.
    try:
        terminal = open('/dev/tty', 'w') if not sys.stdout.isatty() else None
    except OSError:
        terminal = None
    try:
        return saved_check(['just', 'check'], sys.stdout, terminal)
    finally:
        if terminal is not None:
            terminal.close()


if __name__ == '__main__':
    sys.exit(main())
