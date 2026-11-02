"""Bounded process-group supervision without timer or reader threads (POSIX)."""
import os
import selectors
import signal
import time
import threading

GROUP_LOCK = threading.RLock()


def kill_group(process):
    """Clean descendants even after the group leader exited; never target our group."""
    with GROUP_LOCK:
        if getattr(process, '_group_stopped', False):
            return
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        # One successful cleanup owns the group. Signalling it again after reaping
        # can hit a zombie-only group (EPERM on Darwin), or an eventually reused ID.
        process._group_stopped = True


def collect(process, on_line, seconds):
    """Stream actual output, enforce a wall deadline and reap the direct child.

    The caller creates a new session. Descendants must remain in that process
    group; deliberately detached sessions need their own supervisor. Killing a
    leader alone and waiting for pipe EOF is insufficient: children inherit it.
    """
    if seconds <= 0:
        raise ValueError('Process deadline must be positive')
    deadline = time.monotonic() + seconds
    pending = b''
    usage = None
    timed_out = False
    os.set_blocking(process.stdout.fileno(), False)

    def deliver(data):
        nonlocal pending
        pending += data
        while b'\n' in pending:
            line, pending = pending.split(b'\n', 1)
            on_line(line + b'\n')

    try:
        with selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ)
            while usage is None:
                if time.monotonic() >= deadline:
                    timed_out = True
                    kill_group(process)
                for key, _ in selector.select(0.05):
                    data = os.read(key.fd, 65536)
                    if data:
                        deliver(data)
                    else:
                        selector.unregister(key.fileobj)
                pid, status, current = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    process.returncode = os.waitstatus_to_exitcode(status)
                    usage = current
        # A successful/failed leader may leave descendants holding stdout open.
        kill_group(process)
        while True:
            try:
                data = os.read(process.stdout.fileno(), 65536)
            except BlockingIOError:
                break
            if not data:
                break
            deliver(data)
        if pending:
            on_line(pending)
        return (124 if timed_out else process.returncode), usage
    finally:
        try:
            kill_group(process)
            if usage is None:
                _, status, _ = os.wait4(process.pid, 0)
                process.returncode = os.waitstatus_to_exitcode(status)
        finally:
            process.stdout.close()
