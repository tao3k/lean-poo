#!/usr/bin/env python3
"""Alternate historical/current complete gates with unchanged checkout inputs."""
import argparse
import hashlib
import json
import os
import signal
import threading
from pathlib import Path
import re
import statistics
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-ref', default='9a1b17661fcc3189ff762be1865cc737ab5a3434')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=2)
    parser.add_argument('--baseline-jobs', type=int, default=12)
    parser.add_argument('--current-jobs', type=int, default=12)
    args = parser.parse_args()
    if min(args.repeats, args.baseline_jobs, args.current_jobs) < 1:
        parser.error('repeats/jobs must be positive')
    baseline = subprocess.check_output(['git', 'show', args.baseline_ref+':tools/check_gate.py'], cwd=ROOT)
    current = (ROOT/'tools/check_gate.py').read_bytes()
    inventory = json.loads(subprocess.check_output(['python3', 'tools/check_atoms.py', '--list'], cwd=ROOT))
    expected = {a['file'] for a in inventory}
    samples = []
    host_cpus = os.cpu_count()
    with tempfile.TemporaryDirectory(prefix='lean-poo-check-gate-study-') as temporary:
        for repeat in range(args.repeats):
            controls = {}
            for variant in (['baseline', 'current'] if repeat % 2 == 0 else ['current', 'baseline']):
                source = baseline if variant == 'baseline' else current
                # Execute exact historical/current dispatcher text with the same checkout root.
                launcher = Path(temporary)/'run.py'
                launcher.write_text('exec(compile('+repr(source.decode())+', '+repr(str(ROOT/'tools/check_gate.py'))+
                                    ', "exec"), {"__file__": '+repr(str(ROOT/'tools/check_gate.py'))+
                                    ', "__name__": "__main__"})\n')
                print(f'CHECK-GATE-STUDY-RUN repeat={repeat} variant={variant}', flush=True)
                output = []
                load_before = os.getloadavg()
                jobs = args.baseline_jobs if variant == 'baseline' else args.current_jobs
                with subprocess.Popen(['python3', str(launcher), '--jobs', str(jobs)], cwd=ROOT,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True) as process:
                    def expire():
                        try:
                            os.killpg(process.pid, signal.SIGTERM)
                            process.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    watchdog = threading.Timer(180, expire)
                    watchdog.start()
                    try:
                        for line in process.stdout:
                            print(line, end='', flush=True)
                            output.append(line)
                        code = process.wait(timeout=3)
                    finally:
                        watchdog.cancel()
                if code:
                    raise SystemExit(f'{variant} gate failed: {code}')
                rows = [json.loads(line.removeprefix('CHECK-GATE-END ')) for line in output if line.startswith('CHECK-GATE-END ')]
                assert len(rows) == 1 and not rows[0]['failures']
                ended = [re.match(r'CHECK-ATOM-END (\S+) exit=(\d+)', line) for line in output]
                ended = [m for m in ended if m]
                assert len(ended) == len(expected) and {m[1] for m in ended} == expected
                assert all(m[2] == '0' for m in ended)
                transcripts = {p: hashlib.sha256(''.join(line for line in output if line.startswith('['+p+'] ')).encode()).hexdigest() for p in expected}
                controls[variant] = transcripts
                samples.append(dict(repeat=repeat, variant=variant, gate=rows[0],
                                    load_before=load_before, load_after=os.getloadavg(),
                                    executed_dispatcher_sha256=hashlib.sha256(source).hexdigest(),
                                    atom_printed_transcript_sha256=transcripts))
            assert controls['baseline'] == controls['current'], 'Printed per-file Lean output differs'
    medians = {v: {f: statistics.median(s['gate'][f] for s in samples if s['variant'] == v)
                   for f in ['wall_seconds', 'cpu_seconds']} for v in ['baseline', 'current']}
    files = sorted(expected | {str(p.relative_to(ROOT)) for p in (ROOT/'LeanPoo').rglob('*.lean')} |
                   {'LeanPoo.lean', 'Justfile', 'lakefile.toml', 'lean-toolchain', 'tools/check_atoms.py',
                    'tools/check_gate.py', 'tools/tests/test_check_atoms.py', 'tools/tests/test_check_gate.py',
                    'Benchmarks/CheckGateStudy.py'})
    result = dict(schema='lean-poo.check-gate-study.v1', baseline_ref=args.baseline_ref, repeats=args.repeats,
                  samples=samples, medians=medians, host_cpus=host_cpus, printed_atom_transcript_parity=True,
                  executed_dispatcher_sources={'baseline': baseline.decode(), 'current': current.decode()},
                  source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files},
                  limits=['Warm complete gates with recorded file-worker counts, two alternating pairs; host contention uncontrolled',
                          'Historical dispatcher uses current checkout and atomic runner with default threads; exact dispatcher hash recorded separately',
                          'Gate source_sha256 fields describe checkout files; executed_dispatcher_sha256 identifies executed source',
                          'Printed attributed Lean lines match; not byte-for-byte unformatted process output',
                          'No cold/rebuild, confidence interval or CI setup/queue speedup claim'])
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('CHECK-GATE-STUDY-OK '+json.dumps(medians), flush=True)


if __name__ == '__main__':
    main()
