#!/usr/bin/env python3
"""One leased physical CPU: fresh, frozen arithmetic comparison and model replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.process_budget import run_with_budget


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('manifest', 'baseline', 'candidate', 'z3', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cvc5', type=Path)
    parser.add_argument('--index', type=int, required=True)
    parser.add_argument('--timeout', type=int, default=60)
    parser.add_argument('--memory-gib', type=int, default=16)
    parser.add_argument('--validate-models', action='store_true')
    args = parser.parse_args()
    if not os.environ.get('EOS_CPU_IDS'):
        parser.error('run through ExperimentOS with a leased CPU')
    leased = {int(value) for value in os.environ['EOS_CPU_IDS'].split(',')}
    if len(leased) != 1 or os.sched_getaffinity(0) != leased:
        parser.error('exactly one leased CPU must match the process affinity')
    cpu = next(iter(leased))
    os.sched_setaffinity(0, {cpu})
    manifest = json.loads(args.manifest.read_text())
    case = manifest['cases'][args.index]
    if digest(case['path']) != case['sha256']:
        raise ValueError('input hash mismatch')
    out = args.output / f'case-{args.index:03}'
    out.mkdir(parents=True, exist_ok=False)
    commands = dict(baseline=[str(args.baseline), 'solve'],
                    candidate=[str(args.candidate), 'solve'], z3=[str(args.z3)])
    controls = Path(__file__).resolve().parents[2] / 'src/base/controls.json'
    names = {c['name'] for c in json.loads(controls.read_text())['controls']}
    environment = {k: v for k, v in os.environ.items() if k not in names}

    protocol_errors = []

    def invoke(label, command, source, tail=()):
        cmd = ['prlimit', '--as=' + str(args.memory_gib * 1024**3),
               '--cpu=' + str(args.timeout + 2) + ':' + str(args.timeout + 3),
               '--', *command, str(source), *tail]
        stdout, stderr, timing = run_with_budget(cmd, args.timeout, environment)
        if timing['budget_overrun']:
            protocol_errors.append(dict(label=label, **timing))
        (out / (label + '.stdout')).write_bytes(stdout)
        (out / (label + '.stderr')).write_bytes(stderr)
        answers = re.findall(r'^(sat|unsat|unknown)\s*$', stdout.decode(errors='replace'), re.M)
        if timing['timed_out'] or stdout.strip() == b'timeout':
            result = 'timeout'
        elif timing['returncode'] == 0 and len(answers) == 1:
            result = answers[0]
        elif re.search(rb'bad_alloc|out of memory|cannot allocate', stderr, re.I):
            result = 'memout'
        else:
            result = 'error'
        return dict(result=result, **timing, command=cmd, cpu=cpu)

    binaries = {name: dict(path=cmd[0], sha256=digest(cmd[0])) for name, cmd in commands.items()}
    report = dict(index=args.index, case=case, binaries=binaries,
                  manifest_sha256=digest(args.manifest), timeout=args.timeout,
                  memory_bytes=args.memory_gib * 1024**3, observations={})
    # Rotate version/oracle order on the same physical CPU. Historical oracle
    # rows never substitute for a fresh timed invocation.
    order = list(commands)
    offset = args.index % len(order)
    for name in order[offset:] + order[:offset]:
        tail = ('--timeout', str(args.timeout)) if name != 'z3' else ()
        cmd = commands[name] + (['-T:' + str(args.timeout)] if name == 'z3' else [])
        report['observations'][name] = invoke(name, cmd, case['path'], tail)
        (out / 'progress.json').write_text(json.dumps(report, indent=2) + '\n')
    verdicts = {o['result'] for o in report['observations'].values() if o['result'] in ('sat', 'unsat')}
    expected = case.get('expected', 'unknown')
    wrong = len(verdicts) > 1 or expected in ('sat', 'unsat') and any(v != expected for v in verdicts)
    report['wrong_verdict'] = bool(wrong)
    report['protocol_errors'] = protocol_errors
    if args.validate_models:
        sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'fuzz'))
        from fuzz_theory_applications import parse, emit, replay
        prefix = '\n'.join(emit(c) for c in parse(Path(case['path']).read_text())
                           if emit(c[0]) not in ('check-sat', 'get-model', 'exit', 'set-info', 'set-option'))
        for name in ('baseline', 'candidate', 'z3'):
            observation = report['observations'][name]
            observation['verified'] = False
            if observation['result'] == 'unsat':
                independent = (any(report['observations'][n]['result'] == 'unsat'
                                   for n in ('baseline', 'candidate')) if name == 'z3'
                               else report['observations']['z3']['result'] == 'unsat')
                if not independent and args.cvc5:
                    checked = invoke(name + '-unsat-check',
                        [str(args.cvc5), '--lang=smt2', '--tlimit=' + str(args.timeout * 1000)], case['path'])
                    observation['unsat_check'] = checked
                    independent = checked['result'] == 'unsat'
                    if checked['result'] == 'sat':
                        wrong = True
                        report['wrong_verdict'] = True
                observation['verified'] = not wrong and independent
            elif observation['result'] == 'sat':
                model_source = out / (name + '-model.smt2')
                model_source.write_text('(set-option :produce-models true)\n' + prefix + '\n(check-sat)\n(get-model)\n')
                cmd = commands[name] + (['-T:' + str(args.timeout)] if name == 'z3' else [])
                tail = ('--timeout', str(args.timeout)) if name != 'z3' else ()
                model = invoke(name + '-model', cmd, model_source, tail)
                observation['model'] = model
                try:
                    if model['result'] != 'sat':
                        raise ValueError('model query did not return SAT')
                    pinned = out / (name + '-replay.smt2')
                    pinned.write_text(replay(prefix, (out / (name + '-model.stdout')).read_text()))
                    checker = [str(args.cvc5), '--lang=smt2', '--tlimit=' + str(args.timeout * 1000)] if name == 'z3' and args.cvc5 else commands['z3'] + ['-T:' + str(args.timeout)]
                    if name == 'z3' and not args.cvc5:
                        raise ValueError('independent model checker required for Z3')
                    checked = invoke(name + '-replay', checker, pinned)
                    observation['replay'] = checked
                    observation['verified'] = not wrong and checked['result'] == 'sat'
                except ValueError as error:
                    observation['model_error'] = str(error)
    for name, spec in binaries.items():
        if digest(spec['path']) != spec['sha256']:
            raise ValueError('solver changed during comparison: ' + name)
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    metrics = dict(cases=1, wrong=int(wrong),
                   errors=sum(o['result'] == 'error' for o in report['observations'].values()),
                   protocol_errors=len(protocol_errors))
    (out / 'metrics.json').write_text(json.dumps(metrics) + '\n')
    Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics) + '\n')
    return int(bool(metrics['wrong'] or metrics['errors'] or metrics['protocol_errors']))


if __name__ == '__main__':
    raise SystemExit(main())
