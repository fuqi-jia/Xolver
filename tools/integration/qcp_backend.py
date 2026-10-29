#!/usr/bin/env python3
"""Discharge assigned QCP arithmetic VCs with a selectable, untrusted SMT backend.

Emits proof candidates only. A group owner must check the original complete VC
through QCP's controller; UNSAT alone never establishes a verified C program.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import comments, export_goals
from tools.process_budget import run_with_budget

IDENTIFIER = r"[A-Za-z_][A-Za-z_0-9']*"
LEMMA = re.compile(r"\bLemma\s+(" + IDENTIFIER + r")\s*:\s*(" + IDENTIFIER + r")\s*\.")
MEMORY_BYTES = 16 * 1024**3


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pending_goals(manual):
    """Accept only direct named witnesses; never guess a complex Rocq type."""
    text = comments(manual.read_text())
    result = {}
    for match in LEMMA.finditer(text):
        rest = text[match.end():]
        finish = re.search(r"\b(Qed|Defined|Admitted|Abort)\s*\.", rest)
        if not finish:
            raise ValueError('unterminated proof: ' + match[1])
        if finish[1] in ('Admitted', 'Abort'):
            if match[2] in result:
                raise ValueError('duplicate pending goal: ' + match[2])
            result[match[2]] = match[1]
    return result


def leased_cpu():
    lease = os.environ.get('EOS_CPU_IDS', '')
    if not re.fullmatch(r'\d+', lease):
        raise ValueError('one ExperimentOS physical CPU lease is required')
    cpu = int(lease)
    if os.sched_getaffinity(0) != {cpu}:
        raise ValueError('process affinity must equal the ExperimentOS CPU lease')
    return cpu


def invoke(backend, binary, query, timeout, output):
    command = ([str(binary), 'solve', str(query), '--timeout', str(math.ceil(timeout))]
               if backend == 'xolver' else [str(binary), '-T:' + str(math.ceil(timeout)), str(query)])
    command = ['prlimit', '--as=' + str(MEMORY_BYTES),
               '--cpu=' + str(math.ceil(timeout) + 2) + ':' + str(math.ceil(timeout) + 3),
               '--', *command]
    controls = Path(__file__).resolve().parents[2] / 'src/base/controls.json'
    names = {c['name'] for c in json.loads(controls.read_text())['controls']}
    environment = {k: v for k, v in os.environ.items() if k not in names}
    stdout, stderr, timing = run_with_budget(command, timeout, environment)
    output.with_suffix('.stdout').write_bytes(stdout)
    output.with_suffix('.stderr').write_bytes(stderr)
    words = stdout.decode('utf-8', errors='replace').strip().splitlines()
    verdict = ('timeout' if timing['timed_out'] else words[0] if timing['returncode'] == 0 and
               len(words) == 1 and words[0] in ('sat', 'unsat', 'unknown') else 'error')
    return dict(command=command, result=verdict, **timing, query_sha256=sha256(query),
                stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                stderr_sha256=hashlib.sha256(stderr).hexdigest())


INTEGER_TACTIC = '''first [lia | nia | congruence |
    repeat (rewrite Z.gcd_0_r in * || rewrite Z.gcd_0_l in *);
    repeat match goal with
    | H : context [Z.gcd ?b (Z.rem ?a ?b)] |- _ =>
        rewrite (Z.gcd_comm b (Z.rem a b)) in H;
        rewrite (Z.gcd_rem a b ltac:(lia)) in H
    | |- context [Z.gcd ?b (Z.rem ?a ?b)] =>
        rewrite (Z.gcd_comm b (Z.rem a b));
        rewrite (Z.gcd_rem a b ltac:(lia))
    end;
    first [lia | nia | congruence |
      match goal with
      | |- context [Z.gcd ?a ?b] =>
          pose proof (Z.gcd_comm a b); congruence
      end] |
    match goal with
    | |- context [Z.rem ?a ?b] =>
        let Hr := fresh "Hremainder" in
        pose proof (Z.rem_bound_abs a b ltac:(lia)) as Hr;
        destruct (Z.abs_spec b) as [[? ?] | [? ?]];
        destruct (Z.abs_spec (Z.rem a b)) as [[? ?] | [? ?]]; lia
    end]'''


def proof_candidate(lemma, goal, derived=(), residual_heap=True, proof_path=()):
    # Both backends use identical proof reconstruction. These tactics must
    # reconstruct the whole original Rocq statement; no SMT result is an axiom.
    lines = [f'Lemma {lemma} : {goal}.', 'Proof.']
    for step in proof_path:
        if 'unfold' in step:
            lines.append(f"  unfold {step['unfold']}.")
        elif step.get('direction') == 'left':
            lines.append('  left.')
        elif step.get('direction') == 'consequent':
            lines.append('  intros _.')
    lines.append(f'  LLM_pre_process ltac:({INTEGER_TACTIC}).')
    for fact in derived:
        address, value = fact['address'], fact['value']
        lines.extend([
            f'  all: prop_apply_p (store_int_range ({address}) ({value}));',
            '    let H := fresh "HcellRange" in',
            '    Intros_p H;',
            f'    change (-2147483648 <= ({value}) <= 2147483647) in H;',
            '    destruct H.',
        ])
    if derived:
        if residual_heap:
            cells = '; '.join(f"cancel (({f['address']}) # Int |-> ({f['value']}))" for f in derived)
            lines.extend(['  all: split_pure_spatial.', f'  all: solve [{cells}',
                          f'    | split_pures; dump_pre_spatial; {INTEGER_TACTIC}].'])
        else:
            lines.append(f'  all: split_pures; dump_pre_spatial; {INTEGER_TACTIC}.')
    lines.append('Qed.')
    return '\n'.join(lines) + '\n'


def discharge(goals, manual, assigned, backend, binary, timeout, output):
    if not math.isfinite(timeout) or timeout <= 0 or timeout > 60:
        raise ValueError('each SMT invocation needs a positive budget of at most 60 seconds')
    cpu = leased_cpu()
    pending = pending_goals(manual)
    if not assigned or len(set(assigned)) != len(assigned) or any(x not in pending for x in assigned):
        raise ValueError('assignment must name distinct pending manual witnesses')
    binary = binary.resolve(strict=True)
    snapshots = [sha256(p) for p in (binary, goals, manual)]
    output.mkdir(parents=True, exist_ok=False)
    exported = export_goals(goals, output / 'queries')
    if exported['source_sha256'] != snapshots[1]:
        raise ValueError('goal source changed during export')
    by_name = {g['name']: g for g in exported['goals']}
    report = dict(schema=1, integration='pending-vc-discharge', backend=backend,
                  binary=dict(path=str(binary), sha256=snapshots[0]),
                  source_sha256=snapshots[1], manual_sha256=snapshots[2],
                  adapter_sha256=sha256(Path(__file__)),
                  exporter_sha256=sha256(Path(__file__).with_name('qcp.py')), cpu=cpu,
                  timeout=timeout, memory_bytes=MEMORY_BYTES, rows=[],
                  program_verified=False, verified_vcs=0, kernel_checks=0,
                  internal_qcp_smt_queries=None, protocol_errors=[])
    for index, name in enumerate(assigned):
        record = dict(name=name, lemma=pending[name], queries=[], status='unsupported')
        report['rows'].append(record)
        if by_name.get(name, {}).get('status') != 'exported':
            record['reason'] = by_name.get(name, {}).get('reason', 'goal definition absent')
            continue
        queries = [q for q in exported['queries'] if q['name'] == name]
        if not queries:
            record['reason'] = 'no supported arithmetic conditions'
            continue
        for number, query in enumerate(queries):
            path = output / 'queries' / query['file']
            if sha256(path) != query['query_sha256']:
                raise ValueError('exported query changed')
            record['queries'].append(invoke(backend, binary, path, timeout,
                                            output / f'vc-{index}-query-{number}'))
            record['queries'][-1]['integer_function_facts'] = query.get('integer_function_facts', [])
            record['queries'][-1]['proof_path'] = query.get('proof_path', [])
            if record['queries'][-1].get('budget_overrun'):
                report['protocol_errors'].append(dict(goal=name, query=number,
                    seconds=record['queries'][-1]['seconds']))
        if all(q['result'] == 'unsat' for q in record['queries']):
            candidate = output / f'vc-{index}-candidate.v'
            candidate.write_text(proof_candidate(pending[name], name,
                                 by_name[name].get('derived_assumptions', ()),
                                 by_name[name].get('residual_heap', False),
                                 by_name[name].get('proof_path', ())))
            record.update(status='proof-candidate', candidate=str(candidate),
                          candidate_sha256=sha256(candidate), kernel_checked=False)
        else:
            record['status'] = 'unproved'
            record['reason'] = 'SAT/unknown/timeout/error on a projection does not refute the C program'
    # Freeze bytes after execution too; executable/source mutation invalidates evidence.
    if sha256(binary) != report['binary']['sha256'] or sha256(goals) != report['source_sha256'] or sha256(manual) != report['manual_sha256']:
        raise ValueError('input or executable changed during discharge')
    report['backend_invocations'] = sum(len(r['queries']) for r in report['rows'])
    report['proof_candidates'] = sum(r['status'] == 'proof-candidate' for r in report['rows'])
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--goals', required=True, type=Path)
    p.add_argument('--manual', required=True, type=Path)
    p.add_argument('--assigned', action='append', required=True)
    p.add_argument('--backend', choices=('xolver', 'z3'), required=True)
    p.add_argument('--binary', required=True, type=Path)
    p.add_argument('--timeout', type=float, default=60)
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    report = discharge(a.goals.resolve(strict=True), a.manual.resolve(strict=True),
                       a.assigned, a.backend, a.binary, a.timeout, a.output.resolve())
    print(json.dumps({k: report[k] for k in ('backend', 'backend_invocations', 'proof_candidates',
                                           'verified_vcs', 'program_verified')}))
    return int(bool(report['protocol_errors']) or
               any(q['result'] == 'error' for r in report['rows'] for q in r['queries']))


if __name__ == '__main__':
    raise SystemExit(main())
