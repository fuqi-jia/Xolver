#!/usr/bin/env python3
"""Audit QCP program counts against complete witnesses and canonical final-check.

This consumes a real controller result; it is not a Rocq checker. The stage
record must authenticate that result against its ExperimentOS run evidence.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp_proof_promotion import IDENTIFIER, token_mask

FIELD = re.compile(r'\bAxiom\s+(' + IDENTIFIER + r')\s*:\s*(' + IDENTIFIER + r')\s*\.')
LEMMA = re.compile(r'\bLemma\s+(' + IDENTIFIER + r')\s*:\s*(' + IDENTIFIER + r')\s*\.')
END = re.compile(r'(?<![\w.])(Qed|Defined|Admitted|Abort)\s*\.')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assess(goal, proofs, final_check, backend_reports=(), *, state_path=None):
    errors = []
    text = token_mask(goal.read_text())
    interface = re.search(r'\bModule\s+Type\s+VC_Correct\s*\.(.*?)\bEnd\s+VC_Correct\s*\.', text, re.S)
    expected = {}
    if interface:
        expected = dict(FIELD.findall(interface[1]))
        if len(expected) != len(re.findall(r'\bAxiom\b', interface[1])):
            errors.append('unsupported or duplicate VC interface field')
    if not expected:
        errors.append('no complete named VC interface')
    completed = {}
    completed_blocks = {}
    proof_hashes = {}
    for path in proofs:
        proof_hashes[str(path)] = sha(path)
        masked = token_mask(path.read_text())
        if re.search(r'\b(Admitted|Axiom|Parameter|Conjecture|Hypothesis)\b', masked):
            errors.append('unchecked assumption in proof module: ' + str(path))
        for match in LEMMA.finditer(masked):
            end = END.search(masked, match.end())
            if end and end[1] in ('Qed', 'Defined'):
                if match[1] in completed:
                    errors.append('duplicate witness: ' + match[1])
                completed[match[1]] = match[2]
                completed_blocks[match[1]] = masked[match.start():end.end()]
    for name, statement in expected.items():
        if completed.get(name) != statement:
            errors.append('missing complete witness or mismatched type: ' + name)
    record = json.loads(final_check.read_text())
    command = record.get('invocation', {}).get('argv', [])
    result = record.get('result', {})
    if not (record.get('returncode') == 0 and 'final-check' in command and
            record.get('cpu_ids') and result.get('status') == 'passed' and
            result.get('phase') == 'done' and not result.get('errors')):
        errors.append('successful canonical leased final-check required')
    state = json.loads(state_path.read_text()) if state_path else {}
    run = command[command.index('--run')+1] if '--run' in command else None
    if not (state.get('phase') == 'done' and run == state.get('run_id') and
            state.get('final_check', {}).get('status') == 'passed'):
        errors.append('completed canonical state must match the final-check run')
    root = Path(state.get('main_root', '.'))
    targets = state.get('target_files', {})
    if (root / targets.get('goal_file', '')).resolve() != goal.resolve():
        errors.append('goal path does not match the checked canonical case')
    expected_proofs = {(root / targets.get(k, '')).resolve() for k in ['proof_auto_file', 'proof_manual_file']}
    if expected_proofs != {p.resolve() for p in proofs}:
        errors.append('proof paths do not match the checked canonical case')
    backend_errors, discharged, auxiliary, queries, identities = [], set(), set(), [], set()
    for path in backend_reports:
        report = json.loads(path.read_text())
        identities.add((report['backend'], report['binary']['sha256']))
        timeout = report.get('timeout')
        finite = lambda value: (isinstance(value, (int, float)) and
                                not isinstance(value, bool) and math.isfinite(value))
        budget_valid = finite(timeout) and 0 < timeout <= 60
        if not budget_valid or report.get('memory_bytes') != 16 * 1024**3:
            backend_errors.append('valid per-query wall and memory budgets required')
        if report.get('protocol_errors'):
            backend_errors.append('backend wall budget overrun')
        if report['source_sha256'] != sha(goal):
            backend_errors.append('backend used a different original goal hash')
        for row in report['rows']:
            queries.extend(row['queries'])
            for query in row['queries']:
                seconds = query.get('seconds')
                if (not finite(seconds) or seconds < 0 or not budget_valid or
                        seconds > timeout or query.get('timed_out') or query.get('budget_overrun')):
                    backend_errors.append('backend query lacks an in-budget decision: ' + row['name'])
            if row['status'] == 'proof-candidate' and row['queries'] and all(q['result'] == 'unsat' for q in row['queries']):
                candidate = Path(row['candidate'])
                if not candidate.is_file() or sha(candidate) != row['candidate_sha256']:
                    backend_errors.append('proof candidate changed: ' + row['name'])
                else:
                    cmask = token_mask(candidate.read_text())
                    tokens = lambda value: re.findall(IDENTIFIER + r'|[0-9]+|[^\s]', value)
                    if (completed.get(row['lemma']) != row['name'] or
                            tokens(cmask) != tokens(completed_blocks.get(row['lemma'], ''))):
                        backend_errors.append('checked proof differs from backend candidate: ' + row['name'])
                    elif expected.get(row['lemma']) == row['name']:
                        discharged.add(row['name'])
                    else:
                        # Generated split statements also have complete checked
                        # witnesses, but cannot replace a top-level obligation.
                        auxiliary.add(row['name'])
    if len(identities) != 1:
        backend_errors.append('one frozen backend identity required')
    if not set(expected.values()).issubset(discharged):
        backend_errors.append('not every VC has a backend discharge candidate')
    verified = not errors
    return dict(schema=1, program_verified=verified,
                backend_qualified=verified and not backend_errors,
                programs=int(verified), verification_conditions=len(expected),
                verified_vcs=len(expected) if verified else 0,
                external_backend_queries=len(queries) if backend_reports else None,
                external_unsat=sum(q['result'] == 'unsat' for q in queries) if backend_reports else None,
                external_discharged_vcs=len(discharged),
                external_auxiliary_conditions=len(auxiliary),
                external_query_seconds=sum(q['seconds'] for q in queries) if backend_reports else None,
                external_query_scope='Supplied backend reports only; absent reports do not establish zero total calls',
                opaque_internal_qcp_queries=None,
                errors=errors, backend_errors=backend_errors,
                hashes=dict(goal=sha(goal), proofs=proof_hashes, final_check=sha(final_check),
                            state=sha(state_path) if state_path else None,
                            backend_reports={str(p):sha(p) for p in backend_reports}),
                evidence_boundary='Consumes an authenticated canonical controller final-check plus current proof coverage; does not replace Rocq. Pinned QCP frontend and libraries remain the common trusted base. This is qualification, not a timed program performance comparison.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--goal', type=Path, required=True)
    p.add_argument('--state', type=Path, required=True)
    p.add_argument('--proof', type=Path, action='append', required=True)
    p.add_argument('--final-check', type=Path, required=True)
    p.add_argument('--backend-report', type=Path, action='append', default=[])
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    report = assess(a.goal, a.proof, a.final_check, a.backend_report, state_path=a.state)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:report[k] for k in ['program_verified','backend_qualified','verification_conditions','external_backend_queries','errors']}))
    return int(not report['program_verified'])


if __name__ == '__main__':
    raise SystemExit(main())
