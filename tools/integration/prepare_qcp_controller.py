#!/usr/bin/env python3
"""Create a separately frozen QCP controller that retains admitted auto VCs.

The original pinned QCP checkout is untouched. Its native symexec, C inputs,
base libraries and logical paths are selected by --main-root at invocation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil


def prepare(qcp, output):
    source = qcp / '.agents/scripts/verification-orchestrator/symexec_tooling.py'
    text = source.read_text()
    marker = '    snapshots = _generated_artifact_snapshots(plan, output)\n    if returncode == 0:\n'
    if text.count(marker) != 1:
        raise ValueError('unsupported QCP generation boundary; no controller was created')
    hook = '''    if returncode == 0:
        from qcp_proof_promotion import promote_generated_bundle
        promote_generated_bundle(output / plan["target_files"]["proof_auto_file"],
                                 output / plan["target_files"]["proof_manual_file"])
'''
    output.mkdir(parents=True, exist_ok=False)
    shutil.copytree(qcp / '.agents', output / '.agents',
                    ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    target = output / '.agents/scripts/verification-orchestrator'
    (target / 'symexec_tooling.py').write_text(text.replace(marker, hook + marker))
    shutil.copy2(Path(__file__).with_name('qcp_proof_promotion.py'), target / 'qcp_proof_promotion.py')
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    manifest = dict(schema=1, upstream_root=str(qcp), upstream_symexec_tooling_sha256=sha(source),
                    preparation_tool_sha256=sha(Path(__file__)),
                    transformation='promote every admitted auto witness into the manual proof obligations before validation/publication; replay uses the same transformation',
                    files={str(p.relative_to(output)):sha(p) for p in sorted(output.rglob('*')) if p.is_file()})
    (output / 'controller-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--qcp', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    manifest = prepare(a.qcp.resolve(strict=True), a.output.resolve())
    print(json.dumps(dict(files=len(manifest['files']), controller=str(a.output / '.agents/scripts/verification-orchestrator/controller.py'))))


if __name__ == '__main__':
    main()
