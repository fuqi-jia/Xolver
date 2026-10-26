"""Retain QCP auto-classified admitted witnesses as explicit proof obligations.

This module is copied into an isolated QCP controller implementation. Both
normal generation and final independent replay apply the same transformation.
"""
from pathlib import Path
import re

IDENTIFIER = r"[A-Za-z_][A-Za-z_0-9']*"
STUB = re.compile(r'\bLemma\s+(' + IDENTIFIER + r')\s*:\s*(' + IDENTIFIER +
                  r')\s*\.\s*Proof\s*\.\s*Admitted\s*\.')
DECLARATION = re.compile(r'\bLemma\s+(' + IDENTIFIER + r')\s*:')


def token_mask(text):
    """Mask nested comments and quoted strings while preserving byte offsets."""
    result = list(text)
    depth, quoted, i = 0, False, 0
    while i < len(text):
        if depth:
            if text[i:i+2] == '(*':
                result[i:i+2] = '  '; depth += 1; i += 2; continue
            if text[i:i+2] == '*)':
                result[i:i+2] = '  '; depth -= 1; i += 2; continue
            if text[i] != '\n': result[i] = ' '
        elif quoted:
            if text[i] == '"':
                if text[i:i+2] == '""':
                    result[i:i+2] = '  '; i += 2; continue
                quoted = False
            if text[i] != '\n': result[i] = ' '
        elif text[i:i+2] == '(*':
            result[i:i+2] = '  '; depth = 1; i += 2; continue
        elif text[i] == '"':
            quoted = True; result[i] = ' '
        i += 1
    if depth or quoted:
        raise ValueError('unterminated Rocq comment or string')
    return ''.join(result)


def promote_auto_text(auto, manual):
    masked = token_mask(auto)
    matches = list(STUB.finditer(masked))
    if len(matches) != len(re.findall(r'\bAdmitted\b', masked)):
        raise ValueError('unsupported admitted auto proof: retain it as unproved')
    if re.search(r'\b(Axiom|Parameter|Conjecture|Hypothesis)\b', masked):
        raise ValueError('auto file declares an unchecked assumption')
    names = [m[1] for m in matches]
    if len(names) != len(set(names)):
        raise ValueError('duplicate auto witness')
    manual_mask = token_mask(manual)
    if set(names) & set(DECLARATION.findall(manual_mask)):
        raise ValueError('auto/manual witness overlap requires explicit resolution')
    # Completed auto proofs must not depend on a moved admitted witness.
    remaining = masked
    for match in reversed(matches):
        remaining = remaining[:match.start()] + remaining[match.end():]
    if names and re.search(r'\b(?:' + '|'.join(map(re.escape, names)) + r')\b', remaining):
        raise ValueError('completed auto proof depends on an admitted witness')
    moved = '\n\n'.join(auto[m.start():m.end()] for m in matches)
    insertion = next(iter(DECLARATION.finditer(manual_mask)), None)
    position = insertion.start() if insertion else len(manual)
    new_manual = manual[:position] + ('\n' + moved + '\n\n' if moved else '') + manual[position:]
    new_auto = auto
    for match in reversed(matches):
        new_auto = new_auto[:match.start()] + new_auto[match.end():]
    return new_auto, new_manual, [{'lemma': m[1], 'goal': m[2]} for m in matches]


def promote_generated_bundle(auto_path, manual_path):
    auto_path, manual_path = Path(auto_path), Path(manual_path)
    if any(p.is_symlink() or not p.is_file() for p in (auto_path, manual_path)):
        raise ValueError('proof promotion requires ordinary generated files')
    auto, manual, moved = promote_auto_text(auto_path.read_text(), manual_path.read_text())
    if moved:
        # These are fresh controller staging files, not canonical proof edits.
        auto_path.write_text(auto, encoding='utf-8', newline='\n')
        manual_path.write_text(manual, encoding='utf-8', newline='\n')
    return moved
