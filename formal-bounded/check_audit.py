"""Validate the full project's theorem coverage and Lean-produced axiom audit.

Kernel dependency checking is authoritative; the source scan adds guardrails.
This does not infer theorem semantics; inspect the explicit final statements.
"""
from pathlib import Path
import re
import sys

import json
MODULES = tuple(json.loads(Path('proof_modules.json').read_text()))


def uncomment(text):
    # Lean comments nest. Preserve newlines for anchored declaration matching.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i]); i += 1
    if depth:
        raise SystemExit('Unterminated source comment')
    return ''.join(out)


def declared_theorems():
    names = set()
    for module in MODULES:
        source = uncomment(Path(module + '.lean').read_text())
        for pattern in (r'\bsorry\b', r'\badmit\b', r'\bnative_decide\b',
                        r'^\s*(?:axiom|constant)\s'):
            if re.search(pattern, source, re.M):
                raise SystemExit(f'{module}: forbidden construct {pattern}')
        scopes = []
        for line in source.splitlines():
            m = re.match(r'\s*(namespace|section)\b\s*(\S*)', line)
            if m:
                scopes.append((m[1], m[2])); continue
            m = re.match(r'\s*end(?:\s+(\S+))?\s*$', line)
            if m:
                if not scopes:
                    raise SystemExit(f'{module}: unmatched end')
                scopes.pop(); continue
            m = re.match(r'\s*(?:@\[[^]]*\]\s*)?(?:theorem|lemma)\s+(\w+)', line)
            if m:
                name = '.'.join([n for kind, n in scopes if kind == 'namespace'] + [m[1]])
                if name in names:
                    raise SystemExit(f'Duplicate theorem {name}')
                names.add(name)
        if scopes:
            raise SystemExit(f'{module}: unclosed namespace/section')
    return names


theorems = declared_theorems()
if '--generate' in sys.argv:
    Path('VerificationAudit.lean').write_text(
        '\n'.join('import ' + m for m in MODULES) + '\n\n' +
        '\n'.join('#print axioms ' + n for n in sorted(theorems)) + '\n')
    print(f'Generated audit for {len(theorems)} theorems.')
    raise SystemExit(0)
commands = set(re.findall(r'^#print axioms (\S+)', Path('VerificationAudit.lean').read_text(), re.M))
if theorems != commands:
    raise SystemExit(f'Audit coverage mismatch: missing {theorems-commands}, extra {commands-theorems}')
log = Path(sys.argv[1] if len(sys.argv) > 1 else 'verification.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
seen = set()
for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    unexpected = set(filter(None, (x.strip() for x in deps.split(',')))) - allowed
    if unexpected:
        raise SystemExit(f'{name}: unexpected dependencies {unexpected}')
    seen.add(name)
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", log))
if seen != theorems:
    raise SystemExit(f'Incomplete checker output; missing: {theorems-seen}; extra: {seen-theorems}')
print(f'PASS: {len(theorems)} theorems checked across {len(MODULES)} modules; only standard Lean foundations.')
print('See README.md and the root FORMAL_VERIFICATION.md for semantic coverage.')
