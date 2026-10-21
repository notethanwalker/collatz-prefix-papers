"""Check proof-hole policy and the Lean-produced dependency audit.
This audits the listed components; it does not certify either paper in full.
"""
from pathlib import Path
import re
import sys

source = Path('FormalComponents.lean').read_text()
audit_source = Path('VerificationAudit.lean').read_text()
for pattern in (r'\bsorry\b', r'\badmit\b', r'\bnative_decide\b',
                r'^\s*(?:axiom|constant)\s'):
    if re.search(pattern, source, re.M):
        raise SystemExit(f'Forbidden construct: {pattern}')
theorems = {'CollatzPrefix.' + n for n in re.findall(
    r'(?:^|\n)(?:@\[simp\] )?theorem (\w+)', source)}
commands = set(re.findall(r'^#print axioms (\S+)', audit_source, re.M))
if theorems != commands:
    raise SystemExit('Audit commands do not cover exactly the component theorems')
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
    raise SystemExit(f'Incomplete checker output; missing: {theorems-seen}')
print(f'PASS: {len(theorems)} component theorems checked; only standard Lean foundations.')
print('Both papers\' full main-theorem formalizations remain INCOMPLETE.')
