"""Run the Jacobi axiom audit and fail on any non-standard axiom.
Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0. Author: Benjamin Stanley Frohman.
"""
import re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
src = (ROOT/'scripts'/'JacobiAxiomAudit.lean').read_text()
expected = re.findall(r'^#print axioms (\S+)$', src, re.M)
run = subprocess.run(['lake', 'env', 'lean', 'scripts/JacobiAxiomAudit.lean'], cwd=ROOT,
                     text=True, capture_output=True)
out = run.stdout + run.stderr
lines = []
for line in out.splitlines():
    if line.startswith(' ') and lines:
        lines[-1] += ' ' + line.strip()
    else:
        lines.append(line)
print('\n'.join(lines))
if run.returncode != 0 or re.search(r'error|declaration uses', out):
    sys.exit('audit failed to elaborate')
entries = [l for l in lines if l.startswith("'")]
if len(entries) != len(expected):
    sys.exit(f'expected {len(expected)} axiom lines, saw {len(entries)}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, line in zip(expected, entries):
    if not line.startswith("'" + name + "'"):
        sys.exit('order mismatch: ' + line)
    if line.endswith('does not depend on any axioms'):
        continue
    m = re.search(r'depends on axioms: \[(.*)\]$', line)
    if not m or not set(m.group(1).split(', ')) <= allowed:
        sys.exit('NON-STANDARD AXIOM: ' + line)
print(f'PASS: {len(expected)} declarations, standard axioms only')
