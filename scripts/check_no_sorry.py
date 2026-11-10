"""Forbidden-token scan (comments stripped) over the import closure of given modules.
Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0. Author: Benjamin Stanley Frohman.
Usage: python3 scripts/check_no_sorry.py Module.A Module.B ...
"""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
BAD = re.compile(r'(?<![A-Za-z0-9_.])(sorry|admit|native_decide)(?![A-Za-z0-9_])|^\s*(private\s+)?axiom\s', re.M)

def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth == 0 and src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        if depth == 0:
            out.append(src[i])
        elif src[i] == '\n':
            out.append('\n')
        i += 1
    return ''.join(out)

seen, todo, bad = set(), list(sys.argv[1:]), []
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m)
    f = ROOT / (m.replace('.', '/') + '.lean')
    if not f.exists(): continue          # Mathlib / external
    code = strip(f.read_text())
    todo += re.findall(r'^(?:public\s+)?import\s+(\S+)', code, re.M)
    for k, line in enumerate(code.splitlines(), 1):
        if BAD.search(line):
            bad.append(f'{f.relative_to(ROOT)}:{k}: {line.strip()}')
local = sorted(x for x in seen if (ROOT / (x.replace('.', '/') + '.lean')).exists())
print('scanned', len(local), 'project modules:', ', '.join(local))
if bad:
    print('\n'.join(bad)); sys.exit('FORBIDDEN TOKEN in code')
print('PASS: no sorry / admit / native_decide / axiom declarations (comments excluded)')
