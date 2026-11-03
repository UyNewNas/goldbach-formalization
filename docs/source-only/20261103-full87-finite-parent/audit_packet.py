#!/usr/bin/env python3
"""Deterministic source hygiene and rational toy checks; NOT a Lean checker.

No repository numerical fixture is loaded. Fraction experiments check only
this packet's scalar formulas, not proof elaboration or original source data.
"""
from __future__ import annotations
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_comments_strings(text: str) -> str:
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        c = text[i]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            if c == '\\':
                i += 2
            elif c == '"':
                string = False
                i += 1
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif c == '"':
            string = True
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


def rounded(n: int, x: F) -> F:
    x = max(F(0), min(CAP, x))
    scaled = (n + 1) * x
    return max(F(0), F(scaled.numerator // scaled.denominator - 1, n + 1))


def protect(n: int, seed: F, x: F) -> F:
    return max(seed, rounded(n, x))


def main() -> None:
    files = []
    declarations = set()
    for path in sorted(ROOT.glob('*.lean')):
        raw = path.read_bytes()
        text = raw.decode('utf-8')
        code = strip_comments_strings(text)
        forbidden = re.findall(r'(?<![\w\'])\b(?:sorry|admit|axiom|unsafe|native_decide)\b', code)
        assert not forbidden, (path.name, forbidden)
        stack = []
        opening = '([{⟨'
        closing = ')]}⟩'
        for ch in code:
            if ch in opening:
                stack.append(ch)
            elif ch in closing:
                assert stack and stack.pop() == opening[closing.index(ch)], path.name
        assert not stack, path.name
        names = re.findall(r'^(?:theorem|def|abbrev|structure)\s+(\w+)', code, re.M)
        for name in names:
            key = (path.stem, name)
            assert key not in declarations, key
            declarations.add(key)
        files.append({
            'file': path.name,
            'bytes': len(raw),
            'lines': len(text.splitlines()),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'git_blob_sha1': hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest(),
            'imports': re.findall(r'^import\s+(\S+)', code, re.M),
            'declarations': names,
            'forbidden_tokens': forbidden,
            'delimiter_scan': 'pass',
        })
    graph = {f['file'][:-5]: [m.rsplit('.', 1)[-1] for m in f['imports']]
             for f in files}
    done, visiting = set(), set()
    def visit(name: str) -> None:
        if name in done or name not in graph:
            return
        assert name not in visiting, 'new-module import cycle'
        visiting.add(name)
        for dep in graph[name]:
            visit(dep)
        visiting.remove(name)
        done.add(name)
    for name in graph:
        visit(name)
    checks = 0
    for n in range(24):
        grid = [F(k, 128) for k in range(-32, 161)] + [CAP]
        grid.sort()
        values = [rounded(n, x) for x in grid]
        assert values == sorted(values)
        for x in grid:
            a = rounded(n, x)
            assert a >= 0
            assert a * (n + 1) == int(a * (n + 1))
            assert 0 <= a * (n + 1) <= n
            if 0 <= x <= CAP:
                for seed in (F(0), x / 2, x):
                    h = F(1, n + 1)
                    assert x - 2 * h < protect(n, seed, x) <= x
                    assert seed <= protect(n, seed, x)
                    checks += 1
        physical = [CAP * F(k, 16) for k in range(17)]
        for j, x in enumerate(physical):
            for y in physical[j:]:
                seed = x / 3
                assert max(protect(n, seed, x), rounded(n, y)) == protect(n, seed, y)
                checks += 1
        # Hold the Boolean eligible set fixed. This is NOT a recomputed guard.
        for mask in range(32):
            candidates = [F(1, 4), F(1, 2), F(11, 20), F(3, 5), F(2, 3)]
            accepted = [v for i, v in enumerate(candidates) if mask & (1 << i)]
            seed, base = F(1, 5), F(1, 7)
            assert protect(n, base, max([seed] + accepted)) == max(
                [protect(n, base, seed)] + [protect(n, base, v) for v in accepted])
            checks += 1
    current, comparison, base, n = F(11, 20), F(27, 50), F(1, 2), 9
    finite = protect(n, base, current)
    assert not current <= comparison
    assert finite <= comparison
    report = {
        'scope': 'source hygiene and finite rational toy examples ONLY',
        'lean_compiled': False,
        'kernel_replayed': False,
        'independent_review': False,
        'transitive_axioms_checked': False,
        'original_numeric_fixture_loaded': False,
        'new_module_graph_acyclic': True,
        'rational_assertion_groups': checks,
        'unsafe_guard_recomputation_toy': {
            'raw_current': str(current), 'comparison': str(comparison),
            'exact_seed': str(base), 'rounding_index': n,
            'finite_current': str(finite), 'raw_guard': False, 'recomputed_guard': True,
            'meaning': 'toy obstruction only; NOT an original-source or manuscript counterexample',
        },
        'files': files,
    }
    (ROOT / 'STATIC_QA.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'lean_files': len(files), 'declarations': len(declarations),
                      'lean_lines': sum(f['lines'] for f in files),
                      'rational_assertion_groups': checks, 'static_pass': True}))


if __name__ == '__main__':
    main()
