#!/usr/bin/env python3
"""Static hygiene and exact-rational regression; NOT a Lean/kernel checker.

Run in this directory. No network, original fixture or numerical producer is
read. Toy action labels are not claimed to be original saved rows. Any failed
assertion aborts; a report is written only after all checks have succeeded.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib
import itertools
import json
import re

ROOT = Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_comments_strings(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2; out.extend('  ')
            elif text.startswith('-/', i):
                depth -= 1; i += 2; out.extend('  ')
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif in_string:
            if text[i] == '\\':
                out.extend('  '); i += 2
            elif text[i] == '"':
                in_string = False; out.append(' '); i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            in_string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    assert depth == 0 and not in_string, 'Unterminated comment or string'
    return ''.join(out)


def blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def lexical_inventory() -> list[dict]:
    files = sorted(ROOT.glob('*.lean'))
    assert files, 'No Lean files found'
    names = {p.stem for p in files}
    graph: dict[str, list[str]] = {}
    result = []
    for p in files:
        raw = p.read_bytes()
        code = strip_comments_strings(raw.decode())
        forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|#(?:eval|reduce)', code)
        assert not forbidden, (p.name, forbidden)
        stack: list[str] = []
        pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
        for ch in code:
            if ch in '([{⟨': stack.append(ch)
            elif ch in pairs:
                assert stack and stack.pop() == pairs[ch], (p.name, 'delimiter', ch)
        assert not stack, (p.name, 'unclosed delimiter')
        declarations = re.findall(r'(?m)^\s*(?:private\s+)?(?:def|theorem|lemma|abbrev|structure|inductive)\s+([^\s(:]+)', code)
        assert len(declarations) == len(set(declarations)), (p.name, 'duplicate declaration')
        imports = re.findall(r'(?m)^import\s+(\S+)', code)
        graph[p.stem] = [x.rsplit('.', 1)[-1] for x in imports if x.rsplit('.', 1)[-1] in names]
        result.append({'file': p.name, 'lines': len(raw.decode().splitlines()),
                       'declarations': declarations, 'imports': imports,
                       'sha256': hashlib.sha256(raw).hexdigest(), 'git_blob_sha1': blob_sha(raw)})
    seen: set[str] = set()
    active: set[str] = set()
    def visit(node: str) -> None:
        assert node not in active, ('import cycle', node)
        if node in seen: return
        active.add(node)
        for child in graph[node]: visit(child)
        active.remove(node); seen.add(node)
    for node in graph: visit(node)
    return result


def rounded(n: int, x: F) -> F:
    y = max(F(0), min(CAP, x))
    z = (n + 1) * y
    return max(F(0), F(z.numerator // z.denominator - 1, n + 1))


def run_tests() -> dict:
    counts = {'filtered_cap': 0, 'safe_stratum': 0, 'frozen_ancestor': 0,
              'signed_telescoping': 0, 'boundary_examples': 0}
    # Each raw action is modelled by an endpoint, its own gate set, a tent
    # upper bound and an INDEPENDENT ORIGINAL raw-guard bit.
    for n, seed, phase, bits in itertools.product(
            (5, 9, 19, 39, 79, 199), (F(1, 2), F(51, 100), F(13, 25)),
            range(1, 13), itertools.product((False, True), repeat=3)):
        h = F(1, n + 1)
        raw5 = seed + F(1, 100)
        finite5 = max(seed, rounded(n, raw5))
        acts = []
        for j in range(3):
            M = F(53 + ((phase + j * 3) % 7), 100)
            gates = (F(1, 2), M - F(1 + (phase % 5), 1000), M - F(j + 1, 100))
            acts.append((M, gates, M + F(1, 1000), bits[j]))
        raw6 = max([raw5] + [M for M, _, _, eligible in acts if eligible])
        old6 = max(finite5, rounded(n, raw6))
        accepted = [j for j, (M, gates, upper, eligible) in enumerate(acts)
                    if eligible and all(g < rounded(n, M) for g in gates)
                    and rounded(n, M) + h <= upper]
        new6 = max([finite5] + [rounded(n, acts[j][0]) for j in accepted])
        assert finite5 <= new6 <= old6
        assert all(acts[j][3] for j in accepted)
        if not accepted: assert new6 == finite5
        if new6 > finite5:
            witnesses = [j for j in accepted if rounded(n, acts[j][0]) == new6]
            assert witnesses
            for j in witnesses:
                M, gates, upper, eligible = acts[j]
                assert eligible and all(g < new6 for g in gates) and new6 + h <= upper
        counts['filtered_cap'] += 1
        # When the chosen common positive margin dominates 4h, the same
        # accepted action bank gives the original finite maximum.
        gaps = [M - g for M, gates, _, eligible in acts if eligible for g in gates]
        delta = min([F(1)] + gaps)
        if F(4) * h < delta:
            assert new6 == old6
            counts['safe_stratum'] += 1
    # Separate fine resolutions ensure non-vacuous safe-stratum tests.
    for n, a, b in itertools.product((999, 1999, 3999), range(52, 60), range(1, 5)):
        M, delta = F(a, 100), F(b, 1000)
        h = F(1, n + 1)
        if 4 * h < delta:
            Q = rounded(n, M)
            assert M - delta + delta / 2 < Q and Q + h <= M
            counts['safe_stratum'] += 1
    # Unsafe actual winner is removed, but a different OLD eligible and
    # licensed action can still improve fifth. No whole tuple is removed.
    n, base = 99, F(1, 2)
    assert rounded(n, F(29, 50)) == F(57, 100)
    assert not F(579, 1000) < rounded(n, F(29, 50))
    assert F(27, 50) < rounded(n, F(14, 25)) == F(11, 20)
    assert base < F(11, 20) < F(57, 100)
    counts['boundary_examples'] += 1
    # Raw false stays false even if an altered current would pass.
    raw, comparison, altered = F(11, 20), F(27, 50), F(1, 2)
    assert not raw <= comparison and altered <= comparison
    counts['boundary_examples'] += 1
    for n in (9, 99, 999):
        d = n + 1
        for k in (0, 1, 2, d // 2):
            x = F(k, d)
            if 0 <= x <= CAP:
                assert rounded(n, x) == max(F(0), F(k - 1, d))
                counts['boundary_examples'] += 1
    def ancestor(k: int, history: tuple[int, ...]) -> tuple[int, ...]:
        return history[max(0, len(history) - k):]
    for k, size, later in itertools.product((3, 4, 5, 6, 8), range(8, 25), range(15)):
        history = tuple(range(size))
        suffix = tuple(range(100, 100 + later))
        assert ancestor(k, suffix + history) == ancestor(k, history)
        counts['frozen_ancestor'] += 1
    # Algebra of the ledger, for arbitrary signed finite sums; NOT an
    # evaluator for the actual Lean signedTest or its arithmetic fixtures.
    for j in range(1, 2001):
        P5, P6, P8 = F((-1)**j * j, 7), F(j*j - 3*j, 11), F(5-j, 13)
        assert P8 - P5 == (P8 - P6) + (P6 - P5)
        counts['signed_telescoping'] += 1
    assert counts['safe_stratum'] > 0
    return {'counts': counts, 'total_cases': sum(counts.values()),
            'scope': 'exact rational TOY models only; not original data, Lean, or universal verification'}


def main() -> None:
    files = lexical_inventory()
    regression = run_tests()
    report = {'scope': 'static hygiene and exact-rational toy regression only',
              'lean_compiled': False, 'kernel_replayed': False,
              'transitive_axioms_checked': False, 'independent_review': False,
              'original_fixtures_loaded': False, 'numerical_producer_run': False,
              'new_module_graph_acyclic': True,
              'files': files, 'regression': regression}
    (ROOT / 'STATIC_QA.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'files': len(files), 'lines': sum(x['lines'] for x in files),
                      'declarations': sum(len(x['declarations']) for x in files),
                      'regression': regression}, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
