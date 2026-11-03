#!/usr/bin/env python3
"""Lexical checks and exact rational toy tests only; NOT a Lean checker.

No original NPY/BIN fixture, original numerical producer, literal-row
membership certificate, Lean compiler, or network connection is used.
Run in place; a failed assertion prevents a passing report from being saved.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import random
import re

ROOT = Path(__file__).resolve().parent
CAP = F(153, 256)


def strip_comments_strings(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    string = False
    while i < len(text):
        pair, c = text[i:i + 2], text[i]
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
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif c == '"':
            string = True
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


def blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def rounded(n: int, x: F) -> F:
    d = n + 1
    y = max(F(0), min(CAP, x))
    return max(F(0), F((d * y).__floor__() - 1, d))


def gates(t: tuple[F, ...], mask: int) -> list[F]:
    I = {i for i in range(len(t)) if mask >> i & 1}
    ans = [F(1, 2)]
    for j, tj in enumerate(t):
        ans.append(sum(t[:j], F(0)) + 2 * tj)
        ans.append(F(1, 2) if j in I else
                   sum((t[i] for i in I), F(0)) +
                   sum((t[i] for i in range(j) if i not in I), F(0)) + 2 * tj)
    return ans


def tent(s: F) -> F:
    return min((1 + s) / 2, F(57, 64) - 3 * s / 2)


def tests() -> dict:
    rng = random.Random(2026110311)
    counts = dict(conditional_strata=0, all_action_transport=0,
                  chronological_winner=0, endpoint_inheritance=0,
                  inactive_guard_preserved=0, omission_prototype=0,
                  strict_nonstrict_boundary=0)
    for _ in range(500):
        t = tuple(F(rng.randrange(1, 90), 1000) for _ in range(6))
        actions = []
        for _a in range(18):
            mask = rng.randrange(1, 64)
            upper = tent(sum((t[i] for i in range(6) if mask >> i & 1), F(0)))
            M = upper - F(rng.randrange(0, 30), 10000)
            gg = gates(t, mask)
            geometric = all(g < M for g in gg)
            # A further raw-parent guard is independent and may fail.
            actual = geometric and bool(rng.randrange(2))
            actions.append((mask, M, gg, geometric, actual, upper))
            if geometric and not actual:
                counts['inactive_guard_preserved'] += 1
        margins = [M - g for _, M, gg, geo, _, _ in actions if geo for g in gg]
        minimum = min([F(1)] + margins)
        assert minimum > 0
        s = max(0, (2 / minimum).__ceil__())
        delta = F(1, s + 1)
        n0 = (8 / delta).__ceil__()
        for n in (n0, n0 + 1, n0 + 117):
            h = F(1, n + 1)
            assert 4 * h < delta
            for _, M, gg, geo, actual, upper in actions:
                if geo:
                    assert all(g + delta <= M for g in gg)
                    val = rounded(n, M)
                    assert all(g + delta / 2 < val for g in gg)
                    assert val + h <= M <= upper
                    counts['all_action_transport'] += 1
                assert not actual or geo
        # Larger delta can fail only via an original active positive gate gap.
        for test_delta in (delta, minimum, 2 * minimum):
            safe = all(not geo or all(g + test_delta <= M for g in gg)
                       for _, M, gg, geo, _, _ in actions)
            if not safe:
                assert any(geo and any(0 < M - g < test_delta for g in gg)
                           for _, M, gg, geo, _, _ in actions)
            counts['conditional_strata'] += 1
    for case in range(1200):
        fifth = F(rng.randrange(510, 555), 1000)
        base = F(1, 2)
        current = fifth
        eligible_trace: list[tuple[str, int, F, F]] = []
        # Saved and eleven guards both use fifth, not the saved-stage output.
        for family in ('saved', 'eleven'):
            candidates = []
            for row in range(8):
                M = F(rng.randrange(520, 598), 1000)
                cmp = F(rng.randrange(510, 585), 1000)
                ok = fifth <= cmp < M
                if ok:
                    eligible_trace.append((family, row, fifth, M))
                    candidates.append(M)
            current = max([current] + candidates)
        for stage in range(8):
            prior = current
            candidates = []
            for row in range(5):
                M = F(rng.randrange(520, 598), 1000)
                cmp = F(rng.randrange(520, 595), 1000)
                history = F(rng.randrange(480, 600), 1000)
                ok = history < prior <= cmp < M
                if ok:
                    eligible_trace.append((f'later-{stage}', row, prior, M))
                    candidates.append(M)
            current = max([prior] + candidates)
        assert current == fifth or any(M == current for *_, M in eligible_trace)
        for n in (9, 31, 63, 255, 1023):
            parent5 = max(base, rounded(n, fifth))
            parent6 = max(parent5, rounded(n, current))
            if parent5 < parent6:
                winners = [a for a in eligible_trace if a[-1] == current]
                assert winners and parent6 == rounded(n, winners[0][-1])
                counts['chronological_winner'] += 1
            else:
                # No new-action witness is demanded on the inherited branch.
                assert parent6 == parent5
                counts['endpoint_inheritance'] += 1
    for s in range(1, 501):
        delta = F(1, s + 1)
        # Toy source (0,1), margin=t. Omitted volume=delta,
        # omitted integral for f(t)=t is delta^2/2. t=0 is inactive.
        assert 0 < delta <= F(1, 2)
        assert delta**2 / 2 <= delta
        assert F(1, s + 2) < delta
        counts['omission_prototype'] += 1
    raw, cmp, base = F(11, 20), F(27, 50), F(1, 2)
    assert not raw <= cmp and max(base, rounded(9, raw)) <= cmp
    assert not (raw < raw) and raw <= raw
    counts['strict_nonstrict_boundary'] += 3
    return dict(counts=counts, total_cases=sum(counts.values()),
                scope='Finite exact rational TOY cases only; no original source-data or Lean verification',
                raw_guard_boundary=dict(raw=str(raw), comparison=str(cmp),
                                        rounded=str(max(base, rounded(9, raw)))))


def main() -> None:
    files = []
    graph = {}
    names = {p.stem for p in ROOT.glob('*.lean')}
    for p in sorted(ROOT.glob('*.lean')):
        raw = p.read_bytes()
        text = raw.decode()
        code = strip_comments_strings(text)
        bad = re.findall(r'(?<![\w])(?:sorry|admit|axiom|unsafe|native_decide)(?![\w])|#(?:eval|reduce)', code)
        assert not bad, (p.name, bad)
        stack = []
        pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
        for char in code:
            if char in '([{⟨':
                stack.append(char)
            elif char in pairs:
                assert stack and stack.pop() == pairs[char], (p.name, char)
        assert not stack, (p.name, stack)
        imports = re.findall(r'^import\s+(\S+)', code, re.M)
        decl = re.findall(r'^(?:(?:private|protected|noncomputable)\s+)*(?:@\[[^\]]+\]\s*)?'
                          r'(def|theorem|lemma|abbrev|structure|inductive)\s+(\S+)', code, re.M)
        files.append(dict(path=p.name, bytes=len(raw), lines=len(text.splitlines()),
                          sha256=hashlib.sha256(raw).hexdigest(), git_blob_sha1=blob_sha(raw),
                          imports=imports, declarations_count=len(decl),
                          declarations=[name for _, name in decl]))
        graph[p.stem] = [i.rsplit('.', 1)[-1] for i in imports if i.rsplit('.', 1)[-1] in names]
    seen, active = set(), set()
    def visit(name: str) -> None:
        assert name not in active, ('cycle', name)
        if name in seen:
            return
        active.add(name)
        for dep in graph[name]:
            visit(dep)
        active.remove(name)
        seen.add(name)
    for name in graph:
        visit(name)
    report = dict(scope='Lexical hygiene, graph check and exact rational toy tests only',
                  lean_compiled=False, kernel_replayed=False, independent_review=False,
                  transitive_axioms_checked=False, original_archive_loaded=False,
                  numerical_producer_rerun=False, original_later_row_certificates_evaluated=False,
                  new_module_graph_acyclic=True, regression=tests(), files=files)
    (ROOT / 'STATIC_QA.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(dict(lean_files=len(files), lean_lines=sum(f['lines'] for f in files),
                          declarations=sum(f['declarations_count'] for f in files),
                          regression=report['regression']), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
