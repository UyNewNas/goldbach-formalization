"""Exact finite algebra regressions and byte inventory; NOT Lean validation.

Run with Python 3.10+ from any directory. It writes CHECKS.json and
INVENTORY.json next to this script. It does not invoke Lean, modify prior
packets, execute source producers, or access a network.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import random
import re

ROOT = Path(__file__).resolve().parent
PROOFS = [
    'P2GammaSelectedPhysicalTheta.lean',
    'P2GammaSelectedRelativeLogSaving.lean',
    'P2GammaRootFiberRelative.lean',
]


def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            ch = text[i]
            out.append(ch if depth == 0 or ch == '\n' else ' ')
            i += 1
    if depth:
        raise AssertionError('Unclosed Lean block comment')
    return ''.join(out)


def inventory() -> list[dict]:
    records = []
    for name in PROOFS + ['VERIFY.lean']:
        raw = (ROOT / name).read_bytes()
        text = raw.decode('utf-8')
        clean = strip_comments(text)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|#(?:eval|reduce)\b', clean), name
        stack = []
        pairs = {')': '(', ']': '[', '}': '{'}
        for ch in clean:
            if ch in '([{': stack.append(ch)
            if ch in ')]}':
                assert stack and stack.pop() == pairs[ch], name
        assert not stack, name
        decls = []
        for n, line in enumerate(clean.splitlines(), 1):
            m = re.match(r'(?:(private)\s+)?(def|abbrev|theorem|lemma)\s+(\w+)', line)
            if m:
                decls.append({'name': m[3], 'kind': m[2], 'line': n, 'private': bool(m[1])})
        records.append({
            'path': name, 'bytes': len(raw), 'lines': len(text.splitlines()),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'git_blob_sha': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'imports': re.findall(r'^import\s+(\S+)', text, re.M),
            'declarations': decls, 'forbidden_scan': 'NO_MATCH',
            'compiled': False, 'kernel_verified': False,
        })
    return records


def regressions() -> dict:
    rng = random.Random(20261103)
    U = [(3, 5), (5, 3), (3, 7), (7, 3), (5, 5), (11, 13), (13, 11)]
    counts = defaultdict(int)
    for _ in range(600):
        S = [t for t in U if rng.randrange(2)]
        sigma = {t: F(rng.randrange(8), rng.randrange(1, 10)) for t in U}
        test = {t: F(rng.randrange(-20, 21), rng.randrange(1, 9)) for t in U}
        a = F(rng.randrange(1, 30), rng.randrange(1, 20))
        selected = sum((sigma[t] * test[t] for t in S), F(0))
        masked = sum(((sigma[t] if t in S else 0) * test[t] for t in U), F(0))
        assert selected == masked
        assert selected + sum((sigma[t] * test[t] for t in U if t not in S), F(0)) == sum((sigma[t]*test[t] for t in U), F(0))
        assert selected == a * sum(((sigma[t]/a)*test[t] for t in S), F(0))
        counts['masked_partition_homogeneity_cases'] += 1
        push = defaultdict(F)
        for t in S: push[t[0]*t[1]] += sigma[t]
        mass = sum((sigma[t]/(t[0]*t[1]) for t in S), F(0))
        assert mass == sum((w/d for d, w in push.items()), F(0))
        assert (mass == 0) == all(sigma[t] == 0 for t in S)
        counts['product_collision_mass_cases'] += 1
        # Toy root table: not the repository's rootQ computation.
        N, Q = 1000, F(200)
        roots = {t: F(rng.choice([100, 200, 500])) for t in U}
        keep = {t: bool(rng.randrange(2)) for t in U}
        fibre = [t for t in U if keep[t] and roots[t] == Q and 1 < Q/(t[0]*t[1]) <= N]
        assert all(roots[t] == Q for t in fibre)
        assert sum((sigma[t]*(roots[t]+test[t]) for t in fibre), F(0)) == sum((sigma[t]*(Q+test[t]) for t in fibre), F(0))
        counts['toy_root_filter_cases'] += 1
    # Exact algebra: Uconst is an arbitrary positive symbolic stand-in,
    # not a numeric claim about the actual liuUniversalProduct.
    for A in range(9):
        for r in range(9):
            for height in [F(1,10**9), F(1), F(10**9)]:
                ell, N, uc, lam, eta = F(11,3), F(1000), F(3,5), F(2,7), F(1,13)
                massfloor = lam*height/ell**r
                mass = massfloor*F(5,4)
                theta_lower = 2*uc*N/ell**2 * mass
                err = eta*(2*uc)*lam*height*N/ell**(A+r+2)
                assert err <= eta*theta_lower/ell**A
                assert err == eta/ell**A * (2*uc*N/ell**2)*(lam*height/ell**r)
                counts['relative_budget_cases'] += 1
    # Negative control: positive Theta alone need not dominate an absolute
    # log-accuracy allowance. This is a logical scalar example, NOT an
    # arithmetic counterexample to the repository PP statement.
    ell, N, uc, lam, height, eta = map(F, [10, 1000000, 1, 1, 1, 1])
    mass = F(1, 101*103)
    theta = 2*uc*N/ell**2*mass
    err = eta*(2*uc)*lam*height*N/ell**2
    assert theta > 0 and mass < lam*height and err > eta*theta
    counts['positive_only_negative_controls'] = 1
    return dict(counts)


def main() -> None:
    inv = inventory()
    checks = {
        'scope': 'SOURCE_STATIC_AND_FINITE_ALGEBRA_ONLY',
        'proof_files': len(PROOFS),
        'proof_lines': sum(x['lines'] for x in inv if x['path'] in PROOFS),
        'proof_declarations': sum(len(x['declarations']) for x in inv if x['path'] in PROOFS),
        'regressions': regressions(),
        'status': 'PASS', 'lean_invoked': False, 'kernel_replay': False,
        'repository_producer_run': False, 'repository_finite_guard_run': False,
    }
    (ROOT/'INVENTORY.json').write_text(json.dumps(inv, separators=(',', ':'), ensure_ascii=False)+'\n', encoding='utf-8')
    (ROOT/'CHECKS.json').write_text(json.dumps(checks, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
    print(json.dumps(checks, indent=2))


if __name__ == '__main__':
    main()
