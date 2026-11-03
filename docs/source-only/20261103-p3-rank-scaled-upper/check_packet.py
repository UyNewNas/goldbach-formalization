"""Exact-rational domain checks and source inventory; NOT Lean validation.

Run with Python 3.10+ from any working directory. No network or compilation
is invoked. The tests do not execute Lean or prove Python/Lean correspondence.
"""
from __future__ import annotations
import hashlib
import json
import re
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i]); i += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(out)


def inventory() -> list[dict]:
    result = []
    banned = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|#eval')
    for path in sorted(ROOT.glob('P2*.lean')):
        raw = path.read_bytes()
        text = raw.decode('utf-8')
        clean = strip_comments(text)
        matches = banned.findall(clean)
        if matches:
            raise AssertionError(f'{path.name}: forbidden forms {matches}')
        stack = []
        for ch in clean:
            if ch in '([{': stack.append(ch)
            elif ch in ')]}':
                if not stack or stack.pop() != {')':'(',']':'[','}':'{'}[ch]:
                    raise AssertionError(f'{path.name}: unmatched delimiter {ch}')
        if stack: raise AssertionError(f'{path.name}: unclosed delimiter')
        declarations = []
        for n, line in enumerate(text.splitlines(), 1):
            m = re.match(r'(private )?(def|theorem) ([A-Za-z_][A-Za-z0-9_]*)', line)
            if m:
                declarations.append({'name':m[3], 'kind':m[2], 'private':bool(m[1]), 'line':n})
        result.append({
            'path':path.name, 'bytes':len(raw), 'lines':len(text.splitlines()),
            'sha256':hashlib.sha256(raw).hexdigest(),
            'git_blob_sha':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
            'direct_imports':re.findall(r'^import (\S+)', text, re.M),
            'declarations':declarations, 'forbidden_scan':'NO_MATCH',
            'compiled':False, 'kernel_verified':False,
        })
    return result


def domain_checks() -> dict:
    r, emax, kmax = F(19,96), F(1,1000), F(1,100)
    target = (1-kmax)*F(9,20)
    caps = {3:F(37,50), 4:F(14,25)}
    margins = {str(k):str(target-nu*(k*r+emax)) for k,nu in caps.items()}
    assert all(F(v) > 0 for v in margins.values())
    count = 0
    for rank, cap in caps.items():
        for ni in range(101):
            nu = cap*F(ni,100)
            for ei in range(11):
                eps = emax*F(ei,10)
                for ki in range(11):
                    kappa = kmax*F(ki,10)
                    assert nu*(rank*r+eps) <= (1-kappa)*F(9,20)
                    count += 1
    scaled = 0
    for rank in range(65):
        cap = F(1) if rank <= 2 else F(2,rank)
        for ni in range(21):
            nu = cap*F(ni,20)
            assert nu*rank <= 2
            assert nu*(rank*r+emax) <= target
            scaled += 1
    # These larger nu values FAIL the sufficient complete-level inequality
    # at the allowed maximal kappa/epsilon. This is not a counterexample to PP.
    assert F(3,4)*(3*r+emax) > target
    assert F(57,100)*(4*r+emax) > target
    return {'rank3_rank4_cases':count, 'scaled_rank_cases':scaled,
            'out_of_range_controls':2, 'exact_worst_case_slack':margins}


def main() -> None:
    inv = inventory()
    checks = {'source_files':len(inv), 'source_lines':sum(x['lines'] for x in inv),
              'declarations':sum(len(x['declarations']) for x in inv),
              'domains':domain_checks(), 'status':'PASS',
              'compiler_invoked':False, 'kernel_replay':False,
              'analytic_estimates_tested':False, 'python_lean_correspondence':False}
    (ROOT/'INVENTORY.json').write_text(json.dumps(inv,ensure_ascii=False,separators=(',',':'))+'\n')
    (ROOT/'CHECKS.json').write_text(json.dumps(checks,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(checks,ensure_ascii=False,indent=2))

if __name__ == '__main__':
    main()
