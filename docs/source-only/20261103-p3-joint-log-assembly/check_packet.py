"""Source inventory and independent scalar regression. This is NOT Lean verification.

Run: python check_packet.py
Only this packet is read. No repository producer, build, network or CI is used.
The numerical checks use continuous upper caps, not actual project certificates.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import mpmath as mp

ROOT = Path(__file__).resolve().parent

def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
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
        raise ValueError('Unclosed Lean comment')
    return ''.join(out)

proofs = []
for file in sorted(ROOT.glob('P2*.lean')):
    data = file.read_bytes()
    text = data.decode('utf-8')
    clean = strip_comments(text)
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|#(?:eval|reduce)', clean)
    if forbidden:
        raise AssertionError((file.name, forbidden))
    stack = []
    pairs = {')': '(', ']': '[', '}': '{'}
    for ch in clean:
        if ch in '([{': stack.append(ch)
        elif ch in pairs:
            if not stack or stack.pop() != pairs[ch]:
                raise AssertionError(('delimiter mismatch', file.name))
    if stack: raise AssertionError(('unclosed delimiter', file.name))
    decls = [{'name': m.group(2), 'kind': m.group(1),
              'line': text[:m.start()].count('\n')+1}
             for m in re.finditer(r'^(?:private )?(def|theorem|abbrev)\s+(\w+)', text, re.M)]
    proofs.append({'name': file.name, 'bytes': len(data), 'lines': len(text.splitlines()),
                   'sha256': hashlib.sha256(data).hexdigest(),
                   'git_blob_sha': hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),
                   'imports': re.findall(r'^import (.+)$', text, re.M),
                   'declarations': decls})

orders = 0
for A in range(21):
    for J in range(101):
        H = A+J+4
        S = A+J+2*H+3
        assert S-(J+2*H+2) == A+1
        assert H-(J+3) == A+1
        assert H-(J+1) == A+3
        for B in (1, 5, 31):
            row = A+2*(B+1)
            assert row-2*(B+1) == A
        orders += 1

mp.mp.dps = 90
log2 = mp.log(2)
g = 2+abs(log2)
cls = 18+4/log2
cd = 1+1/log2
eta = mp.mpf(34)/1135
cases, max_ratio = 0, mp.mpf(0)
for A in (0, 1, 5, 12):
    for tail in (0, 1, 3, 6):
        exponent = (tail+3)**2-1
        for J in (exponent, exponent+7):
            H = A+J+4
            S = A+J+2*H+3
            t = mp.mpf(2)  # log x; no huge integer x is constructed.
            while H*mp.log(t) > (eta/2)*t:
                t *= 2
            assert H*mp.log(t) <= t/20
            b0 = int(mp.ceil(H*mp.log(t)/log2))
            T = mp.power(2, b0)
            assert mp.power(t,H) <= T*(1+mp.mpf('1e-80'))
            assert T <= 2*mp.power(t,H)*(1+mp.mpf('1e-80'))
            for r in (eta, mp.mpf('0.5'), 1-eta):
                # Supremum caps P=2M, R=2V, Q=x^(9/20); floor caps are smaller.
                beta_log = 1+log2+(1-r)*t
                depth = int(mp.floor((log2+r*t)/log2))+1
                ell = 1+mp.mpf(9)*t/20
                energy_over_h_sqrtx = 2*mp.power(beta_log, mp.mpf(exponent)/2)
                phi_over_sqrtx = (16*ell/T +
                    8*(cls+1)*cd*mp.sqrt(2)*
                    (mp.exp(-r*t/2)+mp.exp(-(1-r)*t/2))*ell**3 +
                    64*cls*mp.exp(-t/20)*ell)
                for C in (mp.mpf('0.1'), mp.mpf(3)):
                    low_over_hx = 2*C*mp.power(beta_log,tail+2)*T**2*ell**2/mp.power(t,S)
                    high_over_hx = energy_over_h_sqrtx*phi_over_sqrtx
                    lhs_normalized = 2*depth*(low_over_hx+high_over_hx)*mp.power(t,A)
                    hc = 2*g**J*(64+256*(cls+1)*cd+128*cls)
                    rhs_normalized = 2*cd*g*(32*C*g**J+hc)
                    ratio = lhs_normalized/rhs_normalized
                    assert ratio <= 1+mp.mpf('1e-70'), (A,J,tail,r,C,ratio)
                    max_ratio = max(max_ratio, ratio)
                    cases += 1

report = {'proof_files': len(proofs), 'proof_lines': sum(p['lines'] for p in proofs),
          'declarations': sum(len(p['declarations']) for p in proofs),
          'forbidden_form_scan': 'NO_MATCH', 'delimiter_scan': 'PASS',
          'exponent_identity_cases': orders, 'scalar_regression_cases': cases,
          'scalar_max_bound_ratio': mp.nstr(max_ratio, 12),
          'lean_executed': False, 'kernel_verified': False,
          'repository_producer_executed': False, 'ci_dispatched': False,
          'independent_mathematical_review': False}
(ROOT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'INVENTORY.json').write_text(json.dumps(proofs,indent=2)+'\n')
print(json.dumps(report,indent=2))
