# P1.4 — exact active full-q / PP licence cutoff with unpaid tail

Baseline **33604cdad255f547cb69679c1a80b49dc90a07e8**, source commit **b08af651b580d1987f11636a591fa90874e25ac9**, branch `chatgpt/p1-full87-active-q-tail-20261107`. Lean candidate `P4AOriginalFull87ActiveQTail.lean`: 167 lines, Git blob `97d133e1bfc02cb739a4d7b068e3ee174d7d6fbf`.

## Actual mathematical gain

The earlier signed singleton PP and sharp-density ledger was over the displayed `actualSmallRoughModuli (P false)` support. Such a display includes coefficients that can vanish. Requiring ALL displayed full-q to satisfy the permitted q cutoff was stronger than the legitimate signed coefficient licence, and may be false. This packet does not assert that bound.

With Q the frozen physical carrier, rho the SAME sign-attached beta coefficient, F any arithmetic test and X a natural cutoff, candidate Lean proof bodies establish the **exact** finite identity

    sum_{q in Q} rho(q) F(q)
      = sum_{0 <= q <= X} rho(q) F(q)
        + sum_{q in Q, q > X} rho(q) F(q).

The first sum uses the ORIGINAL globally zero-extended rho; it is not an unrelated replacement mask. Its proof invokes the existing `smallRoughRho_eq_zero_of_not_mem` outside Q. Thus no off-carrier density term is created.

A separate candidate establishes `|tail| <= sum_{q in Q, q > X} |F(q)|` using the previously proved `actualSmallRoughRho_abs_le_one`; this is an **unpaid** finite invoice, not a logarithmic saving.

More specifically, for a genuinely nonzero physical rho(q) with q>X, the EXISTING `actualSmallRoughRho_ne_zero_factors` supplies the original small a, rough b, sign-dependent beta factor and the true fixed rough coefficient, with `q=a*b`, `a<L`, `fixedRoughCoefficient(b) != 0`. New arithmetic then proves `X < L*b` as reals. This localizes every possible unlicensed high-q contribution to the actual rough parent/leaf branch; no arbitrary mask is added. One more candidate gives exact zero tail if the ORIGINAL active q, not the display, is proved <=X.

This does not prove that rough b is small, that all 87 dynamic parent branches meet the original theta, or that the signed PP is admissible. Those remain true yellow obligations. It does not double-count centre/endpoint invoices, change P(false), replace the original rho, remove occurrence multiplicities, change the hand-picked fixed manuscript, or pay either reserve.

## Checks

GitHub `b08af651b580d1987f11636a591fa90874e25ac9` fetched and re-read: blob `97d133e1bfc02cb739a4d7b068e3ee174d7d6fbf`, 167 source lines. Static forbidden escape scan (sorry/admit/native_decide/unsafe/axiom): none. Independent finite rational tests: 4,000 deterministic random cases of support and signed coefficients, cutoff split, one-bound tail and active-tail zeroing; all matched (505 cases with active cutoff), **not** original saved87 tests. No Lean, Lake, compiled imports, kernel replay, transitive axiom checking, independent review or saved87 certification. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**, zero formal verification credit. No CI, Codex, altered toolchain, external theorem implementation or reserve payment.

## Exact next task

Read the actual policy/leaf supplier and prove the real rough-factor bound `b < N^(theta-epsilon_beta)` on each NONZERO full87 leaf, including inherited branches; combine it with `a<L` and strict inequalities so that active q is within the permitted signed PP cutoff. If a branch remains above cutoff, retain and separately quantify its literal tail; do not silently drop it. Then specialize the original PP weight/support (Gevrey derivatives), pay primitive/endpoint/centre/sharp mean errors relative to H_N, and continue ordinary residual / filtered gains, saved87 and two independent reserves.