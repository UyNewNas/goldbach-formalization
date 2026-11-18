# P5.6 h34 — exact four-step W2-to-Q80 seed audit

Date: 2026-11-19 (Asia/Shanghai).
Incoming confirmed branch HEAD: `bcaef9ce95b3803a564d9d2eed58ebcb02a6f7cc`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean v4.33.0-rc1 / mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Mathematical source increment

The previous packet gave the exact two-table Q80 seed and reduced its full CLOSED-CELL base to the true frozen analytic F inequalities, with first-60 upper height `28131703822432420895412 / 2^80`. Those inequalities were not proved.

This new module checks the EXACT manuscript four-step benchmark `J_{n+1}=20249/1000000+(13/100)J_n`, `J_0=1/50`, proving in candidate Lean that `J_4=23273777353/1000000000000=0.023273777353>2327/100000`. It does not swap the adopted 80-bit seed for that unrounded number.

For an independent operator check it defines `actualW2Model` with the original seven-integral W2 `actualFeedback` in place of the model slope. Reusing `actualFeedback_eq_mul_lambda` and `lambda_exact_seven_logs`, it proves the **conditional** monotonic comparison `J_n <= actualW2Model n` for every n when the actual geometric coefficient `lambda >= 13/100`; hence the EXACT original Q80 seed is below the model's fourth iterate. The final theorem exposes the unchanged three singleton plus D5/D6/D7/D8 integrals as the precise source of that condition.

## Important remaining boundary

The coefficient inequality on those real integrals is NOT proved here. Neither is the analytic payment of the benchmark fixed intercept `20249/1000000`, nor its transmission to the frozen full analytic `F true s` on every first-60 CLOSED query cell. There is **no theorem asserting the original adopted seed is analytically sound**. Even if the seven-integral inequality passes, the true analytic F base conditions and all 430 successor steps remain manuscript-internal obligations.

No new axiom, sorry, admit, unsafe/native escape, h34-equivalent counting licence, changed c/K, root norm 7/2, bank row norm 12, 430+11, actual alpha, same-Q, bank read mode, or altered CI/dependencies.

## Verification and next action

Connected GitHub HEAD and original source definitions were read. Six candidate Lean theorem bodies are new. No Lean/Lake/Elan or staged fixed source-only import closure is available in this runtime; no compilation, kernel replay, transitive-axiom audit, or finite certificate replay was performed. Text-only scans are NOT Lean validation.

Next: actually certify `lambda>=13/100` from the ORIGINAL seven real integrals (including support cuts), then pay the fixed intercept through the frozen analytic source and prove the first-60 CLOSED-CELL F bound. Verify other 340 cell nonnegativity and full 430-round action predecessor bounds separately. Complete original U3/U4 selected counts, owner and root weights, PP/same-rho and one common 430+11 refinement.

**Complete manuscript-internal h34 remains OPEN.**
