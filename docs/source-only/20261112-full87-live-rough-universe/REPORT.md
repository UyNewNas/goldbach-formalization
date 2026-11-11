# P1.4 — original full87 active rough-universe support (SOURCE ONLY)

- Parent remotely verified before branch creation: `0ef853195809355a0b4bb9544a2989829106427d`.
- Proof-source commit: `49e1f9b0e8f2ea62ac93358f070090bffac1a645`.
- Independent branch: `chatgpt/p1-full87-live-rough-universe-20261112`.
- New source: `docs/source-only/20261112-full87-live-rough-universe/P4AOriginalFull87LiveRoughUniverse.lean` (Git blob `b56a4e5aacab77033d1ec6ec9ecf060e01861064`).
- Original manuscript: `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Toolchain pins: Lean v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native 09b97db5764ade1246bfb77206baa1b124760958. Constants c=49044063/25000000 and K=8452171/1250000 unchanged.

## Actual internal candidate
The literal finite alphabet `roughPrimeUniverse N cap w z` has product `U_N`. From existing `fixedRoughSupport_primeFactors_mem` and `fixedRoughSupport_squarefree`, each original retained rough factor b divides U_N. By the already-provided `actualSmallRoughRho_ne_zero_factors`, every genuinely nonzero original physical coefficient q=a*b has a<L strictly and b|U_N. Therefore (for the ORIGINAL policies and fixed N,cap,w,z,L):

  `full87PhysicalRhoChange ... d ≠ 0 ⟹ (d:ℝ) < L*(U_N:ℝ)`

and this actual signed full-q coefficient is zero when d lies on or above that bound. The last candidate theorem applies that exact cutoff to `full87_owned_signed_sharp_callsite`, preserving the original 87-cell source sum, signed old-minus-new `rho`, complete modulus d, beta attachment and occurrence multiplicities. No new high-q mask or arbitrary coefficient class.

This cuts only entries proven zero from the SAME finite physical signed invoice. Importantly, U_N is the product of ALL primes in the actual rough universe, **not** the physical level attained by the stopped tree and not known to be O(N^θ) with θ<1. This step is neither PP admissibility nor a smaller H_N budget. We did not convert a local active-level statement into a global exponent bound.

## Checks and truthful validation
- GitHub source file readback: original blob `b56a4e5aacab77033d1ec6ec9ecf060e01861064`; separate final readback required after documentation commit.
- Source token scan: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in candidate Lean code.
- Exact independent small-integer subset-product check: 768/768 synthetic cases (six small primes, 64 subsets, 12 small factors); NOT original87 arithmetic replay and NOT Lean verification.
- Actual local commands `lean --version`, `lake --version`, `elan --version`: all exit code 127, command not found. `.lake/packages/mathlib` and `.lake/packages/goldbach-lean` absent. No Lean elaboration or kernel replay possible at the fixed pins. Source-only imports also need path adaptation; no compile is claimed.
- Verification: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. KERNEL_REPLAYED=false, TRANSITIVE_AXIOM_AUDIT=false, INDEPENDENT_REVIEW=false. Existing and new proof candidates may have Lean type errors. No CI/Actions dispatched.

## Remaining exact obligations
1. Derive actual policy-specific full-q `q≤N^θ`, θ<1, **from the genuinely active rank-6/rank-8 ordinary stopped levels, rather than from U_N or an auxiliary carrier**; check initial low-rank/inherited branches separately, and strict/non-strict endpoints. Existing `P1OriginalVariableFifthFullModulusBound.lean` applies to an original variable fifth policy; its ceiling cannot be silently transferred to the later licensed sixth/eighth.
2. Show both original signed sixth/eighth coefficients satisfy the frozen manuscript §4 permitted smooth-singleton support, fixed chart/scales, and endpoint; keep the two external sharp PP inputs REGISTERED_NOT_PROVED / NOT_CALLED.
3. Ordinary continuation → genuine residual integral and weighted actual-parent mismatch o(H_N); saved87 original witness and signed numerical gain.
4. Raw/finite/filtered, low/high q, rank9, changed/tagged, compiler/density reserves, same rho.
5. Fixed-version Lean compilation, kernel replay, transitive axiom audit and independent review. P1.4 stays yellow.

No main/master update, force push, merge, toolchain upgrade, Codex, additional cloud resources or new CI.
