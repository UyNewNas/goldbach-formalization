# P1.4 input boundary — frozen upper rho0 numerical cutoff

## Internal manuscript arithmetic
Frozen upper exponent: rho0 = 19/96, exactly as specified in manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, at the upper construction (rho0, mu0, Theta, Lambda) and physical-upper indicator `P_N(N^rho0)`. The proof shows for each fixed N >= 8, `N < (N^(19/96))^6 = N^(19/16)` and `((N-2)/2 : Nat) < N`, hence `((N-2)/2 : Real) < (N^(19/96))^6`. The exponent arithmetic is exact: 6 * 19/96 = 19/16 > 1.

The new proof *specializes* the previously proved-candidate `actual_fixed_fifth_q0_zero_of_rough_six_cutoff` and `actual_fixed_fifth_centre_eq_lower_of_rough_six_cutoff` at the literal `w=N^(19/96)`. It retains the original `receiverTest N`, `sharedRankFour`, fifth-event lists, ordered sixth occurrences, PLUS-beta and complete a*b6 modulus. It does not alter N, cap, z, L, X, e, q, om or signed masses; no rounding or separate error invoice.

**Crucial scope restriction:** this statement proves the exact arithmetic specialization at the upper `w` argument. The polymorphic source itself still takes an arbitrary `w`; proving that a particular production/upper-tree entry actually passes this exact numeric argument is a separate *internal* source-level callsite obligation. No such identification is claimed for lower/marked/changed trees or other w. Nor does this eliminate low-third centre, primitive, modulus-prime or high-q errors. This is NOT asymptotic signed gain or complete P1.4 closure.

## External inputs
Unchanged, REGISTERED_NOT_PROVED_NOT_CALLED: frozen signed sharp-prime PP `eq:current-PP`, `lem:current-sharp-prime`, `eq:current-sharp-pi`. Premises: same original signed physical rho and H_N, complete squarefree N-coprime moduli at fixed theta < 1, original smooth-singleton, endpoint, geometric/Fourier and uniformity qualifications. Normalization fixed to frozen manuscript. Callsite not supplied; no PNT/Mertens/BV/spectral implementation, no new axiom or field.

## Frozen toolchain
Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants `c=49044063/25000000`, `K=8452171/1250000` unchanged.

## Verification boundary
SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no kernel replay, transitive axiom audit or independent review. Source-only packet imports require staging under the matching ImbalancedChen module path before compilation. The local runner lacks lean/lake/elan (each command exits 127); pinned dependency closure not available. Do not trigger CI or change pins.
