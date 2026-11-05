# P3.6 — actual Point d coordinate derivative to Euclidean Frechet derivative

Base (read and compared): '3cca15cee2cd43370a53bdcb4bb0df7cb9047c2a'.
Working branch: 'chatgpt/p3-internal-original-w-20261105'.
Manuscript: 'UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b', 'paper/source/modules/distribution-prime-product-completion-20261010.txt', §4 (F).
Pinned mathlib: 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'.

**SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. P3.6 still YELLOW.**

## This round's actual manuscript-internal proof bodies

The previous signed-square module proved the finite physical frequency sign
but could not connect Mathlib's Frechet derivative to the ORIGINAL 'mixed'.
This packet uses the pinned 'EuclideanSpace.equiv (Fin d) Real', which is a
continuous *linear equivalence*, to identify the actual Point d shift
'shift p i t' with the Euclidean line 'x + t • basisDirection i'.

1. 'coordinateDeriv_pulled_eq_fderiv': at a genuine differentiability point,
   the old 'coordinateDeriv i' of the exact pulled-back f equals
   'fderiv Real f x (basisDirection i)'. This is proved by composing the actual
   one-dimensional derivative of the affine line with a genuine Frechet
   derivative, not by defining a new partial derivative proxy.
2. 'orderedDirections_apply' and 'orderedDirections_doubled': turn the literal
   original ordered list, including each of the two repetitions in 'doubled S',
   into the precise Euclidean coordinate vectors consumed by the previously
   written 'subsetDirections' / 'subset_frechet_fourier'.
3. 'mixed_pullback_eq_frechet': induction over the old recursive 'mixed' uses
   the genuine Mathlib 'DifferentiableAt.iteratedFDeriv_succ_apply_left'' and
   differentiability supplied by finite-order 'ContDiff', producing an exact
   equality to the iterated Frechet derivative evaluated on the entire ordered
   list. The level is the list's actual length, without n+1 in the premise.
4. 'mixed_actual_eq_frechet' and 'actualMixedFamily_eq_realFrechet' specialize
   the result to the old 'w : Point d -> Real', 'doubled S' and the old
   'actualMixedFamily', with only a transparent real-to-complex value cast.

The last theorem is **not** the complexified Frechet Fourier identity:
'iteratedFDeriv' of the complex-valued chart and its real cast must still be
identified, as must the Fourier-space Haar measure and originalWD integrals.
The actual smoothness/ContDiff requirements for every original physical W_T
are open and have not been silently declared satisfied. The result says nothing
about an arithmetic PP discrepancy and keeps the existing rho untouched.

## Mathlib API source review

Read the pinned implementations of 'EuclideanSpace.equiv', 'EuclideanSpace.single',
'PiLp.single_apply', 'HasDerivAt.smul_const' and 'HasFDerivAt.comp_hasDerivAt',
'ContDiff.differentiable_iteratedFDeriv', the multilinear constant-evaluation
rule, and 'DifferentiableAt.iteratedFDeriv_succ_apply_left''. The candidate
includes their exact intended argument types; no library upgrade was made.

## Executed checks and remaining verification

Ran 'python3 check_packet.py' on the candidate: 105 point/Euclidean coordinate
shift cases, 498 SymPy polynomial ordered-mixed differentiation cases,
source-token scan and delimiter scan passed. These are independent finite
regressions, not an analytic proof or Lean elaboration. No Lean/Lake, kernel
replay, CI, transitive axiom audit, numerical heavy producer or Codex executed.
'VERIFY.lean' is an unexecuted audit target; no green state is claimed.

NEXT: prove complexification of actualMixedFamily into the Frechet-Fourier
identity; prove Point d/EuclideanSpace measure normalization, derive the
nonconditional multi-dimensional (F) product majorant and L1/H tail, then
pay the complete same-rho signed modulus mass including product=T separately.
Admission of actual W_T families, causal/HB complete source, empty mother
words and high-rank/enhanced families also remain manuscript-internal open.
The excluded full87 node is untouched. All external analytic inputs remain
record-only in 'EXTERNAL_INPUTS.json' and no axioms were added.
