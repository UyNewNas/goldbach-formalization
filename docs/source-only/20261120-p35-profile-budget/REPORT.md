# P3.5: explicit positive exceptional transform budget

## Baseline and changes

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`4df26579ffe63f4609b097965b3c1a0c8fcda767`. The containing commit is
the new SHA. Adds only `Part3OriginalPositiveProfileBudget.lean` and
this `REPORT.md` under `docs/source-only/20261120-p35-profile-budget/`.
Lean source SHA-256:
`47350362fc8b1eb5578429b6fb02800681be496778652858774763ef706f6954`.

## Exact proposed deduction

For the *actual* fixed original test `spectralTest ell Y`, with Y>0,
let `profile ell hY` be the existing cosine profile and define the
explicit, nonnegative and finite quantity

    B(ell,Y) = 8 integral_{u>0} cosh(u) |profile ell hY u| du.

The candidate `actual_numerator_le_profileBudget` states, uniformly for
0<=alpha<1/2,

    |exceptionalWeight (spectralTest ell Y) alpha| <= B(ell,Y).

It uses the already-written exact exceptional integral representation,
including its factor 8, and the already-written `weighted_profile_L1`.
On u>0, cosh(2 alpha u)<=cosh(u), so a norm-of-integral comparison gives
the bound. No lower bound on lambda, numerical gap or transform estimate
is added as a premise. B remains a real integral depending on the same
Fourier mark ell and physical scale Y, not a claimed uniform constant.

Combining this with `raw_positive_slot_cosine_bound`, the proposed
`raw_slot_le_profileBudget` bounds each *original* positive trace slot
by

    Kcos B(ell,Y) |M_{z,i}| |N_raw(z,i)|,
    Kcos = 1/cos(3 pi/8).

The inherited raw cosine candidate uses the uncompiled
`original_m_zero_high` at tau>3/4 and elementary cosine monotonicity on
the rest. It is a bound on the original product, **not** a uniform
denominator bound for arbitrary eigenvectors or an n-only statement.

`raw_chart_profile_to_pascadi` then applies finite Cauchy over the same
physical `Slots` and `original_chart_J_one_phase`. With W=max(V,Z²/V),
and actual native `pascadiJ`, it proposes

    exists omega, for every r, negativeM, Y>0,
      (sum_slots |H_{z,i} conjugate(M_{z,i}) N_raw(z,i)|)^2
      <= (Kcos B(ell,Y))^2
         * (2+log(4V+1))^2
         * (J_(Z/2)(W,omega)+J_Z(W,omega))/4
         * sum_slots W^(-tau_{z,i}) |N_raw(z,i)|^2.

The source leaves the final energy literally as
`sum (|N_raw|/sqrt(W^tau))^2`; the displayed rpow notation is its
positive-W interpretation. The phase is chosen before r, sign and Y;
the endpoint-corrected levels and same native eigenvectors are retained.
No fake common n sequence, oldform equality or full J bound is used.
The previous node's `raw_original_row_square` is a possible fixed-level
input at X=1/W, but its use, the actual occupied-level aggregation, and
the comparison of its large G L/z cost with the reserve are **not**
included here.

This candidate is for the positive-sign finite strict-exceptional chart
only. B has not been bounded uniformly by the original Fourier budget;
it could be too expensive to pay. It neither proves all-cost (24) nor
extends AvgJ, provides a global 7/32 gap, handles opposite K transform,
returns oldforms or handles regular/continuous contributions.

## Sources and external boundary

* `Part3ActualPositiveCosineProfile.lean`, blob
  `1d8fc4fdc7bd73ee9681e573dba35f5d70d98b67`: exact `profile` and
  `weighted_profile_L1`. `Part3ActualPrescribedPositiveJ.lean`, blob
  `ac43ee9822d8df17a60e16d904006b3617d066e4`:
  `exceptionalWeight` and `exceptional_transform`.
* `Part3OriginalPositiveRawCosine.lean`, blob
  `c7df867dad4446002998d457d29e5e78e25729bc`; its high-order vanishing
  and cosine dependencies are uncompiled. `Part3OriginalPositiveRawCauchy.lean`,
  blob `02abfecfd6ee1307874b80808a42685845ebcb3b`: original raw slot,
  original m and level-dependent n objects, same-phase chart energy.
* `Part3OriginalRawNSieve.lean`, blob
  `da0f3963d68f9e9f4ad01709a6f67557199cc234`: the previous raw fixed-level
  source candidate, with its explicit `(1+max(1,X))(1+|a|U/z)` price.
  It is not imported or treated as a level average in this packet.
* Rechecked manuscript entry
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  `paper/source/manuscript-body.tex` blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; this matches the chain.
  Distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`,
  §7 lines 349–380 and §10(vii) give the original target and inputs.
  Pascadi v3 Theorem J, ABL v1 3.1–3.2, numerical gap and their exact
  normalization/range are recorded in `AVGJ_APPLICABILITY.md` and the
  parent report. No new external theorem was introduced.

## Verification and remaining work

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including upstream raw-cosine, high-positive-zero, integral and
one-phase candidates. No Lean/Lake binary is in PATH; the exact import
closure is unstaged. No compiler ran; no compiler exit code or log
exists. Rechecked repository configuration: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`. Installed versions could not
be checked. Stack 8192 KiB, virtual-memory limit unlimited; no resources
were increased. `sha256sum` gave the source hash above; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). These are not compilation. No CI was launched.

Next compile the exact candidate/import closure, kernel-replay and check
axioms. Bound B quantitatively in the original mark/scale order, and
aggregate the raw inverse-weight n energy either using the previous
expensive fixed-level theorem or the correctly normalized oldclass
return. Supply the independently needed J, regular, holomorphic and
continuous inputs. Both zero lanes, actual truncated tail, separate
14eta/28eta weights, 128C enlargement and original N-threshold/reserve
order remain open.
