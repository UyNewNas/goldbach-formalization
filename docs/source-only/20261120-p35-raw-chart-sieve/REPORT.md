# P3.5: aggregate the raw n sieve on the original positive chart

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`b418ab427c294a0d239f8343e7cf185c7c3a8d1b`. The containing commit is the
new SHA. Adds only `Part3OriginalRawChartSieve.lean` and this report in
`docs/source-only/20261120-p35-raw-chart-sieve/`. Lean source SHA-256:
`7c06a42de9b07d99c043e4289fa27b82479bc1500fea1b0529cad453b7cdc769`.

## Mathematical candidate

For an actual original chart set `levels D k upper`, let
`Slots = Sigma z, {i in exceptional z}` with strict exceptional indices,
`V=2^j`, `Z=fixedZ D upper`, `W=max(V,Z²/V)`, `G=|a| nu`,
`L=U/nu=rowLength k`, and `B_z²=rowMass D r k z`. For nonzero residue a,
the proposed source proves the raw n-energy estimate

    sum_slots ( |N_raw(z,i)| / sqrt(W^tau_{z,i}) )^2
      <= 2 C_sieve (1+G L/Z) sum_{z in levels} B_z².

All variables, signs, original level-dependent coefficients and native
eigenvectors remain the same as in the preceding positive-chart Cauchy
candidate. The proof uses V>=1, W>=V, tau>=0, hence W^tau>=1; it bounds
the inverse-weight n energy by the unweighted energy and invokes the
prior `raw_original_row_square` with X=1 **separately at each level**.
Since all occupied levels satisfy Z<=z, the individual costs are summed
using 1+G L/z<=1+G L/Z. The row set is the exact union of the original
two endpoint-corrected level pieces, not an enlarged J range.

The source then composes that estimate with the previous actual-profile
and same-phase Cauchy theorem. Precisely, with
`B(ell,Y)=8 integral_{u>0} cosh(u)|profile(ell,Y,u)| du`, Y>0,
`Kcos=1/cos(3pi/8)`, native Pascadi J, and original raw positive
exceptional slot T, it proposes

    exists omega, for every r, negativeM, Y>0,
      (sum_slots |T_{z,i}|)^2
      <= (Kcos B(ell,Y))^2 (2+log(4V+1))^2
         * (J_(Z/2)(W,j,omega)+J_Z(W,j,omega))/4
         * 2 C_sieve (1+G L/Z) sum_z B_z².

The single omega is chosen before r, the sign and Y. The two J energies
are not evaluated or postulated bounded. No n coefficient is passed to
J and no equality with the post-removal row is asserted. The preceding
profile/cosine proof, including high-positive m-row vanishing, remains
an unevaluated dependency. The n-side bound is fixed-level and only
afterwards summed; it is not a full level-averaged spectral estimate.

The squared cost G L/Z = |a|U/Z can be large and differs from the
manuscript's ABL 7/32 price. The explicit profile budget can also be too
large because no uniform Fourier/scale bound is provided. Therefore
this is a lossy positive exceptional component with unevaluated J, not
the original all-cost (24), full-range AvgJ, a spectral gap or the 7/32
small-kernel result. It does not supply oldclass removal, regular,
holomorphic, opposite-sign or continuous contributions.

## Sources and external-input boundary

* Parent `Part3OriginalPositiveProfileBudget.lean`, blob
  `ca79a7931650cc487c847df8e90e862d8a03a29a`, gives actual profile
  budget and chart Cauchy into raw inverse-weight n energy; its proof
  dependencies are source-only.
* `Part3OriginalRawNSieve.lean`, blob
  `da0f3963d68f9e9f4ad01709a6f67557199cc234`, gives the original
  fixed-level signed n sieve for all X>0 and its raw GL/z price.
  Its reindexing and fixed-level supplier remain source-only.
* `Part3OriginalExceptionalPostRemovalPair.lean`, blob
  `a038900816ae4e167afb9f46ace2e142440d386c`, provides the actual chart
  levels, row mass and length; its post-removal n row is not used here.
* The original manuscript pin is
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (rechecked),
  distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`,
  §7 (24), §10(vii). No new external theorem is claimed. The precise
  Pascadi v3 Theorem J range/normalization, ABL v1 Lemmas 3.1–3.2 and
  numerical gap are recorded in the parent handoff and
  `AVGJ_APPLICABILITY.md`; none is supplied by this packet.
* Pinned mathlib `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` was
  read at `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` to check the
  signature of `Real.one_le_rpow` used in the proposed proof.

## Verification and next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including all imported proof bodies and the two J expressions.
`command -v lean` and `command -v lake` gave no binary, and the exact
import closure is unstaged. No compiler ran and there is no compiler
exit code or log. Rechecked configuration pins: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot be
checked. Stack 8192 KiB, virtual memory unlimited; no limit increased.
`sha256sum` gave the source hash above. `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). This static inspection is not compilation. No CI was started.

Next stage exact imports and compile/replay; audit transitive axioms.
Quantify the actual profile budget and evaluate whether this direct raw
cost can be paid, or replace it with a justified ABL eigenspace return.
The full J, regular/holomorphic/continuous parts, opposite sign, two
zero lanes, actual cutoff tail, 14eta/28eta, 128C enlargement and
original N-threshold/reserve order remain separate obligations.
