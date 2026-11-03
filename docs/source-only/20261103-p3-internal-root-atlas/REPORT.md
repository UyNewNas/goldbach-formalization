# P3.6 — manuscript-internal U5 root atlas and complete source regrouping

Base: `f91eadb8e329a3ffce7d91a6ab78500d41a86c24`.
Base tree: `bd9f5bd8c020d4886bbe9c1e1fa76235b9f1eb27`.
Branch: `chatgpt/p3-internal-root-atlas-20261103`.
Packet: `docs/source-only/20261103-p3-internal-root-atlas/`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. FULL P3.6 STILL YELLOW.**

The current request limits new work to proofs internal to the manuscript.
External analytic inputs are recorded in EXTERNAL_INPUTS.json, not implemented,
added as Lean axioms, or relabelled as proved. Existing source files are reused
without editing them. Their transitive imports are NOT newly audited or certified.

## Manuscript pin and a correction of work priorities

The accessible paper repository was freshly pinned at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.
This is the inspected repository version, not an assertion about unshared local revisions.
Relevant inspected source locations:

- `paper/source/manuscript-body.tex`, lines 255–358: same integer rho,
  physical versus auxiliary level, exact tensor identity, complete-scale PP,
  fixed-before-N moments and all logarithmic costs.
- `paper/source/modules/distribution-prime-product-completion-20261010.txt`,
  lines 1–90: PP is an ABSOLUTE arbitrary-log estimate. The source explicitly
  does not require a relative error in every cell's mass. Local medium M and
  whole-atom compiler licences are premises of that insertion module, but remain
  internal obligations of the whole paper.
- The same module, lines 185–255: classical UNROUGH Mobius SW is a recorded
  input; the rough-slot auxiliary-coprimality extension and elementary Brun
  reduction are manuscript proofs, not replacement external black boxes.
- `global-chen-lower-completion-20261010.txt`, lines 245–295: the original U5
  level is max(v(t),v(t+u),Lambda-3a/8); the finite H/h realization treats zero
  mass absolutely. This is the root formula used below.
- `final-classical-input-correspondence-20261010.txt`: names and restricted
  quantifiers of cited spectral inputs. This is manuscript provenance; the
  primary external papers were NOT re-audited during this turn.

Thus the preceding optional plateau/relative-Theta exploration is not promoted
into a requirement to prove a uniform positive mass for every exact root fibre.
This increment returns to exact full-source coverage. It proves no new BV, SW,
PNT, Mertens, Kuznetsov, large-sieve or spectral-gap theorem.

## 1. Full four-branch algebra, not another witness rectangle

`P3U5RootAtlas` uses the original `level`, `VariableEnvelope.v` and `plateauLevel`.
Let a=417/5000, h=19/125, mu=25/128, c=90621/160000, and s=u+t.
On the ENTIRE closed original domain a<=u<=t<=h, the level has four exact owners:

1. rise: s<=mu, value (1+s)/2;
2. plateau: s>mu, A(t)<=c and C(s)<=c, value c;
3. fall: s>mu, not plateau, A(t)<=C(s), value 57/64-3s/2;
4. head: all remaining points, value (1+t)/2.

On this domain A(s)>c, so the rising branch needs no additional plateau test.
All equality faces have an explicit owner: s=mu goes to rise, both plateau
faces belong to plateau, and an A(t)=C(s)>c tie goes to fall.
The original root is never rounded, approximated or replaced by a global cap.

The full plateau is characterized, with both equalities INCLUDED, by

`t <= 10621/80000` and `u+t >= 17293/80000`.

This extends the preceding rectangle inclusion to the exact whole plateau.
The falling/head comparison is exactly `3u+4t <= 25/32`.
The owner is a bookkeeping partition of labels, NOT a newly admitted causal
policy, not an analytic smoothing, and not a permission to apply PP to an
arbitrary signed sharp coupled domain.

## 2. Actual U5 source, same rho, full coverage

`P3U5FullSourcePartition` evaluates this owner at the existing logarithmic
coordinates of each pair in `pairSupport N`, retaining the original strict
prime order, half-open prime windows and target exclusions. An arbitrary
keep predicate stays visible. The four lane supports are pairwise disjoint,
and their sum is exactly the entire kept source for EVERY additive test.

The theorem is instantiated to the existing selectedGamma, selectedEmpty
and selectedResidual. The SAME modulus carrier and SAME rho are kept outside
the lane decomposition; counts and their exact coprime means are not split
using different coefficients. No empty-word term or repeated product is deleted.
The complement of keep is retained by a separate exact identity.

The plateau lane is proved equal to the previous rootFiber at plateauQ,
for arbitrary keep and all N>=2. In particular the earlier plateau result
is now attached to its exact full owner region, not merely its witness box.

The complete finite image `rootValues` supplies another exact partition:

`sum_Q selectedResidual(rootFiber Q) = selectedResidual(whole kept source)`.

The original residual-domain tests of rootFiber are supplied from the existing
root geometry, so there is no extra discarded domain. This equality does NOT
say that rootValues has fixed or logarithmic cardinality and does not permit
summing a full N/log^A error per fibre for free.

The same physical normalizer is also reindexed exactly:

`sum_Q selectedTheta(N,Q,rootFiber Q,sigma)`
`  = sum_t sigma(t)*thetaAtom(N,rootQ(N,t),t1*t2)`.

The right-hand side is named movingTheta solely as a labelled ledger. It is
NOT asserted equal to one common-Q Theta, or asserted to have a density limit.

## 3. Nonconstant fibres and why all-fibre mass is the wrong detour

`P3U5AffineRootFibers` proves the exact original product/log coordinate identity.
On either the rise or fall lane, equality of rootQ gives equality of u+t, hence
of the ACTUAL product t1*t2. Reusing ordered prime-factor uniqueness then gives
equality of the original pair. Every exact-root fibre in either of these two
lanes consequently has cardinality at most one. On the head lane, a common root
fixes the larger prime, but the smaller prime is not asserted unique.

The original lower cutoff supplies `t1*t2 >= N^(2a)`. For weights bounded by
height>=0, the finite reciprocal-mass estimate on a rise/fall root fibre is

`reciprocalMass <= height/N^(417/2500)`.

This is a finite arithmetic statement, not an asymptotic PP counterexample.
It prevents confusing these fibres with the positive-area plateau witness.
The manuscript's absolute PP does not require assigning each such fibre an
independent relative-Theta bound with a common logarithmic mass floor.
A final combined lane/root reindexing retains every original label.

## External versus internal obligations

EXTERNAL_INPUTS.json records the classical statements and their restrictions;
no implementation is included. In particular the following remain INTERNAL,
not new external assumptions: restricted moving-residue medium M; actual
same-rho whole-atom compiler admission with every full/selected square; HB3
insertion and rough SW adaptation; one-/two-long Brun reductions; Fourier,
chart and coefficient scalar costs; exact source/root matching; and final PP
assembly. Any missing ones stay yellow. Merely recording the external inputs
does not certify their transitive source implementations or close P3.6.

Full U5 root SOURCE COVERAGE is the scoped advance here. Required causal-history
admission/keep correctness, analytic estimates of the nonplateau branches,
empty-word source identification/payment, unsupported high-rank/enhanced
coefficient classes and full PP assembly remain open. This covers U5, not all
other Chen roots or the excluded full87 work. Sparse-fibre relative mass is
parked as an optional stronger problem, not a newly imposed PP prerequisite.

## Validation boundary

The original factor-uniqueness declaration was freshly read at the base commit.
The predecessor plateau and selected-source files were read from their mounted
archives, and their recorded Git blob identities checked. Source arithmetic
uses existing field/order/power and finite-sum tools; no new proof admissions,
axioms, unsafe evaluation, decision certificate or analytic theorem is supplied.

`check_packet.py` performs exact-rational geometry/boundary tests, independent
finite signed partition/normalizer regressions, ordered-prime-product checks,
byte inventories, delimiter and forbidden-form scans. These do not execute Lean,
prove Python/Lean correspondence or validate transitive dependencies. CHECKS.json
is the actual run receipt, not a compilation certificate. VERIFY.lean is unexecuted.
No Lean/Lake executable was found in this runtime. No compiler, kernel replay,
CI dispatch, project producer, child agent, Codex task or external-paper proof
implementation was performed. No independent mathematical reviewer is claimed.

Only this packet is added on a new branch. Production, previous packets, lock
file, toolchain, manuscript, main branch, full87 and external tracker remain
unchanged. No merge, release, PR or paper publication is requested.

## Proposed tracker delta

```text
黄｜P3.6（稿内证明范围）
    蓝｜原U5全域四分支与完整平台等号边界源码 [containing commit]
    蓝｜全保留来源/keep补集、同rho与原Q有限纤维重组源码 [containing commit]
    蓝｜原Theta逐根值精确总账、非平台纤维基数与倒数质量上界源码 [containing commit]
    黄｜实际causal许可/所需keep、高秩与空母词、完整稿内PP装配
稿外｜经典解析输入仅登记；不实现；无新增验收状态
```
