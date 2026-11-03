# P3.6 — manuscript-internal smooth U5 atlas and harmonic wall payment

Base commit: `f0f55d7b3d12b2b892978f63ef63988961edfca0`.
Base tree: `7ba6df460ae6fbfe97d7d8e2082df52e76f627a9`.
Branch: `chatgpt/p3-internal-smooth-atlas-20261103`.
Packet: `docs/source-only/20261103-p3-internal-smooth-atlas/`.
Paper pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. FULL P3.6 REMAINS YELLOW.**

This increment proves only manuscript-internal geometry, finite source algebra
and the use of an existing harmonic-box supplier. External research inputs are
recorded, not implemented or introduced as new Lean axioms. Three proof modules
contain 620 lines and 67 definitions/theorems/abbreviations. The verification
file is an unexecuted handoff. No independent mathematical reviewer is claimed.

## Why this follows the manuscript, rather than a sharp-domain shortcut

The inspected prime-product completion, section 4, lines 143–185, keeps a smooth
geometric factor and charges its Fourier norm. It does not allow a new signed
sharp coupled-domain theorem. The finite H/h realization fixes its approximation
stage before the target grows and pays proper affine walls. The previous packet
supplied four exact owners, but those sharp indicators were NOT smooth PP charts.

The present construction supplies actual C-infinity weights for all four lanes,
an exact same-rho finite identity, and a sequential harmonic approximation. It
does not convert a small harmonic wall mass into a small arithmetic discrepancy.
It does not license arbitrary keep predicates for analytic PP merely because
its finite algebra and positive harmonic domination permit such predicates.

## 1. Actual smooth four-lane partition

For x=(u,t), define the four margins from the ORIGINAL owner tests:

- g0 = mu-(u+t);
- g1 = c-A(t);
- g2 = c-C(u+t);
- g3 = C(u+t)-A(t),

where mu=25/128, c=90621/160000, A(t)=(1+t)/2 and C(s)=57/64-3s/2.
These are explicitly represented as c_j-L_j(x), with actual nonzero continuous
linear forms L_j. Their nonzeroness is proved by evaluation, not assumed.

Let s_j = Real.smoothTransition((m+1)*g_j). The constructed weights are

w_rise = s0,
w_plateau = (1-s0)*s1*s2,
w_fall = (1-s0)*(1-s1*s2)*s3,
w_head = (1-s0)*(1-s1*s2)*(1-s3).

All four are genuinely C-infinity, lie in [0,1], and sum EXACTLY to one at every
point, including every old equality face. Replacing each smooth step by the bit
1_(g_j>=0) reproduces the exact previous owner convention, with no new domain
restriction. The level, rootQ, physical ceiling and integer rho are NOT averaged.
The smooth chart can overlap adjacent owner regions inside its transition strips;
no branch-specific support/admission licence is asserted there.

Define e(z)=1-S(z)-S(-z), where S is the same smoothTransition. Then 0<=e<=1,
e(0)=1, and e(z)=0 for |z|>=1. The common majorant is

B_m(x)=sum_(j=0..3) e((m+1)*g_j(x)).

A proved four-input circuit inequality gives, for every lane,

abs(1_(owner(x)=lane)-w_lane(x)) <= B_m(x),  0<=B_m<=4.

On any one of the four equality walls B_m>=1. Thus arithmetic labels on the
walls have not been silently deleted. Away from all four transition strips,
the smooth weights equal the original owner indicators exactly.

## 2. Same-rho finite source and a visible discrepancy defect

`P3U5SmoothSourceLedger` acts on the original kept pair carrier. For every real
signed test F it proves

sum_lane sum_(t kept) w_lane(log_N t)*F(t) = sum_(t kept) F(t),

and the exact sharp/smooth identity for EACH lane with its literal signed
`laneDefect`. The sum of all laneDefect values is zero. The kept complement
is conserved separately. No empty-mother source, product multiplicity or
original q-coprime mean is dropped.

The identities are instantiated to selectedGamma, selectedEmpty,
selectedResidual and the moving original thetaAtom ledger. All use the SAME rho,
modulus carrier and actual rootQ. The total scalar restoration cost is exactly
sum_t abs(sigma(t)), not four times that quantity.

For an individual sharp lane the bound is deliberately left in its true form:

abs(laneDefect(F)) <= sum_(t kept) abs(F(t))*B_m(log_N t).

In particular `selectedResidual_lane_defect` retains the original Gamma-minus-
empty arithmetic test inside this sum. This RHS is NOT declared small by the
harmonic theorem below: that test need not have a uniformly bounded harmonic
profile. The signed PP wall-payment bridge remains an internal obligation.

## 3. Proper walls and actual target-deleted harmonic mass

`P3U5SmoothWallMass` works on the entire original positive logarithmic cube
[a,h)^2, a=417/5000 and h=19/125, with density 1/(u*t). The old exact prime order
is restored by the existing strict-selector dictionary.

The existing geometric null-wall theorem is applied to the four explicitly
nonzero forms. Off those walls B_m becomes zero eventually at each point.
Dominated convergence with the integrable majorant 4/(u*t) proves

I_m = integral_(cube) B_m(u,t)/(u*t) du dt -> 0.

For each fixed m, the existing `tendsto_actualPrimeBoxTestSum_cube` is INVOKED on
this actual continuous profile. Its original target-prime exclusions and exact
half-open endpoints remain unchanged. The original U5 reciprocal-totient sum is
bounded by that complete box using the existing exact finite order dictionary:

sum_(t in pairSupport N) B_m(log_N t)/phi(t1*t2) <= cubeWallMass(N,m).

The new terminal declaration is

`ImbalancedChen.P3U5SmoothWallMass.exists_common_four_lane_harmonic_approximation`.

Its exact quantifier order is:

for every eps>0, there is m0, and for EACH fixed m>=m0 there is a target threshold;
AFTER that threshold, all keep predicates, heights H>=0 and signed tests F with
abs(F(t))<=H on the kept carrier are covered SIMULTANEOUSLY for all four lanes.
The conclusion is

sum_lane abs(sum_(sharp lane) F(t)/phi(t1*t2)
             -sum_(kept) w_lane(log_N t)*F(t)/phi(t1*t2)) <= eps*H.

No positive mass or inverse Theta is used, and empty/zero selected families are
included. This is a two-stage fixed-policy result. It does NOT assert a common
N threshold for every m>=m0, a rate for m=m(N), or a new arbitrary-log PP bound.
The original singular-series Theta is not replaced by reciprocal-totient mass.

## Input boundary and remaining manuscript obligations

EXTERNAL_INPUTS.json references the previous complete classical-input register.
The harmonic prime limit is reused through an already existing repository
interface; no PNT/Mertens, SW, BV, large-sieve, spectral-gap or Kuznetsov proof
is added. Fundamental calculus/finite-sum lemmas come from existing imports.
No new external analytic assumption is inserted into a target theorem.

Still INTERNAL and open: admissible causal keep/history and same physical
coefficient binding; quantitative mixed Euler/Fourier budgets for the actual
whole chart family and its prescribed parameter order; transferring any
individual sharp-lane arithmetic defect to a paid PP error; original empty-
mother identification/payment; unsupported high-rank/enhanced classes; the
remaining medium/long and final same-rho PP assembly. The new C-infinity fact
alone is not a proof of those quantitative/licensing conditions.

The known local-native dependency source gap and source-only import installation
remain engineering requirements. No upgrade, replacement definition or claim
of a closed compilation dependency graph is made.

## Checks and reproducibility

The base branch and immutable commit/tree were freshly fetched. Earlier delivered
archives were used for exact predecessor source composition. Fresh source reads
include the pinned paper section, AffinePrimeGates, ActualPrimeBoxTestFunctions,
and P4BSmoothStepDerivativeBudget. Referenced predecessor identities are in
REGISTRY; this is not a new audit of every transitive analytic argument.

`check_packet.py` passed 3,490 exact-rational owner/boundary cases, 625 unit-cube
partitions, 10,000 unit/bit circuit-error cases, 2,500 rational Lipschitz cases,
824 independent numerical transition-model cases and 600 signed finite-source/
domination cases. Static forbidden-form and delimiter scans also passed. The
numerical transition model is not Lean Real.smoothTransition evaluation, and the
finite source tests are not evaluations of repository Gamma definitions.

These tests do NOT elaborate Lean, verify null-wall or prime-box limits, prove
Python/Lean correspondence, or validate a signed PP estimate. No Lean/Lake
executable was found; no compiler, kernel replay, axiom audit, repository proof
guard, numerical producer, CI dispatch, Codex task or subagent was run. No green
status follows. Exact remote blob/zip checks are separately recorded at delivery.

Only this new packet is committed, with skip-CI requested. Prior packets,
production, manuscript, toolchain, dependency lock, main branch, excluded full87
work and external tracker remain unchanged. No merge, PR, release or manuscript
publication is requested.

## Scoped status delta

```text
黄｜P3.6（稿内证明范围）
    蓝｜原U5四分支真实C∞单位分解、原等号owner与显式墙带误差源码 [this commit]
    蓝｜同rho全来源/空母词/keep补集的平滑恒等式及总标量质量守恒源码 [this commit]
    蓝｜四条实际仿射墙、同目标排除调和质量与先平滑后N的共同近似源码 [this commit]
    黄｜实际causal许可、全chart导数/Fourier预算与PP算术墙项付款
    黄｜空母词、高秩/增强及完整稿内同rho PP总装
稿外｜沿用登记；仅记录，不实现，无新增证明验收
```
