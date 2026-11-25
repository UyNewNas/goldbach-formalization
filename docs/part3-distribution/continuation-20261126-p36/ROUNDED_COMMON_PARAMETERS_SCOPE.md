# One common parameter choice for the original rounded U5 output

**Source-only candidate; no Lean compilation, kernel replay or complete
declaration/axiom acceptance is claimed by this note.**

The new module is `ImbalancedChen/P3OriginalU5RoundedCommonParameters.lean`.
It consumes the existing `P3OriginalU5RoundedBetaReserve` supplier and the two
new narrow consumers `P3OriginalU5WarmRoundingPayment` and
`P3OriginalU5RoundedUniformModulusCap`. It does not replace any of them.

## Contract and parameter order

For a fixed coarse mesh, positive rough-box reserve `etaBox`, positive beta
reserve `etaBeta`, and positive `epsilonMax`,
`exists_rounded_U5_common_parameters` chooses one `epsilon`, one positive upper
fine width `tau0`, and one threshold `N0 >= 2`. It also returns

```
0 < epsilon < 1/8,
epsilon < epsilonMax,
epsilon < 1/272.
```

All choices precede the target, receiver, candidate bank, original external
prime pair and finer mesh. For every later even `N >= N0`, actual
`R : PairRange`, `bank : CandidateBank mesh`, `t in pairSupport N`, and
`0 < tau <= tau0`, the theorem simultaneously supplies:

1. The original `roundingLoss` at cap `ceil(cutoff N)` is less than `etaBox`.
2. The literal beta attachment gap is nonnegative and at most
   `etaBeta * singularSeries N / log N`.
3. Every nonzero value of the same `roundedRho N epsilon tau` has complete
   physical modulus `fullModulus t k < N^(599/1000)`.

The fixed policy in every conclusion is
`selectedPolicy R bank (1/1000) false N t`. No per-row or per-mesh epsilon is
selected after the common parameters.

## Exact supplier instantiations

The existing beta supplier first chooses epsilon, with

```
nu = attachmentNu = 34/125,
r = 417/1360,
epsilon request = min epsilonMax (1/272).
```

The identity `nu * r = 417/5000` is proved by exact rational normalization.
It gives the original U5 upper rough cutoff. The other beta powers are exactly
`smallCutoff N epsilon = N^(attachmentNu * epsilon^2)` and
`smallLevel N epsilon = N^(attachmentNu * epsilon)`.

The beta choice gives `epsilon < 1/272`, and the exact identity
`(34/125) * (1/272) = 1/1000` supplies the small-beta allocation needed by
the support consumer. The independent bound `epsilon < 1/8`, together with
epsilon positivity, supplies
`attachmentNu * epsilon^2 < 417/5000` for the rough wall-payment consumer.
Neither allocation is assumed as an additional conclusion-shaped input.

After epsilon is fixed, the support and rough-loss suppliers return two
positive upper fine widths. Their minimum is the common `tau0`. The maximum
of the beta and rough-loss thresholds is `N0`; the support theorem already
applies at every `N >= 2`. This combination is valid because both mesh
suppliers quantify over every smaller positive mesh. It does not assume
that rounded coefficients are monotone, or equal, when the mesh changes.

At the canonical cap, the covering condition for the beta theorem is exactly
`cutoff N <= ceil(cutoff N)`. The conclusion is then rewritten through the
existing definitions `roundedSupport`, `roundedRho`, `smallCutoff`, `smallLevel`
and `cutoff`.

## The literal beta gap

`betaGap` is only a transparent abbreviation for

```
actualSmallEulerProduct N (ceil(cutoff N)) (smallCutoff N epsilon)
  * reciprocalTotientDensity
      (universe N (ceil(cutoff N)) (smallCutoff N epsilon) (cutoff N))
      (coefficient policy N (ceil(cutoff N))
        (smallCutoff N epsilon) (cutoff N) tau)
  - physicalDensitySum (roundedSupport N epsilon)
      (roundedRho N epsilon tau policy).
```

The rough coefficient and physical coefficient have the same policy,
target, epsilon, cap and fine mesh. The sign-sensitive small beta attachment
is inherited from the existing `roundedRho` construction. The original
external pair remains in the complete modulus of the support conclusion.
No beta density estimate, Euler bound, absorption argument or unique
small/rough factorization is reproved.

## Boundary of the result

The rough-box reserve is a bound on the unnormalized rough `roundingLoss`;
the beta reserve is on the singular-series/log-target scale. The theorem
does not equate these two scales or claim their sum is a final normalized
density error. It does not evaluate raw density, prove a physical density
main-term lower bound, identify raw and rounded rho, identify rho at different
meshes, supply common physical Q or a whole-atom tensor identity, or conclude
family admission or PP.

The manuscript boundary remains the frozen 2026-11-06 coefficient appendix's
finite approximation and beta attachment, and the sieve appendix's
`sv:physical-lower`, at manuscript commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. This parameter consumer joins the
already stated error and support interfaces; it adds no external theorem
formalization and no replacement analytic hypothesis.

The author changed only this new module and this scope note, without running
Lean, starting a cloud job, or staging, committing or pushing. Exact-source
strict compilation, official checker replay and the full defining-module,
type and transitive-axiom audit remain the required acceptance evidence.
