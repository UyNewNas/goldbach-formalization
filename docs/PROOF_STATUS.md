# Verification boundary

This project is not a proof of Goldbach's conjecture or of the attached manuscript's main analytic theorem.

## Initial core

- Arithmetic definitions count each additive prime once.
- Finite good/bad count partition and subtraction.
- Exact rational endpoint comparisons and logarithmic transfer margins.

The endpoint comparisons take the displayed rational numbers as numbers; they do not prove that those numbers bound the analytic integrals.

## Concrete normalization

The new source proves convergence and strict positivity of the actual odd-prime Euler product and bounds the finite correction below by one. It derives growth of `C(N) N / (log N)^2`, then discharges the unit-absorption premise of the numerical transfer. These additions passed compilation, module replay, and the 177-declaration transitive axiom audit at commit `a6f206076b77e42a2bcd4d656031ea0751dd7c8a`. The resulting concrete transfer retains the actual Chen count lower estimate and bad-count upper estimate as explicit, unproved analytic inputs.

## Outstanding mathematical work

- Prove the analytic distribution and main-term estimates for the now-instantiated actual finite sieve.
- Keep compilation, module replay, and transitive axiom audits passing for each new analytic module.
- Prove the asymptotic bad-semiprime removal bound.
- Formalize the actual distribution and strengthened sieve interfaces, with all uniformity and order-of-limits hypotheses.
- Formalize the geometric and analytic meaning of the numerical certificates. Nine required author/independent/final-transfer replays have completed with matching mathematical fields, including the full extended run. This does not establish every analytic/table dependency in the package.
- Prove the separate Chen lower count and then deduce the final every-sufficiently-large-even-N conclusion.

The external-input exponent 0.74774 additionally requires the published 1.9728 Chen count; it is not an axiom in the verified core.

## Frontier interpretation

The proposed separate exponent 0.76407 improves the directly stated Li-Liu 0.9 theorem and 0.894 remark, if the draft is valid. It does not improve the manuscript's 0.749 deduction from accepted published inputs plus localization. The proposed external-input exponent 0.74774 improves that specific numerical deduction. No global priority or best-possible claim is made.

## CI contract

A green build means only the committed core compiled. CI also rechecks with leanchecker and audits transitive axioms under ImbalancedChen, allowing only propext, Classical.choice and Quot.sound. No custom analytic axioms, sorryAx or native_decide trust extensions are accepted.

## Verified checkpoint

Commit `a6f206076b77e42a2bcd4d656031ea0751dd7c8a` passed both push and PR checks. [PR run 37752040466](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37752040466) records build success, verbose replay of all eleven modules and the root, and 177 audited declarations within the standard three-axiom allowlist. The earlier full-Mathlib import run exceeded its kernel-replay time budget; focused imports resolved the observed bottleneck without removing a proof check. Lean/mathlib dependency artifacts remain explicitly pinned and trusted, rather than independently rebuilt from first principles.

## Verified localization checkpoint

Commit `26c128d85f45fd0ddd7719459d56fcb112fc582c` passed the full thirteen-module build, module replay, and 238-declaration axiom audit. [PR run 37754452855](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37754452855). The actual bad source is reindexed exactly, cut off using the literal real threshold and its natural ceiling, and its discarded contribution is proved negligible relative to the actual normalization. This pays only the small-receiver localization cost, not the retained-source sieve estimate.

## Verified sieve-source checkpoint

Commit `cf59a1fe88d8caf85b0a0a32549ec73b5e2c0078` passed the seventeen-module build, module replay, and 328-declaration axiom audit. [PR run 37756197691](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37756197691). The inclusive half-product source, unique ordered-pair count including squares, actual sieve product, source/modulus coprimality, and primitive shifted congruence are proved. The original logarithmic cutoff eventually clears the fifth-root cap, and fixed sublinear power-logarithm costs (including rounding) are negligible in the genuine normalization. These preparation theorems do not prove a level-sensitive upper sieve or the 6.786 analytic coefficient.

## Verified finite-sieve checkpoint

Commit `631466a7e36dc1c381813349a75decc345d8a24d` passed the eighteen-module build, module replay, and 369-declaration transitive axiom audit. [PR run 37758586617](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37758586617). The actual shifted source now instantiates mathlib’s `BoundingSieve`, retaining its inclusive endpoint, literal total mass, reciprocal-totient density, and exact congruence remainder. Upper-Möbius and lambda-square inequalities follow from proved mathlib theorems. The added level-truncation module is awaiting CI; neither its finite identities nor the model supply the outstanding analytic main-term/distribution estimates.

## Verified finite-level and Euler checkpoint

Commit `0ae2058371ec1b96da233fef42f882003e6d63a1` passed the twenty-module build, module replay, and 415-declaration transitive axiom audit. [PR run 37760141802](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37760141802). Input support at `L` yields exact lambda-square support at `L * L` and exact restrictions of the actual main/error sums. The finite Euler identity proves the prime-two normalization and the center-divisor correction, including its zero-center edge case. Allowed squarefree Selberg terms are explicitly products of `1 / (p - 2)`. No asymptotic approximation, optimized analytic coefficient, or distribution estimate follows merely from these finite identities.
