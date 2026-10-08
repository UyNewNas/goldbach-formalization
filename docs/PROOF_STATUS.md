# Verification boundary

This project is not a proof of Goldbach's conjecture or of the attached manuscript's main analytic theorem.

## Initial core

- Arithmetic definitions count each additive prime once.
- Finite good/bad count partition and subtraction.
- Exact rational endpoint comparisons and logarithmic transfer margins.

The endpoint comparisons take the displayed rational numbers as numbers; they do not prove that those numbers bound the analytic integrals.

## Concrete normalization

The new source proves convergence and strict positivity of the actual odd-prime Euler product and bounds the finite correction below by one. It derives growth of `C(N) N / (log N)^2`, then discharges the unit-absorption premise of the numerical transfer. These additions still require compilation and the full CI audits. The resulting concrete transfer retains the actual Chen count lower estimate and bad-count upper estimate as explicit, unproved analytic inputs.

## Outstanding mathematical work

- Complete kernel recheck and transitive axiom audit of the seven compiled initial core modules. The first full build succeeded, but the subsequent leanchecker stage exceeded the 45-minute job budget and the axiom stage was skipped.
- Compile and audit the new normalization, concrete transfer and half-product geometry modules.
- Prove the asymptotic bad-semiprime removal bound.
- Formalize the actual distribution and strengthened sieve interfaces, with all uniformity and order-of-limits hypotheses.
- Formalize the geometric and analytic meaning of the numerical certificates. Nine required author/independent/final-transfer replays have completed with matching mathematical fields, including the full extended run. This does not establish every analytic/table dependency in the package.
- Prove the separate Chen lower count and then deduce the final every-sufficiently-large-even-N conclusion.

The external-input exponent 0.74774 additionally requires the published 1.9728 Chen count; it is not an axiom in the verified core.

## Frontier interpretation

The proposed separate exponent 0.76407 improves the directly stated Li-Liu 0.9 theorem and 0.894 remark, if the draft is valid. It does not improve the manuscript's 0.749 deduction from accepted published inputs plus localization. The proposed external-input exponent 0.74774 improves that specific numerical deduction. No global priority or best-possible claim is made.

## CI contract

A green build means only the committed core compiled. CI also rechecks with leanchecker and audits transitive axioms under ImbalancedChen, allowing only propext, Classical.choice and Quot.sound. No custom analytic axioms, sorryAx or native_decide trust extensions are accepted.
