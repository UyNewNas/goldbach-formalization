# P3.1: actual mode coefficient and finite label budget

This increment connects the original actual mode coefficients to the accepted common-cutoff estimate for the six smooth completed pieces. It also bounds the original finite label budget by the actual carrier sizes. The whole P3.1 target remains open.

**Fixed-commit formal acceptance passed** at source commit `c2f98c664fc825e0f09324d785cee5721c57ef58` (tree `a900e0a0d5b8c4de1a37be945728b59698e54932`), task `job_fc4362307dc04c37a5e1c2a96b675bed`. All 40 stages passed, including four strict compilations, four individual bundled-kernel replays, the complete 68-declaration inventory, the three-axiom gate, and full source/object binding. The 81 previously accepted provider objects remain byte-identical to the preceding acceptance. This evidence-only descendant changes no accepted Lean source or verifier. See `ACCEPTED_SCOPE.json`, `RUN.json`, `verification/report.json`, and the independent review records. Development attempts are retained separately.

## Mathematical result

For every natural `r >= 2`, there is a positive constant `A`, chosen before all scales, atoms, modes and signs. For positive `B`, `C`, `x`, any real `epsilon`, and the original admissible actual mode coefficients, use the same cutoff

\[
J=\left\lceil(C/B)x^\epsilon\right\rceil.
\]

Put

\[
T=\operatorname{baseCarrier}(e,D/\delta),\quad
H=e.\operatorname{sharedSmoothFrequencyBound}(Z,D),\quad
F=\operatorname{scaleF}(e,D,g).
\]

The new consumer bounds the difference between the accepted actual six-piece smooth mass and its common finite truncation by

\[
(6A10^{r-1}C^2)\,
\operatorname{rawLabelBudget}(T,H,F)\,
x^{-\epsilon(r-1)}.
\]

The finite budget satisfies

\[
\operatorname{rawLabelBudget}(T,H,F)
\le (2F+1)\bigl((e.Q2+1)(2H)\bigr)^2,
\]

and the final theorem substitutes this explicit bound. The closed signed `f` interval includes `f = 0`; its endpoint allowance is retained. `B,C` remain explicit positive scales and `Z` remains the actual cutoff parameter. A uniform original-family error estimate requires the additional identifications and payments listed below.

## Source and proof boundary

| Module | Role |
|---|---|
| `Part3ActualModeCoefficientNormsCore` | Minimal recovery of original actual coefficients, their phase/mask definitions and their norm bounds |
| `Part3ActualHardTailLabelBudget` | Original ordered-label budget and mass estimate, plus finite source-mass monotonicity |
| `Part3ActualLabelBudgetCardinality` | Original interval/frequency counts and the actual finite cardinality budget |
| `Part3ActualModeSmoothMassTail` | Finite composition with the accepted six-piece tail and exact cutoff substitution |

The coefficient definitions preserve original `gamma2` outside branch conjugation, the period-64 Fourier phases, the inverse amplitude, the exact shortened signed frequency block, and the residue-class indicator. The actual coefficient bounds are derived from these definitions and `MediumAdmissible`; the public actual-mode tail results have no added coefficient norm premises.

The analytic tail estimate is reused from source commit `a7e34b33f540dff1e507909f8ba42cea446e87cb`, with acceptance recorded at `e63206af301eb31c3518794fe5f9a1816e61f3b6`. All 81 previously accepted project provider sources are preserved. Earlier donor compilation evidence is distinguished from this round's strict/replay acceptance of newly extracted module owners.

`SOURCE_INTAKE.json` and `SOURCE_FRAGMENTS.json` pin every donor and retained fragment. Existing exact donor archives are reused when already committed. `SOURCE_DECLARATIONS.json` distinguishes the 37 recovered source declarations, including the original named local instance, from 11 new finite proofs. Generated Lean declarations are counted separately after compilation.

The single recovered-proof adjustment removes a redundant trailing `ring` after `simp` has closed the original cardinality equality. It is individually allowlisted in `MECHANICAL_REPAIRS.json`. Development adjustments to new proofs preserve their statements and are recorded separately.

## Verification contract

The `actual-mass-budget` group extends `verification/verify_part3_continuation.py` through one isolated intake validator. Existing groups, shared source/object checks, baseline preservation, strict compilation, individual bundled-kernel replay, complete declaration inventory and transitive-axiom checks are unchanged.

The selected project import closure has 85 modules: four integration targets and 81 unchanged accepted providers. The formal gate compiles and kernel-replays the four targets, binds all reachable project sources and resolved object parts, and checks that provider objects stay frozen. This does not claim a fresh individual replay of every historical provider or every external Mathlib import.

## Remaining P3.1 obligations

The new bound does not yet pay the complete original family. The next connection must use the true actual scales, the licensed upstream cutoff choice, the original outer mode and label recombination costs, and the return to the original supported row and `signedError`. Source-zero and Poisson-zero payments remain distinct. External spectral J/A inputs retain their existing boundaries.

`NEXT_FAMILY_BUDGET_SOURCE_AUDIT.md` identifies the original `Z = x^eta` construction, its earlier smoothing-error payment, and the elementary geometry needed for a coarse polynomial budget. That theorem uses `cleanedAlphaAtom`; this dictionary must be retained. The Lean smoothing cutoff parameter named `Z` is distinct from the manuscript's later spectral level length. This source audit is a next-step guide, not an acceptance claim for that larger dependency closure.
