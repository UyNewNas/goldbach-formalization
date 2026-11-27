# P3.5 Drappeau adapter implementation plan

> **For agentic workers:** Execute the independently scoped tasks in this session. Use verification-before-completion and a fresh whole-change review.

**Goal:** Complete the remaining C4 normalization and cubic-envelope conversion required to apply the manuscript's cited regular Bessel input.

**Architecture:** Reuse the accepted actual test, Fourier, shell and measure-exhaustion modules. Add two narrowly scoped modules and validate their complete declaration inventory. Keep actual-row and external-input boundaries visible.

**Tech Stack:** Lean 4.33.0-rc1; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; goldbach `09b97db5764ade1246bfb77206baa1b124760958`.

**Spec:** `docs/superpowers/specs/2026-11-27-p35-drappeau-adapter-design.md`.

## Global constraints

- Frozen manuscript 20261106; preserve parameter ranges and signed normalizations.
- Do not repeat accepted proofs or formalize outside Bessel/spectral theorems.
- No sorry/admit/new axiom/native_decide/unsafe; unchanged dependency pins.
- Compile, replay owned objects and audit all owned declarations before acceptance.
- Do not count conditional adapters as closure of the actual P3.5 spectrum.

## Review focus

- `Y` may be arbitrarily small or large; do not assume `Y<=1` or `Y>=1`.
- The constant precedes the Fourier mode, scale and physical parameters.
- Unit normalization is strictly positive, including the zero Fourier mode.
- The low cut includes height zero; the high tail is genuinely summable.
- Integral bounds include local L2 and proved global L1, preventing totalization shortcuts.

## Task 1: Actual normalized C4 test family

**Files:** `ImbalancedChen/Part3ActualSpectralTestNormalization.lean` and a full-type consumer.

**Consumes:** `spectralTest`, `spectralTest_contDiff`, `spectralMode_support_subset`,
`testSeminorm`, `le_normalizedJetSup`, `actual_uniform_testSeminorm_budget` and the
existing actual Fourier weighted budget.

**Produces:** positive normalization; original-test reconstruction; compact
support in `[Y/16,16Y]`; unit normalized derivatives for every `n<=4`; Fourier
summability and a common degree-28 cost.

- [ ] Freeze consumer theorem types and record the missing-feature failure.
- [ ] Implement using the existing derivative and supremum proofs.
- [ ] Run strict compilation, complete axiom/type inventory and kernel replay.

## Task 2: Cubic envelope into existing height payment

**Files:** `ImbalancedChen/Part3DrappeauRegularEnvelope.lean` and a full-type consumer.

**Consumes:** `regular_cutoff_absolute_payment`, `continuous_cutoff_payment`,
`integrable_exhaustion_of_cut_bound`, `regularBase_pairBudget_le`.

**Produces:** the finite and positive-measure regular bound
`260*E*sqrt(((1+Y^2+u)*A2)*((1+Y^2+v)*B2))` from the separate primitive
cumulative bounds and `E*min 1 ((1+Y*sqrt Y)/(1+|t|^3))`.

- [ ] Freeze consumer theorem types and record the missing-feature failure.
- [ ] Prove the scalar conversion and `64*E` tail bound; reuse all existing shell sums.
- [ ] Apply to finite cuts and positive measures, including proved global L1.
- [ ] Run strict compilation, complete axiom/type inventory and kernel replay.

## Task 3: Evidence and remaining-source boundary

- [ ] Add the exact external reference, native normalization correspondence and source-search scope.
- [ ] Independently review all new statements and compare exact bytes with compiler inputs.
- [ ] Commit source and acceptance evidence, push existing P3.5 branch and read back its head.
- [ ] Report P3.5's actual remaining status; do not add it to the closed-node Draft unless its full obligations are met.

## Execution rulings

The existing user request authorizes continued implementation and GitHub
publication. No further plan or worktree confirmation is needed. Isolated
local compilation replaces unavailable P3/fallback MCP sessions; this changes
the evidence location, not the dependency pins or proof acceptance gates.
