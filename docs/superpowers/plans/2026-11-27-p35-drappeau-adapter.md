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

- [ ] Establish the proposed auxiliary consumer RED/GREEN sequence; not completed (see execution evidence below).
- [x] Implement using the existing derivative and supremum proofs.
- [x] Run strict compilation, complete axiom/type inventory and kernel replay.

## Task 2: Cubic envelope into existing height payment

**Files:** `ImbalancedChen/Part3DrappeauRegularEnvelope.lean` and a full-type consumer.

**Consumes:** `regular_cutoff_absolute_payment`, `continuous_cutoff_payment`,
`integrable_exhaustion_of_cut_bound`, `regularBase_pairBudget_le`.

**Produces:** the finite and positive-measure regular bound
`260*E*sqrt(((1+Y^2+u)*A2)*((1+Y^2+v)*B2))` from the separate primitive
cumulative bounds and `E*min 1 ((1+Y*sqrt Y)/(1+|t|^3))`.

- [ ] Establish the proposed auxiliary consumer RED/GREEN sequence; not completed (see execution evidence below).
- [x] Prove the scalar conversion and `64*E` tail bound; reuse all existing shell sums.
- [x] Apply to finite cuts and positive measures, including proved global L1.
- [x] Run strict compilation, complete axiom/type inventory and kernel replay.

## Task 3: Evidence and remaining-source boundary

- [x] Add the exact external reference, native normalization correspondence and source-search scope.
- [x] Independently review all new statements and compare exact bytes with compiler inputs.
- [x] Publish the accepted source at `44743fb463011127f66274f197ff38bf4680c192` and read back its head.
- [x] Preserve complete P1/CI acceptance evidence for publication in the following evidence-only commit.
- [x] Record P3.5 as OPEN; do not add it to the closed-node Draft unless its full obligations are met.

## Execution evidence and deviations

The initial auxiliary consumer probes failed because imported objects were
missing. They did not establish a meaningful missing-feature RED result, and
no auxiliary consumer GREEN run is claimed. Final acceptance instead checks
the actual two modules, every serialized declaration and its full type, with
strict compilation and kernel replay in both P1 and CI. The fresh reviewer
checked the terminal types against the requested quantifier and input boundary.
This records a deviation from the proposed consumer sequence, not a completed
TDD cycle.

A separate minimal expression probe did establish a real RED/GREEN case:
implicit complex coercion of an inverse prevented the expected real-norm
rewrites; explicit `Complex.ofReal` of the real inverse fixed the three
expressions. This is an expression repair, not a theorem or parameter change.
The scalar conversion prefix also passed a scoped strict probe. Neither probe
is presented as full module acceptance.

The complete evidence is under
`docs/part3-distribution/continuation-20261127/drappeau-adapter/`.
P1 passed 35/35 formal stages; CI run `45953060136` passed 36/36. Both audited
28 declarations (24 theorem records, 4 definitions), with only `propext`,
`Classical.choice` and `Quot.sound`. Their full types are byte-identical and
all 6,695 imported source hashes agree. The remaining actual-transform,
native-row and final-assembly obligations stay OPEN.

## Execution rulings

The existing user request authorizes continued implementation and GitHub
publication. No further plan or worktree confirmation is needed. P3/fallback
MCP sessions were unavailable. The local isolated bootstrap stopped after
182 old dependency modules and is not acceptance evidence. P1 subsequently
provided the exact pinned cache and completed the formal verification in an
isolated checkout; GitHub CI independently passed the normal Lake route from
an initial project cache miss. Neither route changed dependency pins or proof
acceptance gates. The accepted branch is retained; no full-node merge is made.
