# P3.5 actual test seminorm continuation

## Authority and scope

Continue the user's authorized P3.5 work and submit it to the existing dedicated
GitHub branch. The mathematical specification is the 1106 appendix, repository
`UyNewNas/chen-imbalanced-semiprimes`, commit
`a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/analytic-appendix.tex`, especially A.5 lines 705–717
and the external input registration at 1025–1028. The accepted whole-height
component at `94cff537f2e60173aaf936c2345d5af0ee5e6585` is reused.

Starting head: `5285d4f5d8c40eddf92c108b492c909de8b43cef`.
Working tree: `/workspace/scratch/b1f8de8cd1b9/goldbach-p35`.
Branch: `codex/p3-5-full-kernel-20261125`.

## Global Constraints

- Reuse reliable existing work. Do not implement already existing proofs anew.
- Prove only manuscript derivations; ABL, KS and Pascadi remain external inputs.
- No `axiom`, `sorry`, `admit`, `native_decide` or `unsafe` proof escape.
- Keep the toolchain and dependency pins unchanged. Do not change accepted proofs.
- On difficulty, check the corresponding manuscript passage and distinguish a
  formal-expression issue, a fillable omitted derivation, and a substantive gap.
- Only the newly owned modules receive strict compilation, bundled kernel replay
  and complete declaration/type/transitive-axiom acceptance. Existing accepted
  dependencies retain normal imported-environment trust and historical receipts.
- Do not claim this component closes P3.5 or proves the actual positive/negative
  Bessel transform estimates, or that derivative order four suffices for Pascadi.
- The controller coordinates P3 cloud jobs and GitHub commits. Do not alter other
  tasks' local or cloud workspaces, or use P1/P2 without a concrete need.

## Task 1: actual derivative suppliers and per-mode supremum budget

**Ownership:** create only these two Lean files:

- `ImbalancedChen/Part3ActualSpectralTestJets.lean`
- `ImbalancedChen/Part3ActualSpectralTestSeminorm.lean`

No git commit or cloud MCP call by the implementer. Notify the controller when
ready for a diagnostic build, then repair only errors from that build. Record
donor excerpts and repairs in the task report; the controller owns provenance
files and the final verification. Do not spawn subagents.

**Existing sources (read-only donor):**
`/workspace/scratch/e5a460f2108f/goldbach-p25`, commit
`52098e403ac4b28c72ec5958fd738ae93d785ac5`.

1. `docs/source-only/20261102-resume-30m/exceptional_j_large_scale/Part3ActualExceptionalJLargeTransform.lean`,
   blob `43fe6493d1a4c90a252ed163aa14572ebe9e44ad`: reuse `modeFrequency`
   (lines 33–34), `phase_hasDerivAt` (50–63), `modeFrequency_norm_le` (136–142),
   retaining namespace `ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102`.
2. `docs/source-only/20261102-resume-30r/full_modulus_test_support/Part3OriginalFullModulusTestJets.lean`,
   blob `d4ce9301a7c98f117937e614ca29577c09e98d19`, SHA-256
   `cf4c4840f8bcdfa778848bb1ded656636dccf5e249e9f957092955a5f7b262dd`:
   reuse private `iteratedDeriv_tsupport_subset` (47–54) and the declarations
   in lines 101–257, `complexChi` through `spectralTest_jet_bound`, retaining
   namespace `ImbalancedChen.Part3.OriginalFullModulusTestJets20261102`.
3. `docs/source-only/20261102-resume-30s/S/s22_actual_spectral_energy/Part3OriginalUniformTestCutoffBudget.lean`,
   blob `4ed252e2956690d46848cb14b4f8253a88050610`: reuse the definition
   `finiteTestJetConstant` and its positivity theorem if helpful. Preserve their
   namespace `ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102`.
4. The existing syntax repair at
   `docs/source-only/20261112-resume/t03/abel-lift-next/TEST_JETS_SCOPE.patch`,
   blob `4d8ccd525446ad28cde6a396b0d345e3b987ca9c`, opens `ContDiff` scope.

Use exact source proofs, adapting only imports/scopes and actual compiler
diagnostics. Do not import the old overbroad M/R20/S22 module graphs. Preserve
original public declaration names, mark the module as selected declaration reuse,
and explain that the whole historical modules have not thereby been accepted.

The minimal supplier imports are:

```lean
import ImbalancedChen.Part3NativePeriod64Reconstruction
import ImbalancedChen.Part3ActualWeightedSpectralBudget
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
```

The two project roots have a 55-module closure already present with identical
bytes. The controller has its hash manifest. Existing APIs are in namespaces
`P3Period64NativeReconstructionSourceOnly`,
`P3NativePeriod64SamplingSourceOnly`, and
`P3ActualWeightedSpectralBudgetSourceOnly`. Inspect the exact statements.

**New mathematical result:** for the actual `spectralTest ell Y`, define

```text
normalizedJetSup n ell Y = sSup (range (q ↦ Y^n * ‖iteratedDeriv n (spectralTest ell Y) q‖))
testSeminorm d ell Y = ∑ n ∈ range(d+1), normalizedJetSup n ell Y.
```

Prove each range nonempty and bounded above when `0 < Y`, prove the sup is
nonnegative and dominates every point, and prove

```text
testSeminorm d ell Y ≤ finiteTestJetConstant d * (1 + |(ell 0 : ℝ)|)^d.
```

Reuse the old all-order `spectralTest_jet_bound` and the already accepted actual
Fourier weighted L1 theorem. The final theorem must have the following quantifier
order and actual data, with no added Fourier summability or derivative hypothesis:

```text
∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
  ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
  ∀ Y : ℝ, 0 < Y →
  Summable (ell ↦ ‖actualCoeff rho sigma ell‖ * testSeminorm d ell Y) ∧
  (∑' ell, ‖actualCoeff rho sigma ell‖ * testSeminorm d ell Y)
    ≤ C * (1+rho)^(4*(d+3)).
```

Choose `C` before all moving parameters. Keep arbitrary fixed `d`. A supremum
outside the mode sum, or a common evaluation point, does not meet the goal.
Include only useful consumers; no duplicate six-scale/tail bookkeeping.

**Validation:** first static forbidden-token/source checks, then controller's
targeted P3 compilation. Final acceptance uses strict Lean, bundled kernel replay,
and complete owned declaration types/axioms on an exact committed head. The only
allowed transitive axioms are `propext`, `Classical.choice`, `Quot.sound`.

**Report:** write the task report beside the task brief. Include owned files,
donor ranges actually used, any repaired proof fragments, declaration inventory,
mathematical boundary, diagnostics resolved and any remaining concern. Return a
short status with the report path. The report must not claim acceptance before
the controller provides actual gate evidence.

## Task 2: provenance and incremental acceptance wiring

Controller creates a donor extraction manifest, dependency closure manifest and
source-repair patch under
`docs/part3-distribution/continuation-20261126/test-seminorm/`. Preserve old receipts.
The new group `p35-test-seminorm` in `verification/verify_part3_continuation.py`
owns only the two new modules. Validate donor identities, the exact 55 reused
dependency hashes, extraction baseline and any local repair patch. Change the
dedicated branch's workflow selector to the new group. Keep the full serialized
inventory/axiom validator and pinned configuration checks unchanged.

Validate Python syntax and source-only preflight. Publish exact candidate bytes
on the authorized branch with `[skip ci]`; P3 supplies the acceptance run. Use
the existing isolated cloud worktree `/workspace/p35-full-height-20261125`,
one CPU, `LEAN_NUM_THREADS=1`, up to 13107 MiB memory. Do not erase dependency caches.

## Task 3: compile, review, acceptance and GitHub delivery

Run focused diagnostic builds and repair genuine failures without weakening
statements. Review the implementation against the frozen manuscript and donor
provenance. On a clean exact committed head, run the new group's strict/replay/
complete-axiom gate. Retain the original machine-generated report, logs, full
declarations/types, object/source hashes and zipped evidence. Independently
review the mathematical boundary and acceptance receipt. Commit the receipt and
review to the same branch. State precisely what this component closes and what
remains open in P3.5; no overall green claim or arbitrary board count edits.
