# P3 independent-05: initial-cutoff equation API repair

## Actual input and failure

- Base commit: `90d08ca851568e6c95a44de321bc34473e395518`.
- Owned source: `ImbalancedChen/ActualExtendedThirdInitialCutoff.lean`.
- Exact diagnostic log: `p3-independent-symbolic-05.log`, SHA-256
  `27b6956d468c4cc8e706eade4f6f07a3dd3afadfe8f85bf1c79435d0c64205ec`.
- The retained module log begins midway through a failed rewrite. Its context
  identifies `initial_nonempty_continuation`: the goal contains raw `List.rec`
  terms while the induction hypothesis names `firstExitRetainedPolynomial`.
  The same mismatch is reported at line 200. At 313/314 the parity induction
  has the analogous raw recursor mismatch and an unused induction hypothesis;
  line 400 cannot expose the selected-branch conditional after a raw leaf
  recursor rewrite.
- Existing `p2-current-symbolic-source-precheck.json` classifies this module
  under `direct_failure_groups.no_record`; there is no old-619 record to retain.
  Precheck SHA-256:
  `49cf58eea08c6a391883b5a26b844c45101f31b133d31cfe754794a4cdb1b2b4`.
  No archive or CI audit was repeated.

## Minimal repair and manuscript boundary

Eleven proof-script sites now use the existing equations from
`FirstExitTree.lean`: `firstExitRetainedPolynomial_cons`,
`firstExitRetainedLeaves_nil` / `_cons`, and `evenListLength_nil` / `_cons`.
This includes the other corresponding raw unfold sites in this file, since
the diagnostic log retained only a tail. The equations expose exactly one
constructor while leaving recursive tails in the form used by the existing
induction hypotheses. The parity induction retains its original `ih`,
`Nat.even_add_one`, and `decide_not` steps. Membership construction retains
the same skip/select branches and the same `if_pos htest` test.

Classification: **formal expression / equation API compatibility**. No new
mathematical derivation, additional premise, or substantive manuscript gap
is introduced or claimed resolved by this change.

Frozen source consulted: `UyNewNas/chen-imbalanced-semiprimes`, commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/argument.tex`, the causal-prefix paragraph and
  `eq:current-upper-exit` (local lines 213–236).
- `paper/release-20261106/en/sieve-appendix.tex`, `sv:upper-cubes` and
  `sv:first-exit` (41–80), the literal first-cube cutoff reduction (248–251),
  and `sv:finite-realization`'s compact refinement and preservation of ancestor
  decisions (265–315).

The existing strict prime cutoff, zero-exponent case, dyadic floor,
ordinary full tests, selection order, parity, mass updates, and final
ordinary-plus density equality are unchanged. The exact dyadic discretization
remains the existing formal implementation of the finite policy; this repair
adds no manuscript assertion about that discretization.

## Static verification and pending gate

- All **12 theorem headers**, including private helpers, are byte-identical.
- The complete `actualExtendedThirdInitialStopExponent` definition and import
  list are byte-identical. Every edit is a theorem-name substitution in an
  existing proof script.
- `git diff --check` passed for the owned source.
- Independent read-only review by `p24_stage_closure` found no Critical or
  Important issue: it checked the existing `rfl` equations, recursive-tail
  matching, leaf membership branches, and actual use of the parity `ih`.
- Before source SHA-256:
  `47165dcc0f73cdeb8fad5f970382b934ccd58b4e8c71ec8ba47c2a6043afb7c6`.
- Candidate source SHA-256:
  `40a5a459cc297bad1c494598389f6e3ff67256b1099f02eb95be115886aae72c`.

No Lean/Lake invocation, remote job, staging, or commit was performed.
This is a source-only candidate pending the parent's actual diagnostic and
subsequent qualification/kernel gates; compile and kernel credit remain false.
