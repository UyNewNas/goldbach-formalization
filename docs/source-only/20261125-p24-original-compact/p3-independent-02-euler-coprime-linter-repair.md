# P3 independent-02: finite Euler and coprime recentering lint repair

Status: source repair prepared; actual strict compilation remains pending.
No compiler, cloud job, kernel replay or Git commit was run by this repair.

## Actual failure and existing-work check

The root supplied the actual P3 `symbolic-independent-02` partial log at
`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p3-independent-02.in-progress.log`,
compiled from `dc6cb9c65fdc51f9694e93affd2766f3bfb4649a`.
Only the eight reported strict-linter sites in `FiniteSieveEuler.lean` and
`CoprimeRecentering.lean` are changed.

Before editing, both modules' own source SHA values matched their successful
schema-2 rows in the existing 619-record registry, SHA-256
`ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`.
They were initially retained. A complete recursive project-source check then
showed that neither old compilation context matches the current closure:

- `FiniteSieveEuler -> FiniteSieveModel`.
- `CoprimeRecentering -> CurvedRegionDiscrepancy -> FiniteSieveModel`.

`FiniteSieveModel` has current source SHA-256
`3bda22d12455339b6678ebd14830379e79f488ebfee9605db2927af26529a594`,
whereas its old record requires
`9112139c826b1ebf81b12d69b873c179a2cbd6e17305ec3d0818032fb34bfb0c`.
All records in these 11- and 10-module closures have exit code zero and matching
direct project dependency-name sets; the ancestor source mismatch is the
specific blocker. Original cache gates remain unchanged.

The pre-edit six-module source-closure report is
`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p3-independent02-six-record-source-closures.json`,
SHA-256 `ab5861ff62c9777cdff1d5491f9e6599b3c1dfe503ea86c6675a780e78fdb0c6`.
It is a source-graph report only, not physical object or cache acceptance.

## Exact changes

Original line numbers refer to the diagnostic source above.

- FiniteSieveEuler 125, 134 and 145: replace the reported unnecessary
  `<;> ring` sequencing with a following `ring` tactic.
- FiniteSieveEuler 237: remove the reported unused `ring` after `field_simp`.
- CoprimeRecentering 124 and 137: replace the reported unnecessary
  `<;> ring` sequencing with a following `ring` tactic.
- CoprimeRecentering 161: remove the reported unused `ring`.
- CoprimeRecentering 231: remove only the reported unused `eq_self_iff_true`
  simp argument.

## Manuscript and preserved formulas

Read the existing frozen 1106 manuscript at commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/argument.tex`, the literal density following
  `eq:current-upper-exit`, and the exact coprime means in
  `eq:current-aux-sw` and `eq:current-PP`.
- `paper/release-20261106/en/sieve-appendix.tex`, `sv:euler-ratio`.

The finite Euler identity retains its strict prime cap, exclusion of primes
dividing N, explicit leading factor two, real subtraction, and the same
odd-prime correction. The recentering identities retain the actual totient,
exact coprime mass, signed weights, modulus-one case and the factor-two error
bound. No formula, hypothesis, range, definition or theorem statement changes.
These failures concern tactic presentation and redundant simp arguments;
this repair introduces no mathematical deduction or new manuscript claim.

## Static verification

The complete postimages equal the base files with precisely the eight listed
transformations. All 30 theorem headers and all six complete definition blocks
are byte-identical, as are imports. No forbidden proof token or linter
suppression was added. `git diff --check` passed for both source files.
These static checks do not claim that the strict Lean retry has passed.

| File | Before SHA-256 | After SHA-256 |
| --- | --- | --- |
| `ImbalancedChen/FiniteSieveEuler.lean` | `d1eb27002ef3da1327a4574067241a26fd825a6e50c1cd9b530b4ace21db42f7` | `11bdebafbc88500f92b9c2ffa765731c1fa0a09928432f3145cea51c72db344d` |
| `ImbalancedChen/CoprimeRecentering.lean` | `45c28d97bd10eccaa99498b2309fb03c9d8efbdd5040e12d7ba33c3702b418c5` | `c3828810105d1d79fc57a732873470bf0a6372574205cab4658a266b80db8c43` |
