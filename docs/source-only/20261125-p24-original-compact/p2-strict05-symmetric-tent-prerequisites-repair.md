# Strict 05: symmetric tent prerequisite proof repair

Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

The complete strict05 log for Lean source `ed3b1667` is
`p2-strict-symbolic-05.log`, 17,467 bytes, SHA-256
`d16e52df7542486074b3ccadc65abca416f372283e7f7c34cfe7e20271d841e4`.
It reports 283/321 successful modules (276 reused, seven fresh), no pending
modules, and four direct failures. This repair concerns only
`ActualThirdOriginalP4ASymmetricTentPrerequisites.lean`.

## Mathematical scope retained

The already frozen 1106 `certify_extended_prefix.py` was rechecked at the six
affine choices, symmetric geometry, and OLD/NEW chord construction (SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`,
manuscript source `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`). The existing
formal prism supplier retains coordinate order `x = max`, `y = min` and the
true ordered mean. Its explicit difference from the producer's square mean
is preserved, including the `.xz / .fall` case. Equality of the two means
is still restricted to the existing balanced coefficient cases `.xy` and
`.xyz`; no general equality or leaf bound is assumed.

The original ascending-test priority, the descending branch's failed
ascending test, root filter, positive residual, exact Fraction endpoints,
reader queries and all strict/weak boundaries remain unchanged. The frozen
producer check establishes this semantic correspondence; it does not newly
authenticate a different historical P160 producer.

## Actual failures and local repairs

| Input proof site | Repair and classification |
|---|---|
| Lines 119/293, z-coordinate nonzero premises | Use `change` to expose `p.2` or the real cast of `z`, then apply the existing positivity proof. Definitional finite-vector reduction. |
| Line 160, four constructor-disjointness goals | After the existing numeric simplification, eliminate each impossible constructor equality with `cases`. This completes finite cases; it needs no new `DecidableEq` instance or native computation. |
| Lines 297/299/301 and 355/357/359, stored-row bindings | After `fin_cases`, explicitly change each goal to its scalar coordinate equation, then retain the original rational-cast proof. |
| Line 430, branch guard | Split the existing `k` into rise/fall and use the original hypothesis directly. Apply the same reduction to the adjacent root/residual transports. This resolves the dependent `match k, hD` representation without changing any test. |

## Loss of the old style exception

The log records a baseline-only `unusedSimpArgs=false` exception for the old
source. The modified source receives no such exception. Separate from the
actual errors above, repeated Matrix simplification lists were removed from
this file's three basic vector proofs and mean-difference proof. The basic
proofs now use their existing coordinate facts after `fin_cases`; the mean
proof uses a scalar `change`, unfolds the same mean definitions, and retains
`ring`. The query/cast and positive-grid simplifications were retained where
their premises explicitly contain the corresponding terms. This is a static
assessment; the new strict-lint run remains necessary. No gate or option was
changed, and no unrelated file was edited.

## Preservation and source identities

Comment-aware comparison against `ed3b1667` confirms byte-identical imports,
20 public theorem headers, three private theorem headers, and all nine
complete computational definitions. `git diff --check` passes. No new
hypothesis, admitted proof, axiom, unsafe declaration, native evaluation or
linter setting was introduced.

- Before SHA-256: `ee22689368b3090db22c039afa204179643629746499422e5c87855d53fec7bd`.
- Candidate SHA-256: `a2dbdc8fa6cff825a6e8e8b86a60b30c81b06930c78890e0d928a8c5f042bbc1`.

No Lean compilation, remote task, index operation or commit was performed
for this repair. The candidate has no new compilation, kernel, finite-check
or endpoint-completion credit.
