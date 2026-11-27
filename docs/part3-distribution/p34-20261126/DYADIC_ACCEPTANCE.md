# P3.4 exact dyadic assembly and short endpoint acceptance

## Accepted source and independent receipt

Published source **`e84c5a1c2f70f983de7bafc80472fa2d2eb947d0`**, tree `fca71215e562bfe8ee5a48c0de3d59589a94b2e2`, passed the nine-module P3 scope in task **`5e2f28aa60a64f3dbd7b5ea1db7a0e06`**, exit 0. This combined task ran the four-module primary gate and the nine-module dyadic gate in separate clean worktrees, taking 283.236 seconds in total. The dyadic run passed **58/58 stages**, including nine strict compilations, nine bundled kernel replays and all **168 declaration records**.

The dyadic worktree began with zero project `.olean` files. Its post-run inventory contains exactly the nine project objects below. Shared dependencies were the pinned external package cache. No unrelated project object was used to satisfy the parser regression tests or any actual theorem import.

| Module, in dependency order | Owned declarations |
|---|---:|
| `Part3FourierModeIndex` | 1 |
| `Part3CoprimePacketCore` | 23 |
| `Part3CuspPhaseCore` | 7 |
| `Part3CoprimePacketCoefficients` | 16 |
| `Part3PrimaryPrimeSupport` | 11 |
| `Part3LiteralReciprocalSource` | 24 |
| `Part3FixedRhoPrimaryFiniteCore` | 22 |
| `Part3PrimaryDyadicShortEndpoint` | 26 |
| `Part3PrimaryDyadicAssembly` | 38 |

The complete inventory includes definitions, theorem constants, private helpers and generated constants. Its only transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. The auditor compares the serialized constant inventory with the actual defining-module inventory. A fresh independent rebuild of the external Mathlib closure is not claimed.

## Exact mathematical content

The new cores reuse the original two `Part3ZActualPrimary*` source prefixes under their old namespaces. The computed key records the primary multiplier, sign and ceiling base-two logarithm of the absolute output. A source's key depends only on its joint output, so all terms contributing to a given beta value lie in the same key fibre.

The resulting identities are `finite_source_assembly`, `finite_beta_assembly` and `finite_beta_energy_assembly`. In particular, the sum of squared norms is an exact identity: it has no multiplier equal to the number of blocks. The identities use the original finite weighted beta, including cancellation within its fibre.

The strict-lower/closed-upper interval convention is preserved. At dyadic index zero the output scale is `1/2`, allowing the nonzero integer magnitude one. `nonempty_endpoint_bounds` uses a nonzero actual beta to obtain a genuine source witness and derives `1/2 <= U/nu`. `short_nonzero_index_eq_one` and `assembled_short_index_eq_one` derive natural index one when `U/nu < 1`, with the original positivity and support hypotheses. Here the Lean output-scale variable `U` corresponds to the manuscript's `Y`.

The signed statements retain the negative-output case before passing to the natural absolute quotient. `signed_beta_block_eq` and `assembled_beta_coprime` supply the existing packet's beta and coprimality gate. The already existing archived `rowPacket_beta` and `rowCoefficient_eq` consumers can use these same declarations once their genuine original data closure is available.

## Source reuse and repairs

`DYADIC_PRIOR_WORK_AUDIT.json` records the original source-only registration and bounded checks of neighboring P3.1/P3.2/P3.5 acceptance. This unit does not reimplement the accepted common functional or continuous exhaustion results.

`DYADIC_DECLARATION_MOVES.json` binds all 48 original declarations: 20 short-endpoint and 28 assembly declarations. All 47 original public qualified names and their statements are preserved. The original private `finite_singleton` helper is promoted once with the same type and body so its retained parent consumer can resolve it. Forty-two proof bodies are unchanged; six repairs address the pinned Lean API, simplifier or strict linter. The independent review checked all 48 target type/owner fingerprints and all eight retained parent blocks. The five short-parent and three assembly-parent consumers themselves are outside this nine-module compilation scope.

The original local source `ca06f1264eb7e098f9c1f21e3174ea059b2d61e9` and published `57feba1f98b8411e39f50589d05f649b70c94dc5` have identical tree `b44520eee77b18d80a38d95e937ab812581f98ac`. That exact local gate also passed 58 stages and 168 declarations. Its parser regression had access to an older out-of-scope Gamma object; the local evidence is retained with that limitation. The repaired fresh run above resolves this reproducibility issue without changing theorem sources or the Lean auditor.

Cloud task `26eb31538a9d4dd09f657a273b194aed` was cancelled by the coordinator before acceptance so the corrected harness could be tested in empty project-object directories. It is neither a successful receipt nor a proof failure. Its metadata is retained in `dyadic-cancelled-cloud-task.json`.

## Reproduction and artifacts

At a clean checkout of the accepted source, with the frozen toolchain and pinned dependency cache:

```sh
python3 verification/verify_p34_primary_dyadic.py \
  --expected-head e84c5a1c2f70f983de7bafc80472fa2d2eb947d0 \
  --output-dir .lake/p34-dyadic-clean-acceptance
```

`dyadic-clean-cloud-report.json` contains the exact source hashes, commands, return codes, resolved imports, tool and object hashes. `dyadic-clean-cloud-verification.zip` contains all 62 output files and has SHA-256 `e6c2232cf67ab6573a63bdeb5ffba04b436228d39f1dcf4a25ef1619d713101c`. Its archive manifest binds every member, including the declaration inventory, raw audit, complete types and fresh-project-object inventory. `fresh-cloud-task.json` preserves the actual combined command and service outcome.

`DYADIC_IMPLEMENTATION.md`, `DYADIC_REVIEW.md`, `FINAL_HARNESS_FIX.md` and `FINAL_HARNESS_REVIEW.md` record implementation, independent review and the scoped harness repair. The original local receipt remains in the separately named `dyadic-local-*` artifacts.

## Scope boundary

The manuscript correspondence is the signed output support and coefficient norms around lines 676–687, the coprime coefficient near line 722 and the minimum regular length at line 999 of the frozen 1106 appendix. This is finite manuscript algebra. It does not construct `OriginalData` or `FixedBlock`, identify a fixed-height Fourier integral with a spectral `R(n)`, prove the oldform multiplier bound, or close P3.4. [The remaining boundary](REMAINING_BOUNDARY.md) records the exact integration obligations and available work to reuse.
