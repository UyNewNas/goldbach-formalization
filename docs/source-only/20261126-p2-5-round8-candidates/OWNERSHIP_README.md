# Round8: the two remaining Full87Ownership reductions

The selected candidate changes only `source_kind_rows`, in its
`remaining.ascending i` and `remaining.seed` branches. Both proof continuations
passed the targeted local Lean diagnostic. The complete module, independent
kernel replay and owned audit remain pending.

## Selected source and unchanged contract

| Item | SHA256 |
| --- | --- |
| Original round7 source | `a0b20f9f98e92a33396d8078700895bb564feb2911b9689bd6b544b30322841a` |
| Selected round8 source | `1023637bdce71f2cfb2d2f9fd05ddfb1bba0174de8ae51044a9ad87a15c1e332` |

The candidate is `after/ImbalancedChen/P4AOriginalFull87Ownership.lean`.
`P4AOriginalFull87Ownership.patch` contains the complete delta.
`OWNERSHIP_IDENTITY.json` records all 15 unchanged theorem headers and all nine
unchanged definition, abbreviation and instance blocks. Imports, options,
original `Source` premises, affine data and every other proof branch are
unchanged. The 49 previously repaired row instances were neither changed nor
recompiled.

Each selected branch makes the same two edits:

```lean
dsimp [P4AOriginalRemainingEighthSources.commonSlack] at hh
```

replaces `dsimp only`, and the existing `norm_num` list includes

```lean
Finset.sum_pair (by decide : (0 : Fin 8) ≠ 7)
```

The application `source_common_pos h 17` is unchanged. The finite `decide`
expression proves only that two concrete `Fin 8` elements differ; it introduces
no axiom or host correctness assumption. No `sorry`, `admit`, `native_decide` or
`unsafe` appears in the candidate.

## Why these reductions suffice

For these two original families, the source definitions give
`selected = {0,7}`, `descendingNew = false`, and
`newCap = A(selectedSum) - eta`. Entry 17 of the original 35-entry `commonSlack`
vector is therefore

\[
C(S)-\eta-(A(S)-\eta)
=C(S)-A(S)
=\frac{25}{64}-2S
=2(\mu-S),\qquad S=t_0+t_7.
\]

Its strict positivity gives precisely the existing `KindRows 0` conclusion
`t 0 + t 7 < mu`. The manuscript's 1106 `argument.tex`,
`sec:current-upper`, defines `mu = 25/128` and the two affine tent branches.
`sieve-appendix.tex`, `sv:selected-gate` and `sv:tent`, defines the selected sum
and this tent. Its `sv:branch-licence` and `sv:eighth-range` retain the support
and ancestor restrictions. The row index 17 and zero-based selected slots are
read from the exact existing Lean source dictionary; they are not presented as
literal row numbers from the manuscript prose. Full manuscript file hashes are
recorded in `ownership-diagnostics/MANIFEST.json`.

The failure is an expression-reduction problem. There is no new mathematical
hypothesis or missing analytic estimate in these two steps.

## Observed diagnostics

The fixture copies 26 existing definition slices, including the **entire**
35-entry `commonSlack` vector. It starts at the already-proved conclusion of
`source_common_pos h 17` and checks exactly two continuations: arbitrary
`i : Fin 14` in the ascending family, and the seed family. It does not replace
the complete module's `Source` premise or claim to revalidate its row theorem.

| Diagnostic | Exit | Seconds | Observed result |
| --- | ---: | ---: | --- |
| Original continuation | 1 | 18.506 | Two `linarith` failures; vector index 17 and the finite sum remain unreduced. |
| First minimal attempt | 1 | 3.475 | Vector projection reduces, but the conditional insert/singleton rules leave the finite sum. |
| Selected final continuation | 0 | 5.089 | Both cases pass; log is empty. |

The first attempted candidate, SHA
`bf458ad6fdc814c43aa6d3ca13fb456408c98674d365dc3a028d82e67fc86e02`,
is retained separately under `failed-attempt1/`; it is not selected. Its source,
log and actual result record remain in `ownership-diagnostics/`. The final
fixture is `CommonSlack17Final.lean`; its actual record is `FINAL_RESULT.json`.

All runs used the existing local Lean 4.33.0-rc1 runtime and Mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, two threads, and the CLI options
`warningAsError=true`, `maxRecDepth=50000`, `maxHeartbeats=40000000`.
For precise accounting: the original extracted `KindRows` slice also carried
the following `set_option maxHeartbeats 0 in` into the first example of the
preserved baseline and first failed fixture. Both genuinely failed. The final
fixture removes that trailing command, so **both successful final examples use
the finite CLI heartbeat limit**. Production options remain unchanged.

`FIXTURE_EXTRACTION.json` records exact source slices and this option scope.
`MANIFEST.json` binds all three actual source/log/result sets, the declaration
identity record and the complete candidate delta. No full-project rerun or
remote compilation was performed. The new local success earns no full-module,
Q96 or P2.5 acceptance by itself.
