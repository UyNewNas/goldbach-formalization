# P2.10 — original Full87 Winner9: final acceptance

**P2.10's original Winner9 terminal and seed-supplier connection are accepted.**
The three final modules passed strict compilation, independent stock kernel replay,
complete owned-declaration/axiom audit, and the original evidence exporter.
The exact final export was preserved successfully. **`terminal_integrated = true`**
for this scoped P2.10 result. Verification completed on **2026-11-25 (UTC)**.

The accepted proof worktree is
[W3 `b33734e49d17d66c4069965b3d445d1da31a1f37`](https://github.com/UyNewNas/goldbach-formalization/commit/b33734e49d17d66c4069965b3d445d1da31a1f37).
A later documentation commit does not replace that proof-source identity.
The [machine-readable acceptance record](./PUBLIC_P210_FINAL_ACCEPTANCE.json)
contains the corresponding minimal actual results.

## Final gates and reuse

| Final module | Strict compilation C | Stock replay and owned audit A | Owned declarations | Export E |
|---|---|---|---:|---|
| `ImbalancedChen.P2Winner9CompleteNumericalChecks` | Existing successful C reused | Accepted | 2 | Accepted |
| `ImbalancedChen.P2Winner9CompleteSeedTerminal` | Existing successful C reused | Accepted | 8 | Accepted |
| `ImbalancedChen.P4AOriginalFull87SeedRefinements` | New successful C | Accepted | 9 | Accepted |
| **Total** | **3 valid: 1 new + 2 reused** | **3 accepted** | **19** | **3 accepted** |

The only new compilation in the final continuation was `SeedRefinements`.
The full compilation closure contains **1,015 successful modules**, with
**1,014 existing compilations reused** and no failed or pending module.
The three final replay/audit gates were new acceptances; the earlier numerical
proofs, accepted prefix, and six preparation modules were retained.

The observed transitive axiom counts are:

| Axiom | Final owned declarations depending on it |
|---|---:|
| `propext` | 19 |
| `Classical.choice` | 17 |
| `Quot.sound` | 17 |

These are overlapping per-axiom counts, not disjoint declaration groups.
No axiom outside the existing allowed set occurred in the accepted final audit.
The original strict compiler, auditor, exporter, importer, and resume-plan
sources remained unchanged.

## Closed mathematical statement

The terminal is
[`P2Winner9CompleteSeedTerminal.complete_seed_ledger_le_original_full87_nine11`](https://github.com/UyNewNas/goldbach-formalization/blob/b33734e49d17d66c4069965b3d445d1da31a1f37/ImbalancedChen/P2Winner9CompleteSeedTerminal.lean):

```lean
(adoptedLogTotal : ℝ) + (savingLower slot21 : ℝ) +
  (savingLower slot22 : ℝ) ≤
P4AOriginalFull87SourcePrimeTests.cellIntegral (.remaining (.nine 11))
```

The original seed-supplier statement is now accepted as well:
[`P4AOriginalFull87SeedRefinements.original_seed_refined_floor`](https://github.com/UyNewNas/goldbach-formalization/blob/b33734e49d17d66c4069965b3d445d1da31a1f37/ImbalancedChen/P4AOriginalFull87SeedRefinements.lean).
It supplies the bound for the original `archived seed`, followed by the same
two chronological increments. The finite checker and null-overlap facts are
supplied by the existing archive proof chain; they are not extra hypotheses
of the public terminal statement.

The original selected total is
`475741072397709744401965 / 2^96`. The two increments retain their exact values
`77410436074156865471 / 2^96` and `481322793305152847935 / 2^96`.
The manuscript correspondence is the
[2026-11-06 release](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/master/paper/release-20261106/en),
section 4.1 equation (23), Appendix F.2 and Appendix I.4–I.5.
The proof retains the original Full87 cell, density factor 4, and 97 tagged
inequalities. There is no quarter-factor or ordering-factorial alteration.

## Numerical coverage and previous acceptance

The completed chain connects **2,048 accepted historical rows + 8,978 accepted
public-CI rows = 11,026 rows**, covering 690 numerical pages and 44 check blocks.
The historical prefix and the original numerical producer keep their existing
acceptance and provenance. The six preparation modules, including Check07,
were accepted before the final continuation and their persistent evidence was
preserved by the final guard.

The final exporter selected **only the three final modules above**. Its
`numeric_rows = 0` means those modules contain no new numerical page rows;
it does not remove the earlier row acceptance connected by their theorems.
This continuation did not recompile the numerical pages, repeat the importer,
or re-export a new accepted selection of the 598-module numerical queue.
See the [earlier numerical acceptance record](./PUBLIC_NUMERICAL_ACCEPTANCE.md)
for that separately accepted batch and its reuse accounting.

## Evidence preservation

The final continuation checked the installed, persistent proof and audit
materials against the bound original receipts, compilation records, dependency
snapshots, six-module manifest, and accepted-prefix reference. Those persistent
inputs and the two previously successful final compilations remained unchanged.
It reused the completed historical acceptance of the transport archive;
**current temporary transport-archive revalidation was zero**.

Accordingly, `original_ci_and_six_preparation_evidence_unchanged` in the JSON
record concerns persistent proof and audit evidence. It is not a claim that
temporary transport files were read again. The original final exporter
manifest and evidence package were preserved byte for byte before the
successful completion was reported. Full operational evidence remains local;
this public record contains the minimal acceptance summary and public sources.

Historical `SOURCE ONLY` banners remain in the pinned Lean files. They record
the source-staging stage; the acceptance in this report applies to those exact
W3 bytes. The banners were retained to preserve source-bound compilation reuse.

## Public source provenance

| Role | Fixed public source |
|---|---|
| Accepted proof worktree W3 | [b33734e4](https://github.com/UyNewNas/goldbach-formalization/commit/b33734e49d17d66c4069965b3d445d1da31a1f37) |
| Finite-index proof repair W1 | [7c6fe1e2](https://github.com/UyNewNas/goldbach-formalization/commit/7c6fe1e249ffdbdf9b76b166022fc2236b2c69fb) |
| Original numerical source | [94c7c507](https://github.com/UyNewNas/goldbach-formalization/commit/94c7c507ab747cf4e05a4f19d8d4507cedfede38) |
| Numerical producer | [Actions run 45611402948](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45611402948) |
| Public transport source | [87c87492](https://github.com/UyNewNas/goldbach-formalization/commit/87c87492ab1e403ef2376188d2a6bfdb9f4520d1) |
| Storage adapter W2 | [8ae63b79](https://github.com/UyNewNas/goldbach-formalization/commit/8ae63b791b35eb8ed089cd3edb2554f137e0ee3d) |

W1 repairs the finite-index sum using the supported list API and an explicit
dependent-index transport. W3 repairs two rational-equality proof bodies using
reflexivity and the existing exact curvature/mixed increment identities.
Statements, rational constants, and chronology are unchanged. W2 retains the
original W1 reception identity and original numerical source; transport and
storage operations receive no new mathematical credit.

## Completion boundary

This acceptance completes the **P2.10 original Winner9 certificate chain and
seed-supplier connection**. The other **86 Full87 cells**, separate all22
density/distribution obligations, the entire P2 development, and the global
**1 + 1.7482** theorem remain outside this completion claim.
