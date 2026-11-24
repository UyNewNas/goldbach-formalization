# P2 private-environment continuation — 2026-11-24

This verification continues `work/p2-formal-proof` from `8657cfff`, through
`8fdeb981` and `a5a42f8`, using the original 20261106 manuscript.
**Full P2 is not complete. The complete 11,026-row numerical family and its
closed original-terminal lower bound are not accepted yet.**

## Environment and provenance

The user selected the private Cloud Compile environment. Its isolated worktree
is `/workspace/p2-private-20261124`; the accepted baseline
`/workspace/goldbach-p2` remains at `8657cfff` and is read-only. The historical
scratch directory `/workspace/scratch/p2-continue/` also exists in this private
environment. It contains the earlier strict/replay/audit scripts and logs.
The former public environment's retained-job limit does not apply to this
worker.

The compiler is Lean 4.33.0-rc1, with Mathlib pinned to
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. The actual Lean executable hash,
source hashes, object hashes, dependency signatures, commands, and results
are recorded in the private evidence. A compiler success, an independent
`leanchecker` replay, and an owned-declaration audit are separate checks.

## Verified changes

- The repaired complete ledger compiles and passes independent replay and the
  complete 115-declaration audit. Its 56 original theorem statements and eight
  definitions are preserved. The finite symbolic triple-projection lemma
  avoids unfolding the complete archive during projection elaboration.
- The exact identity with
  `P4AOriginalFull87SourcePrimeTests.cellIntegral (.remaining (.nine 11))`
  compiles and passes independent replay and its complete 14-declaration
  audit. All 62 extracted original declarations preserve their names, types,
  and bodies, including the full 87-cell types and dispatches. Integrating
  these cores with the four former owners still requires a combined import
  check using their matching refactors.
- All 44 geometry block checkers compile. The full actual-support null-overlap
  theorem also compiles and passes independent replay and its five-declaration
  audit. The complete 93-module geometry audit has now passed all 4,373 owned
  declarations. The eleven original definition cores have separately passed
  all 250 owned declarations (including generated declarations).
- The revised numerical checker and selected checker compile and pass
  independent replay and complete audits of 115 and 15 declarations. Their
  conclusions and `BasicChecks` proposition are unchanged. The revised
  decision procedure uses the already proved factor-mean identity to derive
  the redundant P-mean check, and materializes exact rational inputs before
  repeated kernel arithmetic.
- All sixteen numerical pages 0000–0015 and their block-00 aggregator pass
  strict compilation, independent replay, and complete owned-declaration
  audits: 256 original rows, 544 page declarations and one block declaration.
  This does not establish the remaining 10,770 selected inequalities.
- The unchanged six-row theorem was rebuilt against the revised checker
  dependencies and passed independent replay and its 20-declaration audit.
  Its source and conclusion remain unchanged.

The first complete private export accepts **126 modules and 5,447 owned
declarations**. Its geometry and definition-core coverage are complete; its
numerical coverage is exactly the first 256 original rows. The exported
manifest explicitly records `full_p2_complete=false` and
`full_winner9_family_claimed=false`. See [EXPORT_SUMMARY.json](EXPORT_SUMMARY.json).

The [compact complete evidence archive](evidence-checkpoint-20261124.slim.tar.xz)
retains all 1,209 original export members, with 281 duplicate source payloads
represented by exact SHA-256/size-bound repository references. All other
source bytes, receipts, complete declaration types, and logs remain embedded.
The original manifests, original archive hashes, and source-reference catalog
are included. The local verifier checked every original member and every
referenced source; see [slim-repository-verification.json](slim-repository-verification.json).
This packaging check adds no proof credit. Archive SHA-256:
`3fc76106288cba9e4f0e77daa69e2b4e886fef1848433511e38cb73db83d450c`.

The exact original totals and two chronological differences are unchanged.
No `sorry`, custom axiom, `native_decide`, or replacement integral is used to
close these goals. The original selected log/Q6 branch for every row remains
in the complete numerical renderer.

## Cache and audit discipline

`verification/part2/run_winner9_private_checks.py` uses schema-2 records bound
to the actual source, actual object path and bytes, compiler identity, Mathlib
pin, and recursive dependency signatures. A parent's object can stay identical
when an imported definition changes; therefore direct object hashes alone
are insufficient. Actual project dependency files are frozen before and after
each new compilation. Old numerical probes lacking that snapshot are not
silently adopted. Historical baseline objects retain their historical credit.

The first six completed audits used the exact driver preserved in
`driver-v1.py`, SHA-256
`05f31ad7f78c69bf58a1f0daab4b597db9a90190f255a880abdab22767c864b5`.
The accepted v2 driver, preserved in `audit-driver-v2.py`, adds only a safe
per-worker summary filename. Its replay,
owned-inventory, full-type, unsafe/partial/axiom and transitive-axiom checks are
unchanged. Previously accepted audits are retained without re-running them
just because the summary-output option changed. Parallel workers use disjoint
module lists and distinct summary names.

The only permitted transitive axioms in accepted new declarations are
`propext`, `Classical.choice`, and `Quot.sound`. Audits record every serialized
and environment-owned declaration, including private and generated names;
they are not limited to a hand-picked list of final theorem names.


## Parallel compilation and safe continuation

The private service has a four-core CPU quota and 16 GiB environment memory,
with a 13,107 MiB per-job memory limit. Its service queue runs one job at a time;
inside that job the source-bound runner can compile independent modules in
parallel. Numerical block 00 actually used two Lean processes, completed in
724.392 seconds with no failed module, and peaked at about 10.72 GiB aggregate
process-tree RSS. The complete geometry/core/page audit also used two disjoint
worker lists and distinct summaries: all 119 new module audits passed in
1,742.210 seconds, with about 7.41 GiB peak aggregate RSS. These are observed parallel runs, not
only advertised support.

Keep two heavy numerical compiler processes at this measured memory level.
The optional `--time-budget-seconds 3000` stops dispatching new modules before
the 3,600-second service deadline, lets running modules finish, and atomically
retains their actual records. Exit 2 means an explicitly partial batch; exit
0 means the whole requested closure completed. Repeating the command reuses
only still-valid source/object/dependency signatures. No pending module is
counted as compiled.

## Remaining integration

The complete numerical renderer emits 690 pages, 44 block aggregators, and a
complete aggregator. The final source-only terminal now also connects the
ledger bound to the exact original Full87 integral through the proved
identity. It receives no closed-family credit before all of its actual
numerical and geometric suppliers are verified.

The actual source census found 247 project modules, 506 native Goldbach
modules, and nine LeanArchitect modules, with 21 direct `MathlibNt` roots.
The 762-node graph is closed and acyclic, all eleven dependency pins match,
and no source module is missing; this is source inventory, not compilation.
See [owner-native-source-census.json](owner-native-source-census.json). The native dependency is fixed at
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
Existing exact-source native objects must be checked for reuse before fresh
compilation. A source-only compatibility scan is not a combined Lean import
check, and a Mathlib-only project-cache record does not bind this new native
dependency boundary.

Even a completed Winner9 family leaves the actual same-rho positive-product
supplier, the original H247 endpoint licences, and the moving-family
quantifier/interface work. The native library already has a uniform lower
bound for the actual Wu boxes and uniform collar/prefix error payments;
these must be reused. A finite fixed-query maximum alone does not prove the
required uniform estimate for all moving admitted weights. No counterexample
to the manuscript is inferred from that interface obligation.

No full-P2 dashboard status is promoted by these partial results.
