# P2 private-environment continuation — 2026-11-24

This verification continues `work/p2-formal-proof` from `8657cfff`, through
`8fdeb981`, `a5a42f8`, and `0f87651d`, using the original 20261106 manuscript.
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
- All thirty-two numerical pages 0000–0031 and their two block aggregators pass
  strict compilation, independent replay, and complete owned-declaration
  audits: 512 original rows, 1,088 page declarations and two block declarations.
  This does not establish the remaining 10,514 selected inequalities.
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


## Verified logarithmic prefix estimates

Private job `8eae22d6f9f4499f836f015b157af926` strictly compiled the new
`P2WuPrefixLogDerivativeBudget` and reused the already strictly compiled
profile/support modules. It then independently replayed and audited all five
modules: 18 + 8 + 16 + 24 + 22 = **88 owned declarations**. The two new
main sources retain exactly the accepted bytes. Their historical source-only
header describes their drafting state; this receipt records the later gate.

`moving_physical_log_chart_budget` supplies one constant before the target,
endpoints, positive prime point, and chart point. It bounds the full mixed
Frechet derivative tensor by a fixed constant times
`(Real.log ((N : Real) + 2)) ^ (B * q)`. It uses the existing scalar smooth
step budget and the actual finite-product estimate. It does not assume the
budget it proves, and it does not supply a signed positive-product bound.

The [five-module evidence archive](evidence-wu-prefix-20261124.slim.tar.xz)
contains all 77 original members with five exact source references. Its
SHA-256 is `e83c1f2d9941d765ba09b887b302bf14a9e0ec34dc2526739d92bd65e19ed2eb`;
[byte/source verification](wu-prefix-repository-verification.json) passed.
Combined with the first export, those two archives contain **131 accepted
modules and 5,535 owned declarations**. `P2WuPrefixLogTheta` remains source-only: its older P5
import frontier is incomplete. The complete marked seed is not claimed.

## Second numerical block

Private job `eaf64cad17f14acabd5cb1f7d540d313` independently replayed and
audited pages 0016–0028 with two disjoint workers: all 13 pages and 442 owned
declarations passed. The existing cloud task
`3a5f35ce413f49c8a1fc138a17f65246` then completed pages 0029–0031 and the
block-01 aggregator: 103 more declarations passed. Its actual source/object
preflight and both audit-worker exit codes are retained; these existing
results were reused without another compiler or replay invocation.

The accepted union is now **148 modules and 6,080 owned declarations**.
Numerical coverage is exactly **pages 0000–0031, 512 original rows, and two
block aggregators**. These counts do not include incomplete native cache
qualification, failed memory trials, or pending later numerical pages.
The new main-source copies retain the accepted source hashes.

The [second-block evidence archive](evidence-numerical16-31-20261124.slim.tar.xz)
preserves all 239 original export members, using 63 concrete repository
source references. Sources for which only symlink entry points were available
remain embedded as original bytes. The first ad-hoc catalog was rejected by
the local verifier because it referenced symlink entries; the corrected repack
uses the existing canonical catalog routine and passes
[full byte/source verification](numerical16-31-repository-verification.json).
Archive SHA-256:
`0b89748bb7d6e39e87e9768ffdadbfc5d46ada39032b2157ce70f43ce55ec02d`.
The [disjoint accepted union](ACCEPTED_UNION.json) verifies that the three
published proof archives contain no duplicated accepted module and cover
exactly original row ordinals 0–511. Packaging introduces no new proof credit.

The first follow-up export validated all 13 selected receipts, but its
automatic supplemental-file discovery also collected unrelated quarantined
native-cache JSON. Its completed original archive remains on the private
worker. The subsequent large repack was cancelled before the planned fresh
compiler trial. The scoped exporter excludes that directory only from
automatic supplements; every bound native-context file and explicit
`--extra-evidence` selection still retains its original inclusion rules.
The original exporter bytes are preserved in `export-driver-v3-before-scope.py`.

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

The optional v3 native-context consumer preserves the existing finite
schema-2 cache signatures. Only project modules with actual native ancestry
require its explicit qualified source/object/import/runtime snapshot. Legacy
records cannot acquire native binding merely by changing their schema field.
The independent review is recorded in
[`native_snapshot_consumer_review.json`](../../../verification/part2/native_snapshot_consumer_review.json);
it tests consumer logic and does not qualify any actual native object.

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

A three-process trial on previously uncompiled pages 0022–0024, with a
3,072 MiB Lean memory threshold per process, failed with Lean
`memory_exception` in all three processes. The same pages subsequently passed
under the established two-process / 6,144 MiB configuration. A separate
three-process trial on previously uncompiled all-log pages 0041–0043, with
4,096 MiB per process, also reached Lean's per-process memory threshold.
It produced no new compiled page and peaked at 12,918,591,488 bytes aggregate
RSS. Neither result is described as a mathematical failure or a proof pass.

The page-0029 `--threads 4` invocation reused all 58 existing closure records
and invoked no source compiler. It therefore supplies no four-thread speed
measurement. Increasing threads inside one process must not be confused
with the observed cross-page parallelism. The service limits remain unchanged.

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

Even a completed Winner9 family leaves the same-rho positive-product
supplier and the original H247 endpoint licences. The 20261106 manuscript
fixes a finite marked-query family before taking its asymptotic limit. The
current `P2TableActionSourceOnly.H/h` instead use the native
`wuImprovementLimit` over `wuSourceBox`; identifying that native family with
the manuscript enhanced family remains a separate semantic obligation.
A stronger estimate over arbitrary moving native boxes must not be presented
as a requirement of the manuscript itself. Existing native box lower bounds
and collar/prefix error payments are reusable suppliers, but a fixed-query
maximum alone does not establish the stronger native interface. No
counterexample to the manuscript is inferred from this mismatch.

No full-P2 dashboard status is promoted by these partial results.
