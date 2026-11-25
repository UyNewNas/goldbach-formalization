# Winner9 log evaluation probe — 2026-11-25

**The additive helper and page 0064 passed normal compilation, stock replay,
and the complete owned-declaration audit.** The root agent reported the actual
private-job results below. This covers 16 original rows and 80 owned
declarations across the helper and page. It does not establish the remaining
Winner9 family or full P2. No precise speedup is claimed.

The local source-preparation workspace has no Lean executable. The historical
source-only header in the helper describes its state before these remote
checks; the accepted source bytes are retained unchanged.

## Actual bounded-probe results

The first helper attempt, job `ddaf868c2d864020bb31dc4baffcbf3d`, reused 57 valid
modules and failed on two multiline record-update parser errors. It compiled
no numerical page and earned no acceptance credit. Its helper SHA-256 was
`660b0f719b2f64806990e7c28977b578447134a83bc9f3ee6fec6893ccaa51da`.

Those two expressions were changed to complete record literals in the same
form as the accepted checker's existing forcing operations. The values and
equality statements were preserved. The revised helper SHA-256 is
`d8b8537011ca56c321d57d85c7821a59054b501bde496e1dd3f807a7bf9b95ba`.
The candidate page remained byte-identical throughout, SHA-256
`8cb604c83aa0a24a6a6e76b88eea69f0c365c6b6644e82771c80668fc2257031`.

Retry job `62fb432c008c46369d79063c85363bdd` passed normal compilation of the
helper in 33.661 seconds and page 0064 in 54.191 seconds. The root reported
5.80 GB peak job memory. The retained page-0063 compilation took 111.274
seconds, but the pages contain different rows; this comparison supplies only
preliminary performance evidence.

Job `fd5bb7641e6540fb8018ce03a1cdd0c1` then passed stock `leanchecker` replay and
the complete v3 audit for both modules: 46 helper declarations and 34 page
declarations. The v3 driver SHA-256 is
`36b2e1252b3b926a22505e7a7489485c78b33d1fb6904060840dfc9d613a9637`.
`PROBE_MANIFEST.json` records both source revisions, the failed attempt, and
the successful stage boundaries separately.

## Scope and reason

The existing selected checker already forces the row's rational vertices and
stored means, and the Q6 branch also forces its rational Input and integer
SimplexData. The log branch calls `logFloorCheck` directly. Its `factorData`
therefore remains an expression built by `toSimplexData` while the degree-six
moment arithmetic repeatedly reads its integer gaps, deviations `y`, and `U`.

The new helper uses the existing sound log cross-product unchanged. For each
factor, it first forces the exact rational gaps, factor values, and maximum;
then it forces the normalized integer gaps, `y`, and `U`. Every forcing
operation has an equality proof to the original input. No supplied numerator,
new interval enclosure, approximate arithmetic, new normalization formula,
or stored literal replacement is introduced.

The hypothesis is that this materialization reduces repeated kernel reduction
of rational normalization. The successful probe gives a preliminary timing
observation; the different-row comparison does not isolate the speedup.
The remaining recurrence tables, determinant, first moments, and price
computation are unchanged.

## Additive proof boundary

`P2Winner9MaterializedLogChecker.lean` imports the existing selected checker and
declares the following chain:

1. `checkFactor_eq_decide`: the materialized factor Boolean equals the original
   `decide (logFloorCheck ...)`.
2. `checkLogMaterialized_eq`: the materialized log branch equals original
   `checkLog` for every rational vertex family and every RawRow.
3. `checkSelectedMaterialized_eq`: the complete new Boolean equals original
   `checkSelected` for every RawRow.
4. `checkSelectedMaterialized_sound`: a new Boolean certificate supplies the
   exact original `checkSelected r = true` conclusion.

The original `BasicChecks`, original row binding, physical determinant and
density factor, factor maxima, Q80 log floors, Q96 final comparison, selection
comparison, and whole Q6 branch remain present. The forcing helpers reproduce
the already accepted checker's evaluation pattern locally, because its generic
helpers are private. The new module does not change those existing private
declarations or their owners.

The candidate page has the original namespace and the exact original sixteen
row statements and public `checked` statement. Each row proof now applies
`checkSelectedMaterialized_sound` before `decide +kernel`. Removing only the
additional helper import, helper open, and sixteen apply lines gives the
original renderer's page 0064 byte for byte. The archive has fifteen log rows
and one Q6 row on this page; that last row exercises the untouched branch.

## Bounded benchmark procedure

Stage only the new helper and this candidate page in an isolated source/object
overlay of the current private worker. Resolve all existing imports to the
already source-bound objects. Keep the original active checker and renderer
files and all existing accepted page objects unchanged.

First strictly compile the generic helper. If its equivalence proofs fail,
stop before launching numerical compilation and report the actual error. If
it passes, strictly compile **only page 0064**, then run the existing stock
`leanchecker` replay and full owned-declaration/type/axiom audit for the helper
and that page. Use the existing two-worker, 6,144 MiB configuration where the
runner needs it; the experiment does not test another concurrency setting.
Cap the complete experiment at 600 seconds and retain actual completed
records if the budget expires.

Record compiler process time, stock replay process time, peak RSS, exact
source/object hashes, and dependency signatures. Compare with the already
retained numerical page records, paying attention to branch mix; a comparison
across different rows is only preliminary performance evidence. Do not
recompile any accepted page as a control. Do not claim a precise speedup from
that comparison. A material improvement in both fresh compilation and replay
is required before proposing this proof body for further uncompiled pages.
If the benefit is unclear, retain the current renderer and report the bounded
probe without expanding it into another optimization project.

The completed page 0064 covers original ordinals 1024–1039. At dispatch, normal compilation
covered pages 0000–0063; this candidate therefore does not repeat an accepted
numerical leaf. The root has started the same additive transformation for
previously uncompiled pages 0065–0079 and their original block-04 aggregator in
job `63273245900a458f96bdddcf4d1e0e6c`, preserving the exact reverse source
comparison. That normal job completed successfully. Audit job
`e06549910239461f9a078c985ebc24e3` subsequently passed stock replay and full owned
audits for all 15 additional pages and the original aggregator: 16 modules and
511 owned declarations. Together with already accepted page 0064, block 04
covers all original ordinals 1024–1279 (256 rows; 545 owned declarations).
An earlier audit job was interrupted before any page acceptance and grants no
additional credit. The original renderer and accepted checker definitions
remain unchanged.

## Why the other changes are not proposed

The retained `NUMERICAL_VERIFICATION_COSTS.json` has 1,796.747 seconds of stock
replay process time and 131.005 seconds of audit process time for its recorded
block. Even deleting the entire audit stage would remove only 6.8% of those
two stages, and a smaller fraction after compilation is included. It does not
justify a new audit driver or weaker checking. Import pruning would require a
larger separation of archive/computational/analytic declarations and does not
itself reduce the exact arithmetic performed by the kernel.

The existing two-process allocation is retained. The recorded three-process
trials at 3,072 and 4,096 MiB per Lean process failed at their process memory
limits and supply no successful alternative configuration. Merely replacing
`decide +kernel` with a different closed equality spelling would still require
the kernel to verify the same arithmetic; this probe changes input evaluation
sharing while retaining the existing proof mechanism.

## Static checks already performed

`PROBE_MANIFEST.json` binds the source-only helper and candidate page hashes,
the branch inventory, and the exact current source bytes of the protected
original modules. Both canonical source bytes and any symlink entry bytes were
compared with commit `ac9e6404a9ff7e2f980da6eaa8b80a19677044c6` and matched.
The candidate's statement-preserving transformation was checked against the
untouched renderer. Those local checks provide source/provenance evidence.
Normal compilation, independent replay, and owned-declaration acceptance are
provided separately by the named successful remote jobs above.

References within the unchanged repository:

- `verification/part2/render_winner9_numerical_checks.py`
- `ImbalancedChen/P2Winner9RowArithmeticChecker.lean`
- `ImbalancedChen/P2Winner9SelectedArchiveChecker.lean`
- `ImbalancedChen/P2Winner9FastLogCertificates.lean`
- `ImbalancedChen/P2Winner9RationalSimplexData.lean`
- `docs/verification/20261124-p2-private/README.md`
- `docs/verification/20261124-p2-private/NUMERICAL_VERIFICATION_COSTS.json`
- `docs/verification/20261124-p2-private/PARALLEL_ENVIRONMENT.json`
