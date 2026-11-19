# P4A.5 same-rho hdensity: partial installation audit (2026-11-19)

Status: SOURCE_ONLY; COMPILED=false; KERNEL_REPLAYED=false; transitive axiom audit NOT RUN; finite proof bodies UNEVALUATED. No new mathematical theorem, proof-body change, external input or status promotion. This packet improves reproducibility of installation and locates the next dependency frontier; it is not a complete installation or an elaboration receipt.

## Baseline and provenance

Formalization baseline is `71b47b30928600386237323d4f6a1f0c332edfbe`, candidate `docs/source-only/20261112-resume/t01/P4AOriginalFiniteAll22FineDensity.lean`, SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`. At start the remote branch name for this packet did not exist; this branch is rooted at the baseline. The independent static source review is at `docs/source-only/20261110-yellow-closure-10t/t09_review_density_history/resume-20261112/T01_HDENSITY_REVIEW.md` (not a compiler or current independent review). It reports its own narrow static result; no new independent reviewer was used.

The inherited early-gain registry pins both manuscript revisions `9731290e8f53cffda44129906cde6a965eaa869b` and `ba6ec11d800eccc54406490631895e174de85766`, with the same paper tree. The requested manuscript at 9731290 was read at lines 368–490 and 1326–1369; GitHub reported manuscript-body.tex blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, consistent with the registered manuscript source. No version substitution or mixed parameter set is asserted.

Declared pins in baseline: `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. These are declarations, not local installed-version receipts. Neither dependencies nor toolchain are locally installed. Constants were not changed.

## Exact scope of source reading

The candidate invokes the Fine predecessor once with eta = densityReserve/2. Its Q and rho definitions ignore delta, so the intended density premise has one beta, k and N0 for all positive delta. The correction sign call passes the same F, N, cap=N, w and z, with w≤z inferred using nu*v=19/96 and beta²<v. The compiler expense is inherited, not charged again. This is a textual/interface assessment only: neither this candidate nor its transitive inputs were elaborated here. The retained finite count still contains the complete signed `realPhysicalDistributionError`, `ceil(z)` and `T+1`. The candidate does not supply the full PP estimate, hmajor, hcoprime, hdistribution or complete hUpper.

## Installation progress and remaining frontier

All 12 high helpers in the Fine allowlist were found under `docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor_finite_policy/`; each file's SHA-256 matches its registry. They are archived sources, not installed root modules. The reviewed List overlays were checked byte-for-byte against their exact original plus the scoped edit and the patch hash; the namespace overlay was reconstructed from the original by the recorded one-line namespace change, then checked against the recorded output hash. Neither overlay proves type correctness.

Three registered missing P4 source files were recovered from `eea9486f7b101d484e2938e97499c1d77cc1a67a` into this packet, matching both the old registry SHA-256 and original Git blobs:

- `p4-pinned/P4AOriginalFiniteAll22EarlyDefectCounting.lean`: SHA-256 `6aa6712f383ed24fa64792ab9433767445126e3ea92adba16748167e99660974`, blob `fb3aa5371d57b599fac9726603aaf3d179dd38db`.
- `p4-pinned/P4AOriginalFiniteAll22Nineteen.lean`: SHA-256 `a7bee460a4b9d6a8743b27d1ca2fadb3fc60991e175051c1dc3d52c3166054fa`, blob `abadf4d9fbbec16085deb732f4e3388e35500218`.
- `p4-pinned/P4AOriginalFiniteAll22PaidSixth.lean`: SHA-256 `a6e627bdf5bada7a25f2ead930d571b825a749721a3aa778e898d1b8000b3a3b`, blob `cdef0be4f600a2cb88be6acd756e3d451c9eb40a`.

`INSTALL_MANIFEST.json` records 113 direct copies and one reconstructed namespace overlay; 85 later selections are explicitly provisional: a unique archived filename whose bytes match an existing registry is not, by itself, proof that the source is the correct member of this chain. Confirm each against the relevant selected registry and check all unstaged baseline root sources and data before using this as an installation. Nothing is installed into the checkout's production module directory. `IMPORT_AUDIT.json` records a literal-import traversal from the candidate, including per-file hashes: 515 project modules visited, 36 unresolved project imports and 131 non-project module names. It is a static path graph, not proof of full Lean import syntax, matching `.olean`s, package availability or transitive source identity. In particular `P5HistoricalRectangularGammaTransport` has two archived candidates; do not select solely by filename. The other unresolved names and their importers are recorded in the JSON.

## Validation and next step

- `python3 docs/source-only/20261119-p4a5-hdensity-install/stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-final > docs/source-only/20261119-p4a5-hdensity-install/IMPORT_AUDIT.json`: exit 0. The destination was an empty isolated directory. Hashes and overlay byte transformations were checked. The run reports 114 staged files and the incomplete frontier above.
- `lean --version`, `lake --version`, and `elan --version`: command not found (127 individually). `.lake/packages` and `.lake/build` are absent. `lake env lean /workspace/scratch/cb6959cc4223/stage7/ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean`: exit 127, `/bin/bash: lake: command not found`; no Lean elaboration occurred. No runtime version, memory or timeout acceptance claim follows.
- No CI, remote execution, compiler download, toolchain upgrade, resource expansion, extra axiom, sorry/admit, native_decide, unsafe or user-machine access was performed. No new external theorem was introduced; existing external inputs remain governed by their prior registries, not reverified here.
- Next: resolve the 36 frontier modules against exact chain registries and the two P5 variants, repeat the recursive import audit and account for data files; verify all provisional choices and package pins. In a future permitted environment that already has the pinned toolchain and dependencies, install into a separate checkout, build necessary imports in order, then typecheck this exact candidate and inspect its generated declaration, kernel replay and transitive axioms. Record all logs and exit codes; do not infer success from this packet.

Packet SHA-256 (excluding this report, which cannot contain its own digest):

- `INSTALL_MANIFEST.json`: `74812be4b0b79bb13fc9357ae9a05753cf42a77906c8ae104ca73af274c5862d`
- `IMPORT_AUDIT.json`: `22f526bb574d2923cb93aded468edc0d9d427f89b2d4d96d4bd22b8ee8abdae9`
- `stage_and_audit.py`: `4712cdf8de1acaf35e8ec422e35958736b046088bdaceb39e2c115ca7029dd1a`
