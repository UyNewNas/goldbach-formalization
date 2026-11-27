# Classical common Poisson support: continuation review

Review date: 2026-11-27. This is a source and verification-protocol review;
it does not itself grant Lean or kernel acceptance.

## Initial reviewed identities and scope

- Remote source commit: `4c213f5d6477aa30e1d4636d5c4fb9d01cf8e188`.
- Local source commit: `f167fca3356378275c76bd0c1c6a5d28b96916f6`.
- Both commits have tree `3a5e0b7edb7132f2f7d49d596fc9b81086cbc344` and
  parent `2110a6170401bfc0dcaee46f689ee5f705507683`.
- The reviewed source checkout was clean before and after review.
- The four original consumer declarations are `classicalMScale`,
  `classicalMScale_bounds`, `commonMBlock_classical_support`, and
  `commonPoissonCompleted_classical_support`.

An independent reviewer read the consumer, source intake, complete project
closure, cloud launcher, verification gate, serialized owner inventory,
boundary instances, and shared import/axiom validators. No critical or
important finding was identified. No mathematical source was rewritten in that initial review. The subsequent candidate has two documented proof-body expression repairs; its definition, theorem statements and assumptions remain unchanged.

## Checked properties

1. The original `verify_sources()` run recomputed 57 project modules and 68 bound source paths.
   The original segment, accepted P3.1 core, configuration, current split
   declaration owners, and forbidden-token checks agree with the intake.
2. R2 started without project objects and compiled 56 providers in dependency
   order before the consumer failed. The incremental continuation starts with
   an empty destination object root, authenticates the fixed R2 archive and
   rechecks all 68 old source bindings, tools, packages, all 67 direct external
   objects and all 56 provider objects. It resolves each import again with Lean,
   copies the authenticated provider parts as separate ordinary files and
   compiles only the repaired consumer. Final invariants cover the complete
   inherited external set as well as new audit imports.
3. The inventory uses defining-module metadata and the serialized constant
   list. It distinguishes the four new P3.4 explicit declarations from the
   reused P3.1 provider and from generated compiler records. The combined
   inventory total is not the number of new mathematical declarations.
4. The actual interval retains its `J + 1` clipping. The scale change applies
   only to classical support, with `M = 2^j - 1/2`; the actual phase retains
   denominator `64 * 2^j` and arbitrary integer `k1`. The explicit boundary
   file covers `j = 0`, `m = 1`, `M = 1/2`, and the empty block at `J = 0`.
5. Eleven external package checkouts are bound to their pinned revisions.
   Directly imported external object parts are hashed. The declared trust
   mode is `NORMAL_IMPORTED_ENVIRONMENT_TRUST`, with no claim of complete
   external-source kernel replay.

## Executed local checks

The eight cases in `test_p34_classical_support_gate.py` passed. The separate
source-only gate returned `SOURCE_ONLY_NOT_COMPILED`, with 57 project modules
and all seven checkout/provenance commands returning zero. No local Lean
compilation was performed.

The inherited `test_p34_import_scope.py` fixture requires a configured Lean
environment. A controller invocation stopped at setup because `LEAN_SYSROOT`
was absent, before it could start Lean. This is recorded as an unavailable
local fixture, not as a successful test or a mathematical compile failure.
The current cloud gate performs its actual import-resolution checks directly.

## Interpretation required for the cloud receipt

`matches_prior_receipt_tool_hashes` is an informative equality field. The gate
enforces the specified Lean version, commit and prefix, then records and
rechecks the tools used in this run. A claim that historical and current tool
binaries are identical additionally requires that equality field to be true.

Formal acceptance still requires successful target strict compilation, target
kernel replay, the boundary instances, full owner inventory, and the final
source/object checks. P3.4 as a whole remains open: this finite interval result
does not establish the external Theorem J estimate, original physical level-row
attachment, Fricke-to-Whittaker amplitude normalization, or continuous-spectrum
Plancherel normalization.

## Expression-repair and incremental-gate checks

An independent source review confirmed that only two theorem proof bodies changed. All four declaration interfaces, the actual clipped block and weight, signed integer frequency, and physical denominator remain unchanged. The repaired segment must reverse to the original donor hash. Twelve Python gate regression cases passed on the updated version, including rejection of unauthorized statement/phase edits, replaced checkpoint evidence, changed or incomplete provider closure, stale private object parts and overwrite attempts. Recomputed source checks bind 57 modules and 69 source/evidence paths. These local checks did not invoke Lean.

The fixed R2 evidence archive is SHA-256 `6bc71fbd4b154117078db9c73d954156ca96125e0278b33005472f68831134bb`; its report is `a46ceddb2808b58e849a888ef5778323bee0f690a69230bf102b133a9cba087a`. The archive records 153 stages, exactly one failed consumer strict stage, 56 successful provider compilations, and clean final source/tree provenance. The new gate requires exact equality to the R2 tool hashes and canonical package roots when reusing these objects.
