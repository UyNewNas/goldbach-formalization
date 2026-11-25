# Saving19 HigherMoments facade candidate

## Ready for a single-owner acceptance run

The candidate is ImbalancedChen/P2OriginalSaving19HigherMoments.lean, 15058 bytes, SHA-256:

    da2281584acf0c11940e4ae38dd5a6871f74f81981d9a3be9e2609f5f7459181

This package changes only that facade. It does not modify the production checkout, run P1, or recompile any accepted supplier. SOURCE_MANIFEST.json is the stable entry point. Its SHA-256 is:

    4e0f71c68a2a97e2fe58806381e9684cca77c4187e16f1a4179213619f30f997

The new structural suppliers were reported accepted by the parent in job_1b0e5c52fcfe440b9bd27179ed7fdf14, including normal, kernel, all environment-owned types and axioms. Their source hashes and individual result hashes are recorded in the manifest.

## Exactly what changed

The imports now are:

    import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
    import ImbalancedChen.P2OriginalSaving19HigherMomentsMomentStructure

MomentFloorConsumer remains a direct dependency for MomentRow and the floor consumer. MomentStructure transitively retains the same Core definitions and the accepted Symmetry supplier. The old individual GuardK/AuthorK imports and LowBoundary import are no longer needed by the facade.

Only two theorem proof bodies are replaced:

| Existing public theorem | New proof |
|---|---|
| integratedPower_newton_guard | exact ProofPieces.integratedPower_newton_guard_structural y i k hk |
| duplicateH_author_guard | exact ProofPieces.duplicateH_author_guard_structural y i k hk |

Four original statement headers used the malformed literal field syntax 9.factorial. The pinned Lean parser rejects that spelling. Each occurrence is replaced with Nat.factorial 9:

1. integratedPower_newton_guard
2. binomial_normalization
3. integral_bary_interpolate_power
4. integral_interpolate_mul_power

These are explicit source-byte changes to the headers. The repaired expression denotes the same intended natural factorial 9!, with the original coercions into ℚ or ℝ. The report does not claim those four old headers were byte-identical or successfully parsed.

The original namespaces, opens, binder order, all Fin9 and Fin10 indices, degree bounds, assumptions, definitions, record fields and remaining proof bodies are unchanged relative to the published 0fa baseline. Reversing the two proof replacements and accounting for the four explicit syntax replacements reconstructs the baseline text exactly apart from the import block.

FACADE_DIFF.patch contains the complete diff.

## Three source stages, with distinct provenance

| Stage | Exact source location | SHA-256 |
|---|---|---|
| Original monolithic source | 0fa archive path: docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean | 59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e |
| Published split facade | 0fa path: ImbalancedChen/P2OriginalSaving19HigherMoments.lean | 910de365b810a41d17f7781856e384512cb0080d5051c6be7045643f0004b3b1 |
| This candidate | ImbalancedChen/P2OriginalSaving19HigherMoments.lean in this candidate directory | da2281584acf0c11940e4ae38dd5a6871f74f81981d9a3be9e2609f5f7459181 |

Here 0fa means commit 0fa84a8bf7c3a794d29279f381c8b5b18a8d3b2d. The original 59cc source is a Git object at the archive path in that commit; it is not the main facade blob at that commit. The parent separately reports 59cc as the current remote facade preimage. This package does not claim to have independently inspected that remote installation or identified its source commit.

The provenance directory contains independently named, byte-verified snapshots of both facade preimages and the frozen Core. They are review inputs, not a claim that the actual remote installation has already been backed up.

## All 36 original public contracts compared

PUBLIC_DECLARATION_COMPARISON.json compares every original declaration across the three source stages. The original API comprises 30 declarations now in the facade and six definitions/theorems already moved into the frozen Core.

| Category | Count |
|---|---:|
| Definitions, all byte-identical to original and 0fa | 12 |
| Structure, including all fields, byte-identical | 1 |
| Theorems | 23 |
| Total original public contracts | 36 |
| Headers byte-identical to original and 0fa | 32 |
| Headers with the explicitly recorded factorial syntax repair | 4 |
| Complete declarations byte-identical to 0fa | 31 |
| Theorem proof bodies byte-identical to 0fa | 21 |

The four repaired headers become exactly equal to the original headers after applying only the documented literal replacement. No whitespace or binder normalization is needed to hide other source changes. This is a static source comparison; it is not a kernel comparison against an old malformed parsed type.

There are two additional pre-existing differences between the original 59cc proof bodies and published 0fa. The current candidate preserves both 0fa repairs verbatim:

- rationalMoment_cast explicitly instantiates duplicateH_map, records hmap, and aligns the real cast with a change command before rewriting.
- integerNewtonNumerator_spec uses smul_eq_mul in the existing simp call.

Consequently the candidate has 29 complete declarations and 19 theorem proof bodies byte-identical to the original monolithic source, while it has 31 and 21 respectively relative to the actual 0fa baseline. The report explicitly separates these historical changes from this patch's two guard replacements.

The declaration parser is reused from the prior source partition checker. Its source and slice hashes are recorded in the report.

## Complete source closure

SOURCE_INPUTS.json records every project module, its source SHA-256, imports, origin path and import graph at the pinned base.

- Published split facade closure: 285 project modules.
- Candidate facade closure: 224 project modules.
- No old GuardK/AuthorK provider remains in the candidate closure.
- The full import graph is acyclic.
- All unchanged worktree dependency bytes match their published 0fa Git objects.
- All eight frozen Core/Low/Symmetry/structural source bindings are checked even when a frozen owner is no longer imported by this facade.

Import scanning masks comments and splits whitespace, including existing CRLF line endings. This avoids interpreting a carriage return as part of a module name.

## Installation preimages and strict validation

The manifest permits exactly three existing facade source hashes:

1. Original remote preimage, 59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e.
2. Published local 0fa preimage, 910de365b810a41d17f7781856e384512cb0080d5051c6be7045643f0004b3b1.
3. The new candidate hash, for an idempotent installation.

For either old preimage, the parent installer must separately record the actual preimage SHA, backup path, verified backup SHA and replacement SHA. An unknown preimage is not overwritten. This candidate generator performs no installation.

The source comparison and smaller closure do not replace the existing strict normal/kernel/full-owned/types/axioms checks. The facade is a single changed owner, and all accepted suppliers remain frozen. No global or tactic budget has been added.

## Reproduce the static checks

    python /workspace/p26-recovery-candidates/moment-facade/prepare_facade.py --check

The generator always reads the pinned 0fa Git objects. It writes only beside itself when --check is omitted. It never mutates the source checkout, launches a compiler, or alters the parent's strict API.

The parent may publish the candidate with its own gate-proper owner in a shared runner scope. This package's manifest remains a separate single-facade source binding and contract-comparison input.
