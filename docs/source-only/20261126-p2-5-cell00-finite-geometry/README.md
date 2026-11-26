# Cell00 finite geometry and pulling candidates

**Source only, uncompiled, zero formal credit. `P2_5_proved` remains false.** This package prepares the missing finite facts on the existing Cell00 typed payload. Production files, the current 377-source / 69-owner run, original input files, and all accepted objects remain untouched.

## Exact frontier and reuse

| Obligation | Existing source or accepted supplier | This package |
| --- | --- | --- |
| Eight simplex arithmetic guards and floors | Accepted `AllRowsArithmetic`, Row00–07, `StoredFloors` | Reuse only; no arithmetic proof is repeated |
| Cell header, all vertex dimensions, simplex count, facet-ID bounds | Accepted `TypedSourceFacts` and `StoredFloors` | Reuse `cell00_facet_indices` when forming `Fin 96` row indices |
| Original mask partition | Prepared `cell00-patterns` typed/original source pair; Literal42 is accepted with 15 owned declarations in actual round4 | Reuse that package; no duplicate pattern theorem |
| Strict interior candidate | Original `original_strict_centers`, still a global source-only decision | New closed typed Cell00 specialization against the original 96 physical rows |
| Every saved vertex satisfies every physical row | Original `original_vertices_all96`, still source only | New closed 16-by-96 weak-inequality specialization |
| Positive normal balance | Original complete size/positive-weights/eight-coordinate guard | Preserve the full conjunction in a typed Cell00 specialization |
| Original facet incidence | Original complete facet-list-size and membership/zero equivalence | Preserve both conjuncts, all ten facet IDs, and all sixteen vertices |
| Retained face-ledger decode | Existing `FaceRecord`, `decodeFace`, constructor-success elimination | Exact decoder relocation; typed parse-success decision and existing elimination pattern |
| Primitive reverse-pulling incidence | Existing `Shape`, `shapeDecidable`, and ordered max-pivot `pull` | Closed `Shape ... 9 whole` candidate on unchanged retained records |
| Saved row binding | Existing `original_pulling_bindings` global draft | Exact ordered pull equality and saved-row-list `Nodup`; no row reordering |
| Containment and geometric separation | Existing `closedRows_mem_closure`, `pull_pair_separated`, supporting-facet proof, affine zero-volume proof | Existing proof text is reused; no new coverage or disjointness assumption |

The actual consumer005 aggregate failed at OriginalParse; its Decoded owner and the preserved typed suppliers retain their separate actual acceptance. No accepted OriginalFloors payload/archive correspondence is claimed here. Consequently this package introduces **no original-archive transport theorem**. Once the existing correspondence is accepted, later transports must use that exact equality.

## Small dependency changes

Two fresh light cores expose four existing commands under their original namespaces: `evalQ`, `interiorCandidate`, `FaceRecord` with its derived instances, and `decodeFace`. Their complete command bytes are unchanged. The candidate OriginalArchive and PullingOwnership postimages remove only those commands and add the corresponding import. The PullingFaceInduction postimage changes only its OriginalArchive import to FiniteGeometryCore; every generic proposition and proof body remains byte-identical.

The five initial owners are the two cores, the unchanged-body PullingFaceInduction postimage, TypedGeometry, and TypedPulling. OriginalArchive and PullingOwnership are compatibility postimages for later integration, **not initial compilation targets**: compiling their global closed guards would pull in fourteen-cell work beyond this Cell00 package.

Fresh ownership is substantive. Even unchanged moved commands must obtain strict normal checking, independent kernel replay, and a complete owned-declaration/type/transitive-axiom audit. FaceRecord's generated recursors and derived instances must be included. The static byte check does not simulate a Lean AST or replace this audit.

No new general geometric lemma is introduced. Existing `closedRows_mem_closure` supplies the strict-center/weak-vertex closure argument; existing `pull_pair_separated` supplies the induction from Shape and supporting facets; existing affine-zero-volume and simplex-map proofs supply the later geometric steps. Those existing source-only proofs retain their actual pending status until separately accepted.

## Literal96 and execution boundary

The exact round4 result is pinned in `DEPENDENCY_STATUS.json`. Literal96 appears in its failed-or-blocked normal set and has **accepted=false, declarations=0, reused=false** in the owned audit summary. Its 267-module project dependency set matches the already pinned round2 source graph. The local source closure for these candidates has 280 modules in total. These are dependency inventories, not accepted closure claims.

Literal42's actual accepted owner and the prepared Patterns closure do not provide Literal96 acceptance. The parent is continuing the existing P2 dependency run; no terminal round5 receipt is invented here. Before execution, the runner must select actual accepted source/object/receipt/context suppliers and retain every unresolved owner gate. Compatible accepted dependencies should be reused without repeating their successful gates.

The typed pulling path does not import Literal96. That allows its fresh finite owners to be scheduled separately once the parent's current Cell00 prerequisites and compatible base receipts are ready. TypedGeometry still requires Literal96's actual accepted dependency context.

## What the host diagnostics mean

The read-only rational calculations found no negative value among 1,536 vertex/row evaluations, with 162 exact zeros. The first saved simplex barycenter was strictly positive on all 96 rows, with minimum margin `1/13500000`. The ten original facet IDs, normal weights, and 160 incidence equivalences matched. The retained 17 face records satisfied the existing finite Shape conditions, and fuel-nine pulling reproduced the eight saved rows in their original order with no duplicate row.

These observations are recorded as **host-only diagnostics**. They are neither proof terms nor accepted parse/arithmetic receipts. They introduce no replacement Lean data and certify no kernel resource feasibility. The new proof candidates use `decide +kernel` against the unchanged definitions and literals. Actual elaboration, strict lint, kernel replay, and complete ownership audits remain pending.

The reviewed statements show a finite formal-verification and dependency-packaging task; the host checks did not expose a false closed predicate. This is not a claim that the manuscript has a gap or that its remaining analytic obligations are settled. The manuscript's positive inner-union lower bound needs containment and a.e. nonoverlap, which the existing proof chain addresses; full polytope coverage is not introduced.

## Files and review procedure

`SOURCE_SELECTION.json` binds all seven candidate postimages, their exact preimages, and the patch. `DEPENDENCY_STATUS.json` binds the historical supplier receipts, current source closure, Literal96 status, and existing Patterns package. `HOST_DIAGNOSTICS.json` keeps the nonformal diagnostics separate. `PLAN.md` records the scope and task ledger.

Run `python docs/source-only/20261126-p2-5-cell00-finite-geometry/verify_source_package.py` from the repository root for read-only provenance checks. It validates all pinned source bytes, exact relocation and postimage reconstruction, import closure including historical CRLF files, and the distinct accepted/blocked statuses. It never invokes Lean, mutates production, or changes proof credit. Independent review and the parent's later actual verification gates remain necessary.
