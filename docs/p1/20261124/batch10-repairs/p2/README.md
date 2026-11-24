# Batch10 ordinary P2 candidates

Status: **source-only; uncompiled**. Canonical source was not changed.

The four candidates correspond exactly to the complete Batch9 failure blocks bound in `MANIFEST.json`. The patch preserves imports, namespaces, public declaration names, hypotheses, and all definitions except the explicitly documented numeric factorial selector syntax in Saving19.

- InitialClosedTree: add the reflexive last-coordinate identity for a constant three-vector to the existing proof.
- CompactQ80Table: reuse the current accepted SieveStateInduction cast and denominator cancellation pattern; compact parameters remain 16384 and 12.
- LowerBufferedAffineBoxes: make addition monotonicity arguments explicit.
- Saving19SimplexMoments: reuse the accepted simplex continuity pattern, reduce literal vector entries and image-function beta redexes, and replace seven invalid `8.factorial` / `9.factorial` / `10.factorial` lexical forms with `(8 : ℕ).factorial` / `(9 : ℕ).factorial` / `(10 : ℕ).factorial`. Six theorem headers and the physicalVolume definition have only this authorized syntax difference; the formulas, dimensions, assumptions, and names are unchanged.

The pinned 1106 simplex-moment formula gives 8!, 9!, and 10! respectively for dimension-eight volume, first moments, and second moments. These are not replaced by alternative formulas. Lean's `sorry ()` in the old failure log is parser recovery after the factorial-selector errors; no candidate contains an admitted proof.

`SOURCE_HASHES.json`, `MANIFEST.json`, and `CHANGES.patch` bind exact preimages and candidate bytes. All static comparisons succeeded. Static comparison is not Lean acceptance. Root owns Git publication and all normal/kernel/full-owned verification.
