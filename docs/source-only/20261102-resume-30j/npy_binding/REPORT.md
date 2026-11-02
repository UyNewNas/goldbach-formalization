# J npy_binding: positional original-byte semantics

Two static Lean candidates implement a missing parser/field/order implication. The complete original-byte authenticity target remains OPEN. No compiler, build, CI, certificate replay, finite decision evaluation, new bulk literal, Git operation, quota query or subagent was used. `compiled=false`, `kernel_verified=false`, `formal_credit=0`.

The new substantive proof is `decodeChunks_getD`: induction through the existing parser identifies output position i with precisely input window `[size*i,size*i+size)`. Applying it separately at the 80-byte row and 8-byte column levels gives `decodeFrame_field`, rather than inferring a positional association from an encoder roundtrip. `take_drop_take_inside` proves the row cut does not change a contained field. Consequently `frameFieldBytes_offset` identifies the actual input field with file bytes `[128+80*i+8*c,128+80*i+8*c+8)`. Address injectivity is proved arithmetically for every row, column and byte; it is not an evaluated table guard.

`decodeFrame_field_value` identifies that window's original little-endian two's-complement signed64 value with the corresponding output column. `decodeFrame_field_bytes` additionally reconstructs the same eight input bytes, using the existing scalar reverse theorem. These are parser semantics for arbitrary successful input frames. They make no assertion about the historical file passing a test.

The second module uses `Data.P1HistoricalFifthSavedTableData.rows.toList` and the existing `ArchiveIndex` directly. Its criterion `original_parse_iff_field_association` proves both directions between the full ordered parse and positional scalar agreement with all ten original fields, under the exact header, payload length and byte-domain conditions. The reverse direction first derives existence of a parse from those structural conditions, then uses list extensionality and the injective ten-field wire interface to identify every output position. It does not assume a successful parse of the desired table, a typed signed-range guard, or a whole-table check flag.

The ordered source is the existing 143-block hub, not a new array. The existing `rows_split_at_block` theorem exposes the same conclusion at every block boundary. The zero-based mask-slot equivalence is retained. Conditional transport of F's `actual_typed_keys_nodup` and `archiveRow_baseGeometry` reuses those declarations unchanged; no new key/range/gate decision term is introduced. Those transports are bookkeeping consequences and are not claimed as new uniqueness or geometry proofs.

## Original source and manuscript

Read the assigned TASKS row and README, F/H upper_mesh reports and registries, current frame/payload/completeness/arithmetic/table parsers, E archive index definitions, frozen typed hub/shape source and the original witness exporter. The typed hub currently lives at its frozen draft path, not `ImbalancedChen/Data`; this is an installation boundary, not missing data. Exact paths, hashes and proposed installation targets are in REGISTRY.json.

Current manuscript `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, lines 368-375 preserves actual prefix ancestry and same-stage multiplicity. Lines 386-509 include the literal residual density and finite compilation argument; lines 1310-1435 distinguish complete numerical families, source bindings and earlier complete runs from analytic identities. The associated upper completion module, lines 65-76 and 185-214, retains the original fifth cube, genuine current parent and causal order. The parser work supplies a missing source-address implication needed before those actual rows can inherit analytic meaning. It proves no new analytic gain, parent licence or density estimate. Original c=49044063/25000000 and K=8452171/1250000 are unchanged and do not enter byte parsing.

`../goldbach-research/export_fifth_prefix_jensen_witness.py`, lines 9-25, writes the original ten-column order `[n,l1,l2,l3,l4,l5,mask,vertex_gap_sum,A,B]` into a signed int64 NumPy member. Existing `P1HistoricalFifthNpyFrame` checks exactly the archived 128-byte NPY v1.0 prefix: `<i8`, C order False, shape `(292633,10)`, header text length 118 and all padding/newline bytes. This is a fixed-frame validator, not a general dictionary parser. This delivery neither reruns the exporter nor traverses the mathematical payload.

The original `cells.npy` is present at the pinned pure-data path, 23,410,768 bytes with SHA256 `d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7`. The existing typed hub contains all 143 blocks; its existing shape theorem gives 292633 ordered rows, with the final block of 1817 after 142 blocks of 2048. Metadata hashes were checked only as source provenance. They do not prove binary semantics, scalar agreement or authenticity.

## Exact remaining immutable-byte witness

No closed Lean object representing the complete original file bytes is supplied by the inspected parser/hub sources. The binary file itself is present. For a future immutable, kernel-readable representation `originalBytes : List Nat` of precisely that file, the remaining witness is:

1. `originalBytes.take authenticHeader.length = authenticHeader`.
2. `(originalBytes.drop authenticHeader.length).length = 80 * rowCount` and every payload entry is less than 256.
3. `OriginalFieldAssociation originalBytes`: for EVERY existing `i : ArchiveIndex` and EVERY `c : Fin 10`, the signed little-endian value of the eight original file bytes beginning at `128+80*i.val+8*c.val` equals `wireColumns (archiveRow i) c`.

The third item is 2,926,330 positional scalar obligations over the independent original byte object and the independent actual typed table. This delivery specifies and decomposes that obligation; it does not prove it for the historical file. The criterion is equivalent to the target under structural validity and is explicitly not accepted as an original-byte witness by itself. A hash comparison, a typed self-encoding, or a proof that `decodeFrame (encodeFrame typedRows)` succeeds does not discharge it. No source-byte constant, success theorem or data guard is fabricated.

F's sorted-key/lower-key and prior typed-range decision bodies remain uncompiled and unevaluated dependencies. Full physical/current-parent/history gates remain with their separate suppliers. No passing raw header/payload can itself imply those gates. The actual Q3/Q4 owner, full same-policy history and final analytic integral/constant bounds remain OPEN. No manuscript contradiction was established.

## Verification boundary

Only manual source/mathematical inspection, text/declaration inventories, existence checks and raw SHA256/file-size reads were used. The exact 143-block source hashes were compared with the existing E authority manifest, with no arithmetic/payload parsing. Direct import pins include the frozen source-only predecessors and proposed installation paths; no production or older batch file was changed. Independent review, installation and user-owned compilation are still required. Static source completion is not a kernel verification claim.
