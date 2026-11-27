# Cell05 publication source scope review

**PASS** against `447127edc4a97db1ebc3fa9c1793e390ef2e3e49` on `refs/heads/work/p2-6-source-closure-20261125`.

The exact commit root tree is `1ae16189f3cf4fc5cc22ff6e17f6329028d7460d`; its ImbalancedChen subtree is `8c19226d8e13537d02bbbd8214c612cfb835cc09` (6181 entries, not truncated). Every listed remote blob was fetched by its Git SHA, and its byte length and Git blob SHA were recomputed before direct byte comparison.

**Only one Lean source path changes: `ImbalancedChen/P2OriginalSaving19Geometry05ScalableShape.lean`. All nine paths already exist. The other eight are byte-identical to this exact head and to the preserved original remaining9 package.**

| Suffix | Remote bytes | Publication action |
| --- | ---: | --- |
| SimplicesValue | 2497 | unchanged |
| SimplicesField | 3338 | unchanged |
| PhysicalVolumeField | 4126 | unchanged |
| WholeValue | 4533 | unchanged |
| WholeParse | 2496 | unchanged |
| DecodeFields | 7860 | unchanged |
| Decoded | 5109 | unchanged |
| ShapeRows | 9817 | unchanged |
| Shape | 7353 | update existing file to7508bytes |

## Shape proof-only change

The old source is7353bytes/SHA256 `d530f5979a380f28ff750c47114b44a38f7d8af4c882f68ac1ffa0ae470cc905`; the exact compiled/reviewed replacement is7508bytes/SHA256 `fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb`.

Exactly six proof fragments change. The helper `property_of_list_toArray` replaces its unnecessary `simpa using (Array.getElem_mem_toList hi)` with `simp`. Five fields of `concreteGeometry05_shape` introduce the dependent Fin index and apply the existing theorem to a Fin value with the same `.val`; the corresponding size theorem transports only its bound proof. The fields are `facetIndicesBound`, `rows`, `vertices`, `facets`, and `faces`.

Applying exactly those six replacements to the actual remote source reproduces the current source byte-for-byte. All bytes outside those fragments match. All18 theorem names and declaration types, all3 imports, the complete GeometryShape structure, options, namespaces and axiom-print directives remain unchanged. The accepted source copy in the real Shape export also matches this candidate byte-for-byte.

## Separate proof records that the checkpoint must preserve

| Evidence family | Original context targets | Accepted targets/checks | Full owned declarations | State to preserve |
| --- | ---: | --- | ---: | --- |
| Original14 prefix |14|13 /39|112|Original continuation remains stopped at ShapeArrays normal failure|
| Separate ShapeArrays repair |1|1 /3|28|Its original independent SUCCESS|
| Original remaining9 prefix |9|8 /24|116|Original continuation remains stopped at Shape normal failure|
| New separate Shape completion |1|1 /3|40|New independent SUCCESS and external readback PASS|

The original14 continuation keeps37 newly executed commands (36 accepted plus one failed) and3 reused pilot records. The original9 continuation keeps22 newly executed commands (21 accepted plus one failed) and3 reused pilot records. Neither failed original batch acquires a full SUCCESS. The new3 records belong to the new single-owner context and its repaired source, never to the original nine-target context.

Across these four connection families only, the aggregate is23 owners /69 accepted checks /296 owned declarations:66 historical checks plus3 new checks. This is not a count of every declaration in all126 project modules. New Shape has125 reused dependencies and126 actual project imports. The old normal commands did not explicitly set trust0. The new normal and owned commands explicitly use `--trust=0` and `-DwarningAsError=true`; the kernel command uses the pinned stock leanchecker.

The final external gate is `PASS_REAL_SHAPE_EXPORT_INDEPENDENT_READBACK` for job `64419527e8294cd2880cc7575368f6d5`. Its report is9574bytes/SHA256 `f4945da9830a798bc2734c1b2ea0e77cad2c0541e95b929b33b5840fa7e68115`:40 full-owned declarations,18 printed declarations,126 project imports and one99952byte object shared by all3 modes. No old proof was rerun.

## Endpoint and publication boundary

The endpoint states that the actual original packed Cell05 string parses and decodes to `concreteGeometry05`, and that this decoder output satisfies the unchanged finite `GeometryShape` predicate. It does not establish geometric realization, simplex coverage/disjointness/ownership, determinant or volume semantics, or integral identities. **P2_6_complete remains false.**

Publish the exact reviewed Shape source with the separate original and new evidence contexts. Preserve both historical failed chains, the original guard and original context references, the explicit recovered current-runtime certificate, and the separate combined index. Build on the reviewed head or recheck source identities if that head advances. This review made no main-repository edits, cloud calls, Lean invocations or publication actions.
