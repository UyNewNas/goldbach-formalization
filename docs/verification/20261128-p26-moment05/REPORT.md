# P2.6: complete original Cell05 moment parse, decode and shape

Base: `6638b10044b8f48d22920bf73ddbdb9e72417600`. `P2_6_complete` remains false.

The previously missing original moment input is now available. All 26 original
inputs were recovered, matched byte-for-byte to the existing archive-core ledger,
published with explicit user authorization, downloaded again and checked. Their
separate archive commit is `a2a7146f8de2beb8fc79f09d111f4af023840580` on
`artifacts/p26-original13-inputs-201942a4-20261127`. See the adjacent
`20261128-p26-original-inputs/READBACK.json`.

Cell05 has 28,973 original ASCII bytes, preserving CRLF. Its SHA256 is
`9a85e92f79b24c2b2361717d3a29ecb6167059e5509211c2f3fb290b5284fe2c`.
The existing `ArchiveMomentData05` owner and original packed-input loader are
unchanged. The new input interfaces prove the exact count and list spans.

The original pure `SourceJson` reader is unchanged. Checked arbitrary-tail and
accumulator equations, exact raw-span bindings, and the original parser's fuel
rule establish a complete parse of the original input. The original typed
`decodeMoments` then returns `momentConcrete05`. All 56 rows are retained, with
their original IDs, ten Q80 factor fields, and old/new Q96 fields. Metadata fixes
cell 5, dimension 8, nine vertices, ten factors, degree 6/3, and denominators
`2^80`/`2^96`. Bounded lookups are connected to the original decoded array.

The Cell00 layout is only a source-generation template. Cell05 quotations and
typed values were proposed from its own original bytes. Lean checks every parser
and decoder equation. The root fuel constant is derived from Cell05's own length:
`28869 + 105 = 28973 + 1`. No host parser result is accepted as a proof.

Verification completed: a fresh 43-module project build, then 36 normal
compilations with `--trust=0` and warnings as errors, 36 independent stock
`leanchecker` replays, and a complete serialized/environment declaration
inventory, full-type and transitive-axiom audit. All **949 owned declarations**
passed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorry`,
`admit`, `native_decide`, new axiom or assumed parse-success fact was added.

`RUN.json`, `NORMAL_BUILD.json`, the logs and `owned-declarations.json` retain the
verification records. `project-objects.tar.xz` contains exactly the 43 project
objects in this verified context; each archive member was read back and compared
to the pinned object bytes. `CAPSULE.json` records its hash and size. Lean is
4.33.0-rc1 and Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

```sh
python3 -B tools/p26/analytic-closure/build_moment05.py
python3 -B tools/p26/analytic-closure/check_moment05.py
python3 -B tools/p26/analytic-closure/package_moment05.py
```

This closes the original Cell05 input, parse, decode and shape boundary. It does
not validate the saved Q80/Q96 inequalities or attach those floors to real
integrals. The higher-moment analytic closure, complete 13-family/28,918-row
certificate, simplex ownership/coverage and final integral endpoint remain open.
The separate higher-moment diagnostic build is not promoted by these results.
