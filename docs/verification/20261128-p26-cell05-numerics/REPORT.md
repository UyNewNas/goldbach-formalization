# P2.6: all original Cell05 Q80 and Q96 numerical records

Base: `6a2d6aeb7aa64ad5e307701dd30f39d1850bef00`.
`P2_6_complete` remains false.

All **560 original Q80 factor integers** now equal the unchanged frozen
evaluator on the actual parser-bound Cell05 coordinates. The evaluator uses
the existing nine-node prefix table, the canonical nonnegative rational
encodings, the exact degree-six gap expression, and integer floor at `2^80`.
No stored moment, host-computed coefficient, floor, or parse-success fact is
supplied as a hypothesis. Four rows per block keep the kernel computations
bounded; the complete theorem includes all 56 rows and all ten factors.

All **56 original new Q96 integers** now equal the original new-floor evaluator.
The proof first identifies its Q80 total with the sum of the original stored
factor integers divided by `2^80`. It then checks the unchanged cubic correction
and `2^96` floor. Reusing the 560 proved equalities avoids evaluating the prefix
table again inside each Q96 check. It does not replace the evaluator.

The old Q96 integers also agree with the geometry Jensen records. The original
stored Q80 factors are nonnegative, every stored new Q96 is at least its old Q96,
and each stored new integer divided by `2^96` is exactly the computed rational
`simplexLowerQ96`. There is no Q112 step or Q96-to-Q80 conversion.

The two source files are the exact original Cell05 geometry and moment inputs,
with SHA256 respectively
`e601ac9ceda569646f06a64f4baddcf9cd405cde1e377a323a238ad4e4681b82` and
`9a85e92f79b24c2b2361717d3a29ecb6167059e5509211c2f3fb290b5284fe2c`.
Their original bytes are archived at commit
`a2a7146f8de2beb8fc79f09d111f4af023840580` with explicit user authorization.

## Verification and dependency context

The pilot, complete Q80 certificate, and Q96 connection passed **17 normal
compilations**, **17 independent stock-kernel replays**, and **three complete
serialized/environment declaration and full-type/transitive-axiom audits**.
All **89 owned declarations** passed: 4 + 71 + 14. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Unsafe, partial and axiom declarations,
truncated types and forbidden transitive axioms are rejected.

The earlier first-moment context has 139 project modules and the original
moment-input context has 43. Their seven shared modules have identical source
and object bytes. `BASE_CONTEXT.json` records the checked 175-module union.
The new targets give the final **192-object** project closure. No P2.5 donor or
alternate native project cache is searched. Lean is 4.33.0-rc1; Mathlib is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, with unchanged locked dependencies.

Each phase directory retains its exact command records, logs and owned inventory.
`project-objects.tar.xz` includes exactly the final 192 project objects; every
archive member was read back and compared with its pinned object bytes.
`CAPSULE.json` pins the archive and phase records. `PREFLIGHT.json` is explicitly
an advisory Python rational-arithmetic replay and contributes no Lean credit.

```sh
python3 -B tools/p26/analytic-closure/compose_numeric05.py
python3 -B tools/p26/analytic-closure/check_q80_pilot.py
python3 -B tools/p26/analytic-closure/check_q80_complete.py
python3 -B tools/p26/analytic-closure/check_q96_records.py
python3 -B tools/p26/analytic-closure/package_numeric05.py
```

The completed statements are finite arithmetic equalities on the original
decoded data. The separate higher-moment analytic context is still being
verified. Actual simplex-map/integral attachment and the full 13-family,
28,918-row ownership/coverage and final integral endpoint are not certified
by this numerical certificate. The MCP service and managed tunnel remained
healthy while the checks ran through its bounded single-task queue.
