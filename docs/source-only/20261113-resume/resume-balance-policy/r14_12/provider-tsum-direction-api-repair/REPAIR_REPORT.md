# Canonical old-provider sum-exchange direction repair

**SOURCE ONLY / UNCOMPILED.** This successor changes three rewrite expressions,
one per source. Compiled modules: **0**; kernel-verified modules: **0**.

## Exact inputs and duplicate check

All three exact paths were first published in
`484d8ffc8f79e7c213b33ae86a8d960cd4da6de4`. The corresponding objects at current
source `06f3e98f81031d292c99cee98fd14c78909e3254` were read independently and
are byte-identical to the publication. Their SHA256/Git blobs also match the
exact artifacts selected by 05's `CUTOFF_TRACE_ALLOWLIST.json` and
`SCALAR_SPECTRUM_ALLOWLIST.json`. Full paths and all raw hashes are in
`SOURCE_PINS_AND_STATIC_CHECKS.json`.

| Path suffix within `r14_09/avgj-reciprocity-next/` | Input blob | Input bytes | Actual original rewrite line |
| --- | --- | ---: | ---: |
| `prescribed-cutoff-trace-r2/Part3OriginalSwitchedMaassExchange.lean` | `25739275b62025ab93df7018e35163030e6575f8` | 7760 | 106 |
| `prescribed-cutoff-trace-r2/Part3OriginalSwitchedHolExchange.lean` | `5b848afad3a1c0915feb7884f766311becda4a07` | 5384 | 96 |
| `same-infinity-scalar-spectrum-r2/Part3OriginalSameInfinityTensorSpectrum.lean` | `40ac701e0de3a6be2d3ff722a3c3a19abceb94e9` | 5765 | 74 |

The third line number is 74 in the actual selected Tensor postimage, rather
than the approximate line 80 in the task description. It was checked by its
own source and function types before being included. No earlier same-path
published repair was found in local Git history; 05 confirmed no duplicate
successor had been written. The original non-r2 files and 09's current separate
holR2 work are not inputs and are not changed.

## Fixed-host direction and the three concrete types

The fixed host is mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, exact file
`Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean`, Git blob
`0c1829e9cc57418b3746581d8bd9ab86c1bf6a62`, 14267 bytes, SHA256
`3d789b5fa814405e5bcc74a9ab48ce1f5a13dec070550291b6047c3d2c997283`.
The exact Git source was read statically. The `@[to_additive Summable.prod]`
declaration at line 235 preserves the first product index as the outer sum.
The `@[to_additive]` declaration at line 260 generates the opposite-order
equality for `Summable.tsum_comm`.

For `s : Summable (Function.uncurry F)` with `F : K → I → ℂ`, the relevant
generated additive types are:

```lean
s.prod.hasSum :
  HasSum (fun k => ∑' i, F k i) (∑' k, ∑' i, F k i)

s.tsum_comm :
  (∑' i, ∑' k, F k i) = (∑' k, ∑' i, F k i)
```

Thus the value of `prod.hasSum` matches the **right** side of `tsum_comm`.
To use the existing inner-mode sum identity, rewrite that value with the
symmetric equality, obtaining `∑' i, ∑' k, F k i`. The original forward rewrite
has the wrong orientation for this value.

The actual functions and inner-mode identities are:

| Source | First index K | Second index I | Unchanged next step |
| --- | --- | --- | --- |
| MaassExchange | mode `k : ℤ` | actual Maass `Idx` | `(point i).tsum_eq` identifies `∑' k, H k i` with `nativeWeight * disc` |
| HolExchange | mode `k : ℤ` | weight `j : ℕ` | `row j` identifies `∑' k, F k j` with the original finite `BasisIndex q.val (j+1)` sum |
| TensorSpectrum | original full `Modes` | `actualCuspBasisIndex q.val (NeZero.pos q.val)` | `individual i` identifies `∑' v, D v i` with `packet * disc` |

Tensor therefore has the same confirmed orientation issue, not merely a
similar-looking tactic. Its `ds` is explicitly summability of `uncurry D` with
mode first and actual cusp-basis index second.

## Minimal proof changes

```lean
-- MaassExchange
rw [hs.tsum_comm.symm] at DS

-- HolExchange
rw [SF.tsum_comm.symm] at H

-- TensorSpectrum
rw [ds.tsum_comm.symm] at discrete
```

Each line differs from the original only by appending `.symm` to the equality.
All subsequent `point`/`row`/`individual` rewrites and every other proof byte
remain unchanged. The absolute double-summability proofs are retained exactly;
no extra summability or target identity is assumed. All full Maass indices,
all holomorphic weights and their original finite bases, all tensor modes,
all continuous terms, normalization and cutoff arguments are preserved. This
is a formal equality-transport direction repair, with no new mathematical
estimate or relaxed spectral range.

The 3 Maass, 2 Hol and 6 Tensor declaration headers (11 total) are byte-identical.
Imports, local instances, definitions, theorem parameters, premises, numbers
and index ranges are unchanged. Exact single-expression replacement reconstructs
each complete postimage. No `sorry`, `admit`, new axiom, opaque target, or target
hypothesis is introduced. No global replacement of other `tsum_comm` uses is
performed; forward uses in other proof contexts are outside this repair.

Postimages:

- MaassExchange: 7765 bytes, SHA256
  `4b6c8ce60e99f24d4d009924bb83127eb325d0730993c576a741302cb59ea623`.
- HolExchange: 5389 bytes, SHA256
  `f29a89d0813c018744508571f1837f140b457d6b03353ba55f7dcb2a6f4dec79`.
- TensorSpectrum: 5770 bytes, SHA256
  `732768d836b4bc9a154f17d23118414dda51aa6b4fb64b2acce621dcc4b91bfa`.

Only this separate successor directory was written. Canonical published files,
old freezes, 09's separate holR2 work and the protected dirty continuation were
not modified. No local Lean/Lake/LSP, environment/setup, stage, collector,
project helper, fixture, runtime/certificate, Git/GitHub mutation, CI, quota
check or agent spawn occurred. All evidence is static source/hash/JSON/read-only
Git evidence. Independent 05 source review must precede any dependency update.
