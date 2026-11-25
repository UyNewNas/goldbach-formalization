# P2 strict06: preserve the base filter's Decidable instance

## Completed run and exact failure

The original strict checker compiled `a2dcc3fe90a4e22e58c4c683ca9e2736b05cf522`; the completed batch has 286/321 successful modules. Complete log: `docs/source-only/20261125-p24-original-compact/p2-strict-symbolic-06.log`, 13,454 bytes, SHA-256 `501f0a48515e5cae43d70408517a6d46cabc6c5c419b85d3cbe736e40cfc12f7`.

The assigned selector now has only the line 227 instance error. At `of_decide_eq_true hr`, the synthesized instance is `(153*D-96*lo 2).decLe (256*T)`, while the instance already present in the filter evidence is `Classical.propDecidable (rootTest lo hi D T Candidate.base)`. The earlier dependent-match supplier errors do not recur in this run; their proofs are left byte-identical.

Local baseline HEAD: `0d8eba1fae2584db1fdbc0fd29f8400c56f8bf0d`. The assigned source initially matched `a2dcc3fe` exactly.

## Boundary and minimal repair

Rechecked the fixed base branch of `rootTest`, the classical `decide` inside `sourceCandidates`, and the existing filter/reflection interfaces. The frozen 1106 producer's base plane `(153,0,0,-96,256)` and whole-box upper-root filter describe the same fixed B-plane inequality. This uses only those plane/filter clauses, without substituting the Q80 producer's different candidate order or score for the preserved auxiliary selector. Frozen publication commit is `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`; cached `certify_extended_prefix.py` SHA-256 is `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.

This is an expression/typeclass-instance problem, not a missing arithmetic or analytic derivation. The candidate replaces only the final reflection line in `selected_base_root` with:

```lean
  letI : Decidable (rootTest lo hi D T .base) := Classical.propDecidable _
  have hroot : rootTest lo hi D T .base := of_decide_eq_true hr
  exact hroot
```

The local instance preserves the filter's original decision instance. The typed intermediate proposition keeps Boolean reflection at the original `rootTest` expression; only afterward does `exact` use definitional equality with `153*D-96*lo 2 ≤ 256*T`. No decision expression or selector computation is changed. No new hypothesis, weakened boundary or additional mathematical statement is introduced.

## Frozen evidence and verification boundary

- Before source SHA-256: `a6ab617c31b85f34243414b7edab32173a2193fd3de58159c61b7aa140e7d35f`.
- Candidate source SHA-256: `23c398d3d6da90ff7359444b8d443d6bf045747ed4427cf0ed2ecf059b895945`.
- Exact-byte reconstruction from `a2dcc3fe` confirms this single replacement is the entire source change. All 18 theorem headers, 15 complete computational declaration blocks, the sole import, every other proof body and all options remain unchanged. Scoped `git diff --check` passes.
- Independent read-only review by `p24_project_cache_reuse` agrees that the local instance plus typed intermediate addresses the reported instance mismatch and avoids a new generic helper. It found no static blocker; it did not edit or compile.

Only this Lean file and this new note were edited. No source option, linter exception, proof escape, index, commit, ref, remote input or compiler task was changed. This candidate has not been compiled; acceptance remains pending the parent's unchanged original strict checker.
