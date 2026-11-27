# P2.5 HalfOpen continuation

This continuation reuses the previously prepared proof-only repair of
`ImbalancedChen/P4AOriginalCell0HalfOpenPrimeCarrier.lean`.

At publication of this source checkpoint, Lean compilation, independent kernel
replay and the complete owned-declaration audit of the repaired owner are
**pending**. This document does not claim that P2.5 is complete.

## Exact source and scope

- Base: `9b6f207f1f3f0138a7a67be3eb34550e5708d801` on
  `work/p2-5-saving16-20261125`.
- Failed source SHA-256:
  `f06ea67a68c218279ed051108ca17b1f77271e5bc680c207cf085188d9c89a9d`.
- Reused candidate SHA-256:
  `c629a82f73a6ccd83286745cbbe235def6ed00d752e83e11f5854e1033bab9b0`.
- The 31 declaration headers, 18 theorem statements, all definitions, imports,
  options and unrelated proofs are unchanged. The repair changes seven proof
  bodies in response to nine actual R18 diagnostics.
- The changes remove an unused cast tactic; use the appropriate additive
  monotonicity lemma; make rational-to-real order transport explicit; simplify
  `Fin.castLE` at zero; expose a definitionally equal affine row before rewriting;
  and unfold function composition in the endpoint convergence proof.

No axiom, admission, unsafe declaration, native decision procedure or relaxed
verification option is introduced. The pointwise eventual-mesh statement and
the explicit `CurrentParentGuard` premise retain their original scope.

## Evidence already available

The preserved R18 terminal result, dated 2026-11-27 07:26:27 UTC, reports
362/377 ordinary modules and 54/69 accepted owned targets. The failed owner is
HalfOpen; the other 14 entries are dependent blocked modules. These are
historical results, not new acceptance from this continuation.

The complete R18 export and portions of its runtime cache are unavailable.
The existing R19 controller's complete-export gate is preserved. Partial
transport must not be represented as a complete old receipt. Exact surviving
objects are recovered by their existing source/object hashes; genuinely
unavailable objects require a separately recorded fresh build.

## Manuscript boundary

The reference is the frozen 1106 manuscript at
`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`,
under `paper/release-20261106/`.

The carrier implements the existing finite half-open refinement and strict
affine margins. It does not by itself establish all fourteen physical cells,
the same-policy signed integral envelope or the quantitative distribution
error estimate. Existing successor `P4AOriginalCell0ActualSixthParentGuard`
already contains the candidate derivation of the true sixth-parent guard and
must be reused after this import blocker is removed.
