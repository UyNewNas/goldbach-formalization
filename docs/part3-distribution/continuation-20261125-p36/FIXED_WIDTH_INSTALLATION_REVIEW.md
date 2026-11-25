# Independent review of the fixed-width installation

**Result: installation bytes and the actual source graph passed independent checks. No Lean acceptance is claimed.**

Reviewer: `/root/p36_source_recovery`. The review read the installed canonical files and fixed Git objects without changing any source, manifest, verifier, or remote task. Only this Markdown report and its JSON companion are written by the review.

## Frozen sources and installation

All seven installed files were compared byte for byte with their recorded origins: six prepared files at `c5d32e919718a72880b17d9597cbedb592f2c0bf`, plus the fixed-width candidate at `88bad2514b057e323ed0adc00498f3af57820887`. Every length and SHA-256 value matched. The candidate remains SHA-256 `76e20ecdebb2d2d2accecef691544181703ed32cd8b38f10704100d3e18ed68a`; the interval core remains `ecdd92cc98d0a1ab993e70a256333ba6e568aab248bef2032f074bbf2fa3edfe`.

The 274 previously selected source files were independently compared with the canonical files at the parent commit, as well as with their old and new selection hashes. All 274 remain byte-identical. The manifest moves from SHA-256 `71b7e264199c2537321250353cda549621e8a4472e1e36bc6a7d3ac43ea1867e` to `d8985c91e5ffc71b7af5d4bea3a7c3ad3128733caf591dd0b3bc6357d41e66d2`, adding exactly six selected modules. The seventh installed file is the compatibility wrapper.

## Actual installed dependency graph

The graph was rebuilt from the actual canonical source bytes, after checking every selected source hash. All **280 selected modules are reachable from the 12 selected targets**, with no missing project source or cycle. All eight recorded compatibility companions match their hashes and are unreachable from those targets.

The fixed-width target reaches exactly **57 project modules**. Its complete import graph and every selected source hash match the frozen reviewed preflight. The only added direct external import is `Mathlib.Data.Fin.Tuple.Basic`.

The historical preflight baseline `f77468ef3bbc9f49294df0242079a58594ceae0679cc5d4d038c3f12a2861d4d` was independently located at commit `88bad2514b057e323ed0adc00498f3af57820887`. Exactly two selected sources differ between that historical baseline and the immediate pre-installation baseline: `P3OriginalU5AllSourceSquares` and `P3OriginalU5FreshFifthSquareSupplier`. Both are outside the fixed-width target's 57-module graph, and their import lists are unchanged. The earlier 205-module historical closure was not recomputed by this installation review.

## Verifier and acceptance boundary

The tracked verification tree is unchanged at Git tree `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`; the working tracked verification files have no diff against the parent. The source manifest bytes were also identical at the beginning and end of this review.

This review did not run Lean, an official kernel replay, a declaration/type inventory, or a transitive axiom audit. It establishes exact installation and dependency boundaries, and does not add formal acceptance or close P3.6. The JSON companion records all seven source origins and hashes, the compatibility list, and the checked manifest boundaries.
