# P1.4 original descending15 + ascendingPair13 strict interiors

## Verified baseline and same-source continuation
Checked branch `chatgpt/p1-full87-h5h7-original-interiors-20261109` matches exact HEAD `24afacb9a441e9e584652d27e92daed1fa903ecc` (identical by compare), and read its REPORT.md, REGISTRY.json, INPUT_BOUNDARY.md, HANDOFF.md and complete candidate Lean. No AGENTS.md at root, docs, docs/source-only, ImbalancedChen. Created a **new independent child branch** `chatgpt/p1-full87-desc15-ascpair13-original-interiors-20261109` based on that commit; no master/main changes or concurrent-branch overwrites.

Original frozen source map is the actual `P4AOriginalFull87SourceDictionary.Source`, with exact `.descending i` and `.ascendingPair i` selectors; **not** an artificial Source, mask or requested arithmetic-population structure field. Real original literal modules:
- `ImbalancedChen/OriginalDescendingFifteenLiteralAffineRows.lean` Git blob `817b4c8c98ff24864a2eb414721b5e7390d7b459` (all 15*96 exported rows).
- `ImbalancedChen/OriginalAscendingThirteenLiteralAffineRows.lean` Git blob `48b4f14ec8baf09b9760289f65a7385bf6595e9e` (all 13*97 exported rows).
- The full87 dictionary defines `.descending i` and `.ascendingPair i` by those exact StrictExportedRows, global indices 15..29 and 45..57.

## Actual mathematical increment
Constructed 28 new distinct 8D rational points of denominator 100000000 (15 descending and 13 ascending-pair) using projection against the original literal exported coefficient tables. Re-read **full original literalPool and literalIndex**, then used exact BigInt rational arithmetic (not floating-point acceptance) against **all 2701 real original rows** and the rounded Lean point table. Exact result:
- 2701/2701 satisfied `a[0] + Σ a[j+1]*point[j] >= 9/1000000`, 0 failures.
- Minimum exact margin **289/25000000** at ascendingPair i=0, row r=19 (zero based), and maximal absolute coordinate slope **11/2**.
- Safe common slope 6; with all eight coordinate perturbations `|s_j-t_j| <= 1/100000000`, row loss <= `8*6/100000000 = 3/6250000`.
- Hence every actual original row on the full 8D positive-width box remains at least `1/125000>0`, with a proved-candidate direct membership statement for **the original full87 Source** and zero new axioms. The bound is intentionally conservative (9e-6 − 0.48e-6 >= 8e-6).

These are fresh feasibility reconstructions, **not original saved87 .witness.json values**, not real N-dependent prime tuples, not original signed source gain, and not a dynamic `actualParent` proof. Earlier 47 disjoint continuous geometry Source candidate cells remain; these 28 make **75/87 source interior candidates**. Twelve original H3 first-failure cells remain without this specific geometric certificate. The 75/87 count is NOT progress percentage toward the theorem.

## Checks and exact status
- Executed exact BigInt rational verification of all 2701 original rows from live connected source text and generated rounded point numerators. Max slope and minimum rational bound checked. The saved `CHECK_ORIGINAL_ROWS.py` provides a checkout replay but was not itself run in a complete repository environment.
- No local `lean`, `lake`, `elan`, fixed mathlib/native dependency tree or Docker available (checked). **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; these `decide` candidate proof bodies have not been elaborated, kernel-replayed or independently reviewed. No transitive axiom audit or original saved87 numerical replay.
- No CI dispatch, Codex, pin changes, cloud expansion, forced ref update, master/main mutation, or user-machine access.

## Remaining exact obligations
- 12 original H3 geometries if useful, plus **actual frozen saved87 witness bytes**, normalized original 87 source integrals, and claimed signed numeric gain.
- N-dependent physical prime tuple Source membership, actual sixth parent, common fourth/fifth history, true original RAW/LICENSED and full beta occurrence multiplicities, stopped/frontier boundaries.
- Original PP adapter for real admissible `W_N` and integer `X`, low/high-q errors relative to common `H_N`, ordinary integral, raw/finite/filtered loss, rank9, changed/tagged, and independent compiler/density reserve books.
- Pinned Lean compile, kernel replay, transitive axiom audit and independent review.

**Next specific action:** inspect H3 original literal source and/or recover archived saved87 raw witness; never infer arithmetic membership from continuous interior. Keep P1.4 YELLOW.
