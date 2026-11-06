# P1.4 persistent continuation — exact historical-shell vs cubic-annulus split

## Recovery coordinates

- Base actually read: `2289412178792463fdf9d5bb88a36e50e95aadc5` on `chatgpt/p1-full87-rank9-reciprocal-window-20261106`.
- Independent continuation branch: `chatgpt/p1-full87-rank9-two-sided-window-20261106`. Source/report/registry/boundary commit **`e134d56be82397970c77684ea5cc1bc207a16244`**, [skip ci]. This handoff will have its own later commit; at each later run re-read the branch's live HEAD, compare commits, and do NOT reset to old 9649ab3.
- Packet: `docs/source-only/20261106-full87-rank9-two-sided-window/`.
- Candidate source (318 lines): `P4AOriginalFull87RankNineTwoSidedWindow.lean`, GitHub blob **`db367b1558160ed9aabfab286a4a451da92b8232`**, read back. Report blob `40b8b47c1cdb8934deed48c0a531ca513920e067`, registry `ab35abcf4005d53395a98055be08990d0d50ec00`, external boundary `183fae9aed9817ea0ed9571c7ef05e804caab228`.
- Predecessor full-source import unchanged: `docs/source-only/20261106-full87-rank9-prime-crossover/P4AOriginalFull87RankNinePrimeCrossover.lean`, blob `1c04e79c04abba8e9d657a2cc71bd6d44b12bdc5`.

## Nontrivial mathematical gain, scope limited

Previously only `B*p^3 < U=max(Rparent,Rcap)` was known to be NECESSARY. The actual rank-nine three-mode threshold, for each real prime position `p>=2`, simplifies EXACTLY to `max(J,B*p^3)` with the full historical odd-square ceiling `J`. A strict choice changes precisely when `L=min(Rparent,Rcap) <= max(J,B*p^3) < U`.

The candidate establishes an exact, disjoint, endpoint-correct split:
- Historical-shell: `L <= J < U` and `B*p^3 < U` (no cubic lower cutoff for the prime);
- Cubic-annulus: `J < L <= B*p^3 < U`.

This prevents the false inference that every crossed prime must satisfy `B*p^3 >= L`. For each **actual** original prime occurrence the preceding finite `1/(p-1)` invoice is the SUM of these TWO disjoint invoices, never two payments on one prime, retaining the physical eighth mass and Euler-source ordering. The exact partition lifts to every original owner/trim cell's ordered states via the previous signed discrepancy bound. When `J<L`, historical-shell cost is provably 0. This is a finite algebraic advance; it does not yet show any invoice is asymptotically small.

## Checks and limitations

- GitHub branch HEAD after the source commit read back `e134d56...`, with full source blob `db367b...`, 318 lines, 3 unchanged documents with matched SHA and JSON parseable at creation. Static forbidden proof escape scan clean. No AGENTS.md found in relevant root and source-only ancestors. Fixed manuscript pin `9731290e...` and toolchain/mathlib/native/c/K unchanged.
- 25,000 exact integer synthetic threshold/history/level pairs (3,907 historical shell; 5,382 cubic annulus; 15,711 noncross, 18,741 threshold/history equality setups); all assertions passed. **Additionally** 12,000 exact rational/integer ordered-prime-list simulations, 83,446 prime occurrences **with duplicates retained**, 7,779 histories with `J<L`; confirmed full harmonic list invoice = disjoint shell + annulus invoice and safe-history shell=0. Synthetic samples do not replay actual saved87 or prove Lean elaboration.
- **SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT**. Did NOT run Lean/Lake, kernel replay, transitive axiom audit, original full87 geometric/numerical archives, independent review, CI, Codex, or resource upgrades. No external analytic theorem implemented/invoked; `INPUT_BOUNDARY.md` registers the relevant sources and preconditions only.

## Exact yellow obligations / concrete next move

1. **Do not treat a cubic annulus alone as the whole rank-nine invoice.** Inspect actual frozen old/new level ordering and archived 87-cell geometry at the same `rho`; establish whether `L <= J < U` can occur on the genuine licensed-eight source. If yes, derive its separate finite-to-asymptotic estimate; if excluded, prove this from real parent/cap and geometry, rather than assuming.
2. Obtain a same-rho, uniform-in-even-N bound for BOTH real physical reciprocal sums, with actual target prime deletion, fixed parameter quantifiers, and legitimate one-time reserve debit. Current source only provides an exact list-based ledger, not a normalized small-o estimate.
3. Global `RealizedHistory`, attachedLeafTest primitive/AP/centre/modulus terminal error, sixth filtering, ordinary exit integral, original saved87 gain, changed/tagged, two independent reserves and root final same-rho assembly remain open. External analytic inputs remain REGISTER_ONLY.
4. Prefer a first actual Lean v4.33.0-rc1 compilation within approved resources if later allowed; **do not trigger CI or upgrade automatically**. Validate this and predecessor proof packets for elaboration errors before any green promotion.

No main/master edits, no merge, no force push; preserve all earlier packets and independent pins.
