# Part 1 round 8 — three-stage historical correction, source checkpoint

**Status: UNVERIFIED_CANDIDATE until new exact-SHA core CI finishes.**

Parent HEAD: `6c37e6e4d882c07716d9f89ddf4b6799cd90aaca`.
Branch: `chatgpt/chen-p1-history`.
New production source blob: `c7cab8e6ecf517eaa09275763c10f46b5b9d7a77` (`ImbalancedChen/HistoricalThreeStageTelescope.lean`).
New complete defining-module audit source blob: `1bc2e243fe14853932a5dcd21feb4eafac061fcb` (`ImbalancedChen/HistoricalThreeStageTelescopeAudit.lean`).
Updated root source blob: `b05411de2b46214fedfd9798b83e68ada61c0550`.
Frozen manuscript `ba6ec11d800eccc54406490631895e174de85766`; shared proof baseline `1a80c1bcce67886f699d097fc37fd245cd3620bf`. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, goldbach `09b97db5764ade1246bfb77206baa1b124760958` and all manifest pins unchanged.

## Independent target

The new production module derives the third selected-cell difference, then a single exact finite third/fourth/fifth telescope on one rank-five processing-order tuple using literal projected ancestors. Fourth/fifth summands subtract their true inherited `D.old4` / `D.old5`, and missed cells contribute zero rather than discarding the ancestor. Its specialization to `actualPrimeTupleOwnCubeMinus` keeps the strict old and new own-cube gates separate. These are algebraic identities valid for any fixed table `HistoricalPrefixCapData`, not a claim that the manuscript's adopted data have been instantiated or their integrals evaluated. The sign is **new minus old** in each actual residual; a later global upper-saving sign still requires the existing tree equation.

The audit source enumerates every declaration with the new defining module, including private/generated, exports the original compiler expression type, and rejects new axioms, unsafe declarations and transitive axioms other than `propext`, `Classical.choice`, `Quot.sound`. The existing root imports this audit and preserves previous proof gates.

## Evidence status and next minimum action

The previous exact source `b416a21d70255a94dfc44c03aade3bd118de2f6e` has verified core CI `38345607447` and specialized CI `38345607444`; this checkpoint does not invalidate or rerun those leaf receipts. Before this new commit there were no active Part 1 workflows. The isolated current container lacks `lean` and `lake`, and its git has no external network. No strict local compilation, original bundled checker, defining-module runtime census, imported or output `.olean` hash is asserted for the **new** proof. The exact new commit's existing core CI must supply trustLevel=0 strict build, original leanchecker replay, full compiler-type census, and the transitive axiom gate. Specialized variable-envelope CI cannot replace root acceptance. If a core stage fails, repair its exact error; if success, preserve stage exit codes and unmodified original logs and obtain source/object/import bindings where available.

The manuscript's actual adopted historical `J/I/old/nu/cap` rows and their ancestor identities remain uninstantiated. The independently reported earlier fifth source remains `SOURCE_PENDING`. Whole-cell adoption, complete multistage/global correction, boundary/truncation, physical signed prime distribution, and final `K=8452171/1250000`, `c=49044063/25000000` bounds are still open. P2 `exact_Z` is not a stored `cap`. Next execution: read branch HEAD and exact-head core status; never start a duplicate active build.
