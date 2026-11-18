# P5.6 / h34 — actual-Q even-N signed first-exit bound on matched invisible receipts

Date: 2026-11-19 (Asia/Shanghai).
Baseline **verified branch HEAD**: `7c4000cfcfb61a791db6f5eb3be87d6ee453f766`.
Lean mathematical source commit: `777b6b8521a86e53f651fc1b6fe1668c05051294`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Manuscript: `ba6ec11d800eccc54406490631895e174de85766` (unchanged).
Pinned Lean `v4.33.0-rc1`; pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Mathematical advance (source-only candidates)

The previous root-matched packet separated genuine same-root 430-edge-invisible first-excluded keys from wrong-root keys, but gave only an exact signed ledger. The older EvenSignedExitBounds theorem establishes a NEGATIVE genuine rank-two signed Euler correction at a fixed caller-Q for an eligible original fourth-lane key, assuming **2 divides N** and **z0 <= cap**.

The new `Part5OriginalH430ActualQMatchedExitSign.lean` proves source candidates that remove the fixed-Q mismatch WITHOUT replacing actual original Q:

1. `actual_Q_key_is_fourth_key_at_own_Q`: an actual key `k = (Q,p,ell)` drawn from the original two tag-preserving first-excluded sources belongs to the genuine fourth-lane key set **at k.1**, using the original tagged receipt's `originalPhysicalQ` and the distinct frozenOnly/rejectedFrozen first-bad-factor functions. This discharges rather than assumes the old lemma's fixed-Q source membership.
2. `actual_Q_key_signed_exit_interval`: transport the already proved old conditional even-N interval at each real Q, yielding
   `-originalEventMass(k.2) <= actualRankTwoSignedExit(N,cap,lower,k.1,k.2) <= 0` whenever `2 | N` and `z0 <= cap`.
3. `matched_invisible_signed_exit_interval`: specialize to genuine root-matched, fully 430-edge-invisible keys, NOT all wrong-root keys. The real historical signed Euler suffix is unchanged.
4. `matched_receipts_signed_fibres` and `matched_receipts_card_by_keys`: exact arbitrary-weight tagged q-receipt and unit-cardinality correspondence for the matched subset. Different q and U3/U4 tags are not identified by physical keys.
5. `matched_unit_receipt_unpaid_lower`: subtracting the nonpositive once-per-physical-key historical correction from the true UNIT tagged receipt source leaves a remaining gap at least the full matched receipt count; not just number of keys.
6. `matched_unit_unpaid_pos_of_receipt`: if at least one genuinely matched/invisible original receipt exists, the exact unit-count gap is strictly positive. The file does NOT claim the matched subset is nonempty.

The new result is a directional **obstruction**, not a paid count: a negative signed first-excluded correction by itself cannot be credited as positive root selected-count capacity. No fourth `Choice` constructor is postulated, no owner is inferred from an equal event label, and no U3/U4 weight is replaced by the unit weight in the final theorem. The unit receipt result is explicitly a *diagnostic* count inequality only.

## Remains INTERNAL / OPEN

- Real full/selected/inherited source to true selected-history `Fin` owner, exact tag/q multiplicities, root norm 7/2, six rejection classes and signed residual quantitative payment.
- Genuine same-root non-edge historical rejection event's lawful relation to actual CLOSED-CELL request actions (the resolver still has only retained, Buchstab and bank).
- Remaining request-level Buchstab/retention positive source, all-action CLOSED-CELL induction, base/seed and correct floor/feedback payment.
- Manuscript PP/same-rho, native-history mass controls, outer integral–Theta–actual-count bridge and one shared 430+11 nested causal construction.
- Actual fixed-environment Lean/Lake compile, kernel replay, transitive-axiom audit and inherited finite certificate replay.

## Validation & concurrency

Remote branch HEAD was checked before mutation. GitHub `create_file` wrote a NEW path under the dedicated h34 source-only branch; post-write fetched the exact Git blob `0ae528e80794023b566654557a1c5802bbc963f3` and verified compare is **ahead 1 / behind 0** from baseline, no other file touched by the mathematical source commit.

Local `lean`, `lake`, `elan` are absent, and the native git remote failed with `Could not resolve host: github.com`. A genuine Lean/Lake compilation, kernel replay, transitive axiom audit and finite certificate evaluation were NOT run. Syntactic scans and remote blob correspondence DO NOT constitute Lean validation. `SOURCE_ONLY / UNCOMPILED / UNEVALUATED`; no green node.

No manuscript, P1.4/P3.6, CI or dependency file changed. No existing parallel h34 write was detected in the baseline/preflight; future writers must recheck the branch HEAD before mutations.
