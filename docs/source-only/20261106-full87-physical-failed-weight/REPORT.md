# P1.4 — real weighted failure occurrences, not unit-event weights

**SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT. P1.4 YELLOW.**

## Recovery, pins and exact source

Verified predecessor was `44731a0f9184b3ac7588f4ca1b3af815a45aa332` on `chatgpt/p1-full87-actual-deletion-once-20261106`, and it remains unchanged. Independent continuation branch: `chatgpt/p1-full87-physical-failed-weight-20261106`. Source commits `e780b51a4eddf34fe81596e74c5afa64c7d02b00` (initial) and `a5f54294ee4f1949228aa5db557b09cff2faac33` (reused existing prime-density supplier). Source file `docs/source-only/20261106-full87-physical-failed-weight/P4AOriginalFull87PhysicalFailedWeights.lean`, Git blob `3d1bac2ca4ce68fe1991373d2aaada47db1223a2`; three source-only candidate theorem bodies.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, §4, especially `eq:current-upper-exit` and `g_N(p)=1_{p>2,p∤N}/(p-1)`. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants `c=49044063/25000000` and `K=8452171/1250000` unchanged.

## Newly covered *candidate* mathematics

1. Generic induction over the EXISTING `firstExitRejectedAttempts` select/skip recursion. Any physical failed event has `remaining=before++rejected::smaller`, `chosen <+ before`, `older=chosen.reverse++pre`, and **exact incoming mass** `a.mass=mass*prod(chosen.map h)`. Only successfully selected primes enter incoming mass; rejected `p` enters `a.value h` once, together with its one Euler suffix.
2. Independently of arbitrary local h/k and their initial masses, the ORDERED lists of `(older,rejected,smaller,positive)` of the physical and unit recursions are equal. This is list equality, NOT `Finset` deduplication. It preserves occurrence multiplicity, sign, skipped branches and actual policy decisions.
3. For an owned actual original87 eighth state from the existing sixth policy and either frozen `useParent` choice, initialize the physical continuation with **`s.mass * prod(s.selectedPrefix.map halfProductDensity)`** (not bare unit `s.mass`). On the SAME target-deleted `s.remaining`, every selected continuation prime and rejected prime satisfies `p>2`, `p∤N`, and `halfProductDensity p=1/(p-1)`. The equality reuses the existing `chenInitialBoundingSieve_prime_density` lemma and the exact `owned87_eighth_state_exact_carrier` carrier. For each event the `a.value halfProductDensity` term keeps its actual incoming prefix+chosen product, rejected factor, and suffix product, with no added target deletion multiplier.

This is a source-to-physical-WEIGHT occurrence bridge. It does **NOT** yet prove source-root to eighth weighted frontier reindexing, rank-nine payment, actual entire signed physical correction equality at the root, any signed saving, asymptotic integral, or coupling of the prior deletion inequality to a density bound. No `targetDeletionFactor` is charged in this packet. It also does not make an assumption equivalent to the desired saving.

## Checks and limitations

- GitHub source commits and branch HEAD inspected; source blob `3d1bac2ca4ce68fe1991373d2aaada47db1223a2` read back. Historical failed-attempt recursion, manuscript and exact Chen prime-density source read. No applicable AGENTS.md found at repository root or docs/source-only ancestor (404 / directory listing).
- Separate exact `Fraction` synthetic recursion: 4,000 seeded cases; 130,928 failed occurrences compared. Checked each mass equals initial mass times actual successful-selection product, key lists match the unit recursion, and no skipped/rejected prime enters incoming mass; zero mismatches. These are NOT the real87 archived states or Lean evaluation.
- Lean/Lake: **NOT RUN**. No local pinned Lean executable available. Neither imported source-only dependency graph nor this candidate has been staged or elaborated. Kernel replay, transitive axiom audit, saved87 archive replay, independent review and CI: **NOT RUN**. Static forbidden escape-token scan passed. **SOURCE_ONLY / UNEVALUATED / FORMAL CREDIT 0**.
- Only this proof packet was edited. No main/master, no forced update, no CI dispatch, no toolchain change, no Codex or external analytic project.

## Actual remaining work

First: prove full root-to-eighth **weighted frontier** transport (the current eighth state was generated with unit h), then combine the already-proven generic exact `correction_eq_failed_attempt_sum` at `halfProductDensity` with the same physical `g_N` event list, and only THEN insert the prior one-time deletion-factor estimate into the matching density comparison. Treat positive/negative sign separately: do not infer signed-saving monotonicity from nonnegative cap growth. Rank-nine inherited-square loss is separate. Same-source ordinary exit-series/residual integral, primitive/centre/modulus errors, sixth filtering, saved87 full archive, changed/tagged, two independent reserves and same-rho assembly all remain yellow.

External inputs remain REGISTERED / UNVERIFIED / NOT IMPLEMENTED / NOT INVOKED.
