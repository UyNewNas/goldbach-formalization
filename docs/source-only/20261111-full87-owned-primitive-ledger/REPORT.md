# P1.4 — physical full-modulus primitive discrepancy on the actual 87 owned sources

## Recovery and provenance
- Immediate verified parent: `730ebc4c9e7557dccb3f2f02f97e7d3c4fa9448b` on `chatgpt/p1-full87-signed-parent-invoice-20261111`; read its complete candidate, REPORT, REGISTRY, INPUT_BOUNDARY and persistent HANDOFF.
- This run's branch: `chatgpt/p1-full87-owned-primitive-ledger-20261111`. Original proof, source arrays, fixed policy, root/master, dependencies, reserves and external theorems are not edited.
- Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; specifically §4 full-prime-product PP statement and upper source. Pinned Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`. c=49044063/25000000; K=8452171/1250000.
- Inspected `P1Pair12RetainedSignedSource.lean`, `P1SignedDescendantAccounting.lean`, `P4AOriginalFull87OwnedEighthSource.lean`, `P4AOriginalFull87EighthPrimeMeanLedger.lean`, `P4AOriginalFull87ActualParentResidualGap.lean`, `ChenInitialPrimeSource.lean` and previous handoff. Ancestor AGENTS instructions were searched; no applicable AGENTS.md found.

## New manuscript-internal result — exact full-q PP adapter and localized invoice
The earlier receiver decomposition uses the *physical* difference
`gain(G) = physical(sixth,G) - physical(eighth,G)`, with unchanged original policy and rho, and has a primitive discrepancy term `gain(primitiveError N)`.
Previously the only generic bound for that term was `absoluteGainBudget`, the old-plus-new absolute physical support, which includes unchanged branches.

This candidate instead expands the *same* primitive term on original rank-eight owner/trim occurrence lists. For state `s` in `states(width r,...,c)`:
- `beforeLeaves(s)`: first-exit leaves under the original ordinary policy frozen at `N ^ actualParent(n,e,q,om,N,s.selectedPrefix)`.
- `afterLeaves(c,s)`: first-exit leaves under the original ordinary policy at `N ^ finiteCap(n,c,point8(N,s.selectedPrefix))`.
- For each literal leaf ℓ, with sign and multiplicative coefficient `ℓ.value`, the exact primitive contribution is `ℓ.value * sum_(a in actualSmallRosserSupport) β_(ℓ.sign)(a) * primitiveError N (a * ℓ.selected.prod)`. That is the **full modulus**, not just its rough product. There is no sign-neutral beta.
- `primitiveStateSaving` is old leaves minus new leaves. The proof `ordinarySaving_primitive_eq_leaf_invoice` reuses the existing `signedTest_eq_leaves` identity; neither side restarts the prime tree or changes its parent.
- `abs_primitiveLeaf_le` and LIST induction bound the original signed local change by the sum of absolute beta-weighted discrepancy terms on exactly those two leaf lists, without collapsing duplicate occurrences.
- `owned_primitive_exact` and `owned_primitive_abs_budget` use the exact original `states` lists. The final `full87_primitive_owned_budget` is

```
|gain(width r,..., primitiveError N)|
  <= sum_(c : original Cell) sum_(s in ORIGINAL states(c))
       [sum_(leaf in actual BEFORE leaves(s)) |leaf.value| sum_a |beta_sign(a)| |primitiveError N(a*leaf.prod)|
        + sum_(leaf in actual AFTER leaves(c,s)) |leaf.value| sum_a |beta_sign(a)| |primitiveError N(a*leaf.prod)|].
```

This removes the **unnecessary unchanged branches from the primitive AP discrepancy bill** at the finite-algebra level. The bound is not proved small relative to H_N and is NOT a numerical reserve payment. It does not assume a PP input or equate ordinary density with the residual integral.

## Verification evidence and limits
- New source `P4AOriginalFull87OwnedPrimitiveLedger.lean`, Git blob `2cc1d0dcb50c062e7415b07fffdd091f21ff23cf`; seven proof declarations including a private list triangle helper. All proofs are CANDIDATES, not elaborated.
- Direct remote source re-read checked the Git blob; static scan of uncommented source found no axiom, sorry, admit, native_decide or unsafe.
- An independent Python `Fraction` finite analogue constructed actual prime-prefix congruence counts and exact coprime means for N=23,31,47,59,97, and synthetic signed beta/rough-leaf occurrences (including duplicate/empty cases): 52,200 Cell comparisons + 600 87-Cell aggregate comparisons, zero failures. This checks the finite algebra only; it does not enumerate original states, verify the saved87 numerical witness, typecheck Lean or establish PP.
- The local runtime has no `lean`, `lake`, `elan` (`--version` all exit 127). No fixed project dependency tree is checked out. Consequently **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**, no kernel replay, transitive axiom audit or independent proof review.
- No CI, Codex, extra cloud resources, user-local access, force push, merge, or fixed pin change.

## Remaining exact yellow obligations
1. Apply the frozen manuscript's §4 PP only after proving the original `W_N`, full-q modulus support, permitted signed rho, prime-label/geometric smoothness, legal integer X and fixed-parameter quantifiers match the actual leaf family. Obtain a genuine uniform quantitative bound on the **new localized** primitive invoice on the one H_N scale; the present code DOES NOT prove or assume this bound.
2. Derive the actual ordinary-continuation density-to-residual integral asymptotic with the same parent/history and beta, and quantify the previous signed parent-gap invoice under H_N. Do not identify it with the physical gain by assumption.
3. Modulus-prime and centre-prime, low/high q, raw/finite/filtered, rank9 and changed/tagged payments, separately booked compiler and density reserves.
4. Restore authentic frozen saved87 integral witness/interval files and independently replay the original numerical gain; prior selected rational records alone are insufficient.
5. Stage exact imported source modules and run the fixed Lean kernel. Kernel replay, axiom audit and independent review stay separate.

P1.4 remains **YELLOW**; external §4 PP is **REGISTERED_NOT_PROVED / NOT_CALLED**.

## Follow-up actual receiver-density insertion (second source file)
A new standalone Lean candidate `P4AOriginalFull87ReceiverLocalizedBudget.lean`, Git blob `43641f89b241bb9a3686e27cb753bca3629be588`, reuses the **already established exact finite receiver decomposition**, not a separate sieve bound:
`gain(receiverTest N) = primeMass N * gain(densityTest) + gain(primitiveError N) - gain(modulusPrimeTerm N) - gain(chenCentrePrimeAPCount N N)`.
It substitutes the genuine `full87_primitive_owned_budget` only for the absolute primitive-discrepancy component, leaving modulus-prime and centre-prime corrections as **two distinct** existing `absoluteGainBudget` terms. `full87_receiver_density_with_owned_primitive` proves this physical receiver-density-error bound without a new external assumption or a double payment.

**Numerical ordering caveat:** This localization removes *unchanged branch support* from the primitive bill but does NOT prove its numerical RHS is always <= the previous global `absoluteGainBudget(primitiveError)`. Absolute values before/after cancellations may alter that comparison. It is a better specified actual PP call-site, not yet a proven smaller scalar or a reserve debit. Like the first file, the second is uncompiled; source and all proof terms remain UNEVALUATED.
