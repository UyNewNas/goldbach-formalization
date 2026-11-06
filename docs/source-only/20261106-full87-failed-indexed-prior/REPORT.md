# P1.4: actual failed-attempt ALL indexed prior odd squares and pair logs

State: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL ACCEPTANCE**; parent P1.4 remains YELLOW.

## Pins and provenance
- Base: `3b743a3aaecc8e27179c5ab48544c56e8a5e35cf`, independent branch `chatgpt/p1-full87-failed-indexed-prior-20261106`.
- New proof commits: `de5acd8176cf1a37bd58186a0c5e33e6e3bcde07` (finite all-split bounds); `fa983dc5027ad03aacfcb47e0ef6873c159f8ab9` (strict logarithmic adapter).
- Proof: `docs/source-only/20261106-full87-failed-indexed-prior/P4AOriginalFull87FailedPriorSquares.lean`, final Git blob `3ead7e51b8fcecfb21ac6748d9aa3c90f1a76720`.
- Manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, §4, upper exit identity and residual-density passage.
- Lean pin `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. No updates. c = 49044063/25000000; K = 8452171/1250000.

## Real manuscript-internal progress
1. `validSelection_even_past_odd_guard`: for every split `chosen = past ++ r :: rest` with even-sized `past`, the *existing actual* `FirstExitValidSelection` certifies the odd decision `ordinaryParityRosserPolicy false R false (r :: past.reverse ++ history)`. This is not restricted to the immediately preceding odd ancestor.
2. `passed_odd_smallest_full_square`: from the literal full `UpperAdmissibleSet`, sorted odd prefix and the strict test, derive the **strict** inequality `(r::older).prod * r^2 < R`, not merely the total-product cutoff.
3. `owned87_failed_all_prior_odd_squares_and_pairs`: instantiate on every actual owned original87 failed attempt with the true `chosen <+ before`, `before ++ rejected :: smaller`, same eighth selected history, and one frozen actualParent/rounded finiteCap. Every prior even-sized split has its original strict square. Every pair of consecutive selected occurrences has decreasing prime and increasing log order; no setification or multiplicity change.
4. `passed_square_to_history_past_log`: strict N-log conversion of the same physical full square; exact `history.prod * past.prod * r^3` gives `S8 + log(past.prod)/log N + 3 log r/log N < beta`.
5. `owned87_failed_all_prior_log_guards_and_pairs`: true original Fin 8 sum and this exact inequality for every previous odd split, alongside all adjacent chosen log inequalities. The old hEXIT source from `P4AOriginalFull87FailedLogExit` is unchanged and does not get paid a second time.

The first after-eight rank-nine failure is NOT made into a new-last-square exit. Earlier historical levels are not transferred to the frozen eighth level. The candidate still requires an index equivalence between `past.length = 2*k`, `tailEvenMass` and `chosen.getD`; hence the final `post8_first_odd_exit_log_lower` application is NOT asserted here. The original structural event enumeration uses `h(p)=1`: these lemmas are geometry/source adapters only and do not yet prove the physical `g_N` weighted correction or its density.

## Checks performed this round
- GitHub baseline, parent and new branch ref checked before writes; proof blob read back after the first commit.
- Exact-integer synthetic recurrence check: 10,000 history scenarios; 34,624 strict previously successful odd-square instances and 54,964 adjacent-order instances passed. These are NOT original saved87 arithmetic archive and NOT formal proof.
- Static banned escape-token scan: none in source; source hash/commit to be reread. No Lean/Lake executable in the working runtime. Source-only imports require project staging to match Lean module names; not attempted.
- Lean compilation NOT RUN; kernel replay NOT RUN; transitive axioms NOT CHECKED; independent review NOT RUN; original saved87 NOT REPLAYED; CI NOT DISPATCHED. All source candidates remain UNEVALUATED.

## Remaining manuscript-internal obligations
- Prove the concrete indexed bridge from every even-sized `past` split to `∀ k < m` with `tailEvenMass t k`, `hpair` and `t (2*m)=log(rejected)/log N`; apply the existing post-eight potential to the *same* hEXIT and same beta. No duplicate payment.
- Rank-nine inherited historical square failure: quantitative bound or honest error budget.
- Ordinary same-source exit-series to residual integral and positive termwise bounds, including physical `g_N`, target-prime deletion, primitive/modulus/centre discrepancy and limit exchange; all external classical inputs stay documented unverified.
- Sixth-stage filtered signed loss, raw/finite/filtered coefficient gain, saved87 full numerical archive and changed/tagged coverage, independent compiler/density reserves and same-rho final assembly.

Next action: inspect `P4AOriginalFull87Post8SuffixExit.tailEvenMass` and `P4AOriginalFull87FailedLogExit.owned87_later_failure_exact_rank_log_exit`, write the exact indexed prefix/last-prime-list adapter from the actual returned `chosen` (not an invented coordinate family).
