# P5.6 → h34 — exact actual bank/Buchstab union and single-threshold row budget

Date: 2026-11-09 UTC. Repository: `UyNewNas/goldbach-formalization`.
Dedicated branch: `chatgpt/p5-h34-actual-selected-row-budget-20261109`.
Verified incoming h34 HEAD: `6730af27ce352c40cd49e8fc6508ab2b6145f9f0`.
Mathematics commits: `4085c6321e35294ee1f0d244d16b51ed47e84351`, namespace correction `5c8d3cd3904e4bf4307e34a71296fb190522cc86`.
Lean source: `Part5OriginalH430ActualSelectedRowBudget.lean`, final Git blob `558e7bfa136310cee02fa4199449294e7ce2c0ae`.
Source has 7 definitions and 5 candidate theorem declarations.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Starting point and genuinely new source

The original 20261105 request-admission REPORT, REGISTRY, EXTERNAL_INPUTS and the newest 20261109 actual-request-nonbank quantitative handoff were inspected, together with the predecessor Lean source. The starting point is the verified 20261109 HEAD `6730af2`, NOT the historical `0a3fa5a`.

Previously, the real g+1 resolver's Fin positions had been partitioned into retained, Buchstab and original 106 bank winners. Another packet matched the nonbank winning positions to the older local estimates. However, the newest packet used a uniform pre-N threshold ONLY for the Buchstab estimate and full request-value bound; its result did not yet combine the original 106 bank absolute and applied errors with the Buchstab error, nor did it provide one actual disjoint winner-row coefficient mass formula.

This packet adds genuine, local proof candidates:

1. `actualBankTheta/Error/AppliedError/Row` are computed from the original selected 106 bank rows, not arbitrary per-action substitutes.
2. `actualSelectedTheta/Error/Row` combine only selected bank and Buchstab row/error terms; retention stays an exact old-cell read.
3. `actual_bank_theta_eq_positions` and `actual_bank_row_eq_positions` reindex the original 106 action sums onto actual bank-winning Fin positions. They do not add unchosen alternative rows or identify repeated integer products.
4. `actual_selected_theta_eq_positions` and `actual_selected_row_eq_positions` prove the literal disjoint Buchstab-or-bank union equality, using the genuine request resolver. The exact physical root-specific Q, stage and original path mark are preserved.
5. `uniform_actual_selected_error_row_budget` chooses **one T before N, n, root, tau, p, g and the 106 actions**, from the fixed-version bank and actual-nonbank suppliers. It proves bank absolute error and bank applied error each bounded by epsilon*actualBankTheta, Buchstab absolute error bounded by epsilon*actualBuchstabTheta, combined absolute error bounded by epsilon*(actualBankTheta+actualBuchstabTheta), and nonnegative combined row entries with
   `sum_b actualSelectedRow(b) <= 12*actualBankTheta + 5*actualBuchstabTheta`.
   This is a segregated 12/5 accounting, **not** a new global norm 17 replacing the manuscript's immutable 12 bank norm. The applied-error inequality is an alternative bound for the same bank source, not a second charge added to its absolute error.

The proof uses the original literal scalar/specified-cell choice, same root physical Q, Fin-list occurrence multiplicities and true alpha through its pinned predecessors. It does not change c=49044063/25000000, K=8452171/1250000, root norm 7/2, bank row norm 12, separate Buchstab 5*Theta, or the 430+11 nested budget.

## Explicit manuscript-internal gaps

- An upper bound on the **feedback row** is not yet the genuine original arithmetic U3/U4 CLOSED-CELL count induction. The original predecessor base/seed, actual full/selected/inherited count owner, fixed/switched bank value, integer floor sign, true original q/tag-root weights and threshold mismatches remain to be proved.
- Six original rejection lanes, collisions and signed Euler first-excluded payments are not paid by the selected-row coefficient mass. Their H430 allowable error bound remains open.
- Feedback-to-integral, PP/same-rho instantiation, native-history proper/equality/inherited mass, outer integral–Theta–count and ONE common 430+11 nested causal refinement remain open.
- The original selected source may have zero occupied paths or large unpaid q mass, as established in preceding genuine-history packets. This result does not assume q equals historical product d, or that positive request row mass implies complete q coverage.

## Immutable provenance and verification boundary

Manuscript mapping remains `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, as required by `docs/CURRENT_MANUSCRIPT_MAP.md`.
Toolchain stays Lean `v4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Authenticated GitHub permissions and prior branch-head ancestry were checked. Writes are **only** to this new independent h34 source-only directory; no edits to other h34 packets, production modules, P1.4, P3.6, main, CI workflows, toolchain, or manuscript. The mathematics source was read back with the exact final blob; the branch is a normal forward descendant of the incoming HEAD. No force-push or merge.

This runtime has Git but no Lean, Lake or Elan binary. Native `git ls-remote` fails on github.com DNS resolution. The held source-only predecessor import closure is not staged under the production `ImbalancedChen/` paths. Thus there was **NO Lean elaboration or compile**, no kernel replay, no transitive axiom audit and no finite numerical430 replay. Static source/diff/placeholder checks are NOT a Lean validation. No green proof status; inherited finite checks stay UNEVALUATED. No CI was dispatched.

**Next specific action:** in a separate pinned local/source-only build closure, compile this module with its actual bank/nonbank dependencies and repair real errors. Mathematically, use this precise selected-row budget in the original U3/U4 CLOSED-CELL successor estimate with a correct predecessor base/seed and original count-owner identification; retain the full unpaid q/tag and signed Euler differences until genuinely bounded.

**完整h34稿内证明仍未闭合。**
