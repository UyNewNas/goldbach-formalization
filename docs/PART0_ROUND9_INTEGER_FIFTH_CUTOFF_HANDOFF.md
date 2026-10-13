# P0 Round 9 — fifth integer-cutoff reception

Receiver parent: `59d338b93b2347021237eb51293bb934a316909d`.
P1 source: `b416a21d70255a94dfc44c03aade3bd118de2f6e`; exact proof blob: `3e7fe2e871217c16124f3b97ffb743a400bc24cf`.
Direct-import blob `HistoricalFifthCutoffInvariance`: `c10501d72a8f30dc8712e146fb5f2538960f9c09` in both trees.

P1 core CI: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38345607447 — success (full build, stock checker, seven defining-module types and allowed axioms); specialized CI 38345607444 — success. Evidence: `verification/parts/p1/round7/VERIFICATION.json` and `DECLARATION_TYPES.json` at `6c37e6e4d882c07716d9f89ddf4b6799cd90aaca`.

P0 parent core CI 38349841383 and variable-envelope CI 38349841389 both succeeded. This new receiving commit needs its own full root verification. P0-specific Round6/Prefix128/P4/new P1 compiler-type exports remain pending.

The strict integer cutoff `floor(N^b)+1` ensures fifth historical prime enumeration safety and gives conditional finite and limit identities. Actual adopted history, hLower, hUpper, and the final unconditional theorem remain unproved. Fixed manuscript, common proof baseline, Lean/mathlib/goldbach dependencies, and theorem/normalization constants are unchanged.
