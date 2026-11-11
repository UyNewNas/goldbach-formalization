# Durable handoff — actual licensed-sixth action ceiling

Resume from the live repository branch `chatgpt/p1-full87-licensed-sixth-ceiling-20261112` and inspect its HEAD and `REGISTRY.json` before creating another change. This packet derives from parent `63691b4e3a264a8e040163d31cae9385c7eb1c7d` (do not revert to older source-only pins). Candidate source blob `19b45358a35d5a64a40aae63192d3f6b0a7250f0`; path `docs/source-only/20261112-full87-licensed-sixth-ceiling/P4AOriginalFull87LicensedSixthCeiling.lean`.

NEW FACT (not PP): for every actual history, `licensedCap≤max(actual inherited cap5,VariableEnvelope.cap-width)`. Accepted strict updates satisfy the original selected-mask upper license, hence `licensedCap<153/256`; the actual third-active `level6Exponent` inherits the max bound. No assumed `q≤N^theta`, new structural input or policy variant was used. This is the missing global bound for **new sixth actions** only, not the already existing fifth seed or third-inactive raw-sixth action.

Reopen in this order:
1. `docs/source-only/20261104-full87-licensed-sixth/P4AOriginalSixthLicensedFilter.lean`
2. `docs/source-only/20261104-full87-licensed-sixth/P4AOriginalFull87LicensedSixthPolicy.lean`
3. `docs/source-only/20261103-full87-finite-parent/P4AOriginalFull87FiniteParentCaps.lean`
4. `ImbalancedChen/P1OriginalVariableFifthFullModulusBound.lean` (different old variable-fifth policy: DO NOT silently transplant its global ceiling)
5. `ImbalancedChen/P1OriginalHistoricalRetainedModulusLevel.lean` for first-exit validity; `docs/source-only/20261103-full87-finite-eighth/P4AOriginalFull87FiniteEighthCap.lean` for strict rank-eight caps.

NEXT substantive proof: establish an actual global fifth predecessor bound with literal original data/guards, then a rank-six/rank-eight retained-leaf modulus bound on both active and inactive histories, preserving source occurrence, full modulus Rosser beta, rounding once and fixed-before-N quantifiers. Do not infer modulus support from `prod(roughPrimeUniverse)` or from only the winning rank-eight owner. Then check sharp PP allowed smooth singleton X and endpoints; external PP stays REGISTERED_NOT_PROVED / NOT_CALLED.

This run: `lean --version`, `lake --version`, `elan --version` each exit 127; .lake fixed deps absent; 5000/5000 synthetic exact rational finiteMax checks; no original87 replay. SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no kernel replay, transitive axiom check or independent review, no CI. Manuscript pin `9731290e` blob `d529bea2`; Lean 4 v4.33.0-rc1; mathlib e4c91783; native 09b97db; c=49044063/25000000, K=8452171/1250000. No other task branch touched.
