# P2 half-open endpoint integral handoff (2026-11-11, round 3)

SOURCE ONLY; UNCOMPILED. Parent: 34aa0f58e6805959ecd7d00cb6dc38fcc32ebde7.
Branch: chatgpt/p2-integral-rounding-20261111.
New source: ImbalancedChen/Certificates/P2PairedHalfOpenIntegral.lean (273 lines).
No Lean/lake/Elan, Codex service, user computer, numerical checker or CI run.
No workflows, dependency pins, public root, other routes or existing source files changed.

## Freshness, manuscript and ownership

- Branch head was re-read immediately before publication preparation and remained 34aa0f5; no later P2 source writer was observed. The sealed branch remains 3a46b3f0a4ee8ee7e628c9234717fae03064a52b.
- Read both earlier 20261111-p2-rounding handoffs, current manuscript map, adopted evidence catalog, sealed ROUND_PAUSE_CHECKPOINT.md and DISPATCH.json, and automation/contracts/ownership.json. Certificates/** and automation/parts/p2/** are P2-owned.
- P1.4 retains actual history/full87/saved87 ownership; P4 retains complete noncompact tails and All22 attachment. Its separate branch chatgpt/p4-uniform-correction-20261111 was observed at 6eed80494ec6432efa739c7cf1ce3e61882da3eb. No P1/P3/P4/P5 source is edited.
- Current manuscript pin: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b. The adopted certificate JSON metadata again returned blob 49499697cca96de5f7b779e95077874ce5f9d119, also confirmed at historical ba6ec11d800eccc54406490631895e174de85766 by independent read-only review.
- Read the current module paper/source/modules/corpus-renewal-paired-certificate-v2-20261010.txt (blob 4b21263141eaae9273e60dc4ca1fd5fdb90fd67f): 6091+11481=17572; 7/3 replaces 12/5; K/80 includes the Chen quarter once; no permutation multiplier.
- Reuse the existing complete Row over 186 strips, original firstU, indices, cutoff, selector and checked endpoints. No prefix experiment, data regeneration, finite-checker replay or replacement of certificate arrays.

## Duplicate-work check and minimal reuse

Catalog B explicitly left the literal prime-box half-open convention and boundary-null identification as an interface. P1 LogPrimeBoxIntegral uses Set.univ.pi of Set.Ico; LogPrimeBoxMesh retains the same [lo,hi) ownership.
The existing P2AdoptedUnionIntegral already proves all seven walls null and closedSupport_ae_eq_support. P2SemanticGainSetIntegral already proves genuine semantic integrability, Fubini and disjoint-union integration. P2PairedSelectedRows and P2PairedRoundingLedger already prove directed bounds and rounding accounting.
Those are reused, not reimplemented. Existing tUpper_le_tLower/uUpper_le_uLower separate the actual grid intervals at their meeting walls.
Read-only checks of these modules, sealed Certificates and old chen-p2-certificates found no corresponding half-open adapter. Default-branch searches were bounded and non-exhaustive. Unavailable local/unpublished material is unverified, not considered absent.
Pinned mathlib APIs were checked directly at e4c91783ca8e6a7c693ae624ade32fd22d4e43c1: MeasureTheory.ae_all_iff, IntegrableOn.congr_set_ae and setIntegral_congr_set. No external theorem was newly formalized.

## New deductions and exact premises

- halfOpenSupport uses tl <= t < tr and ul <= u < ur, and keeps a < w < z < Z unchanged.
- mem_halfOpenSupport_primeBox is an exact dictionary to P1's two-coordinate logPrimeBox in coordinate order (t,u).
- The existing closed nested support implies the original Buchstab residual >= 7/3 even at the two newly included lower endpoints.
- Actual mesh separation proves unique row ownership at every point, including the lower walls; this is stronger than a.e. uniqueness.
- support is contained in halfOpenSupport, which is contained in the already defined closedSupport. Existing seven-wall nullness therefore gives a.e. equality.
- For every finite adopted row selection s, the measurable halfOpenUnion s agrees a.e. with the original rowUnion s. Full univ means all 17572 rows; no row is sampled or counted twice.
- Genuine raw-kernel and actual semantic-kernel integrability is transported by a.e. set equality. Every half-open constant row integral equals its genuine gridIntegral; every half-open semantic row integral equals its actual omega fourfold rowGainIntegral.
- Selected constant and semantic integral bounds follow from the original checked suppliers. For the full mask, the genuine half-open integral is exactly the existing unionIntegral/fullSemanticGain, retaining the original K/80 and K/4 normalizations.
- L <= I_half <= U, and L <= S_half <= 10U. The narrow U and width W only enclose the constant 1/20 minorant, not actual omega.
- The exact existing rounding ledger also transports: R <= I_half-F <= R+W, where L=55858378943374979/10^20, U=55858409959907296/10^20, F=558583/10^9, W=31016532317/10^20, R=78943374979/10^20.

All new statements use original row geometry and original checked suppliers. There is no assumed target enclosure, integrability, a.e. identity, parent ownership or gain dominance.

## Validation and remaining obligations

Independent read-only mathematical and Lean-source review of the main candidate plus the four final supplier adapters found no mathematical direction error or definite Lean source error. Lexical proof-escape guard and source delimiter checks passed; these are static checks only.
Lean elaboration, kernel replay, complete declaration/type inventory and transitive axiom audit: NOT RUN. All imported candidates retain their actual previous acceptance level. No blue/green or whole-P2 closure claim.

The a.e. statement concerns real product volume. halfOpenRegion is not claimed to be a literal subset of the original open region. Arithmetic prime atoms at endpoints, actual historical retention/injection, saved-estimator identities and concrete deletion budgets remain with their genuine suppliers. This endpoint adapter does not discharge them.
Other adopted integral endpoints/raw witness bindings remain open. P4 complete tails remain open.

## Existing compilation-repair handoff and next entry

Target: ImbalancedChen.Certificates.P2PairedHalfOpenIntegral. Direct imports: P2PairedSelectedRows, LogPrimeBoxIntegral and Mathlib.Tactic.FinCases.
Its exact source ancestry includes 34aa0f5 -> cc7da5cf6e78dfac313f8b66d7a302c009a2448c -> 3a46b3f0a4ee8ee7e628c9234717fae03064a52b.
Use the exact candidate commit and full import closure; preserve the existing validation gates and object identity checks. Lean leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; goldbach 09b97db5764ade1246bfb77206baa1b124760958; LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271.
A following P2-owned validation-request file will bind the exact source commit SHA for the existing P0 compilation-repair queue. It requests validation only; no CI is dispatched by P2 and no acceptance is presumed.
Next substantive entry: consume an actual licensed historical selection when supplied by its owner, or bind another adopted certificate's precise source payload to its already available actual integral semantics. Do not recreate Fubini, walls, finite checker or P1 historical work.
