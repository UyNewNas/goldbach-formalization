# Part 0 Round 8 — five verified physical upper-sieve interfaces received

## Exact provenance and received code

- Receiving branch: `chatgpt/chen-p0-integration`; parent proof-root SHA: `456eae4e174c8f409cfa2b3d0738b478e2e842ff`.
- Fixed P4 producer HEAD: `e5d044a087b15cd0936ed6f062ac8bc62e8e5f75` on `chatgpt/chen-p4-upper`.
- Full producer-specific CI: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38328994604; job `115074172304`; **SUCCESS** on exactly `e5d044a087b15cd0936ed6f062ac8bc62e8e5f75`; original artifact `part4-upper-38328994604-1` ID `11783508650`.
- Producer root CI: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38328994583 **SUCCESS**. Variable-envelope CI: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38328994576 **SUCCESS**.
- Source modules reused byte-for-byte, with producer Git blob IDs:

| Exact module | Original Git blob |
| --- | --- |
| `ImbalancedChen.ActualUpperPolicyDensity` | `487f13707ee13159cd7f161879b5a2e44ffb8c19` |
| `ImbalancedChen.UpperCoefficientPerturbation` | `7b024033e58e19c0dcf94de322d6cb7d6815d987` |
| `ImbalancedChen.ActualUpperDensityAssembly` | `e363dee459e99b2be6f83f2c70b15f8968fd4817` |
| `ImbalancedChen.RealPhysicalUpperWeightBridge` | `c774859dab0bdcfc1266200d7437a62d0c69e5ea` |
| `ImbalancedChen.RealUpperCountingAssembly` | `6e6843444cafa0e1d51a903981da0092983d2ac0` |

The receiving root `ImbalancedChen.lean` adds explicit imports for these five source modules, with no changes to their proof terms or to the fixed manuscript/proof pins. Each original import depends only on existing baseline/P0 modules or another module in this batch. The producer proves 5 strict source compilations with warning-as-error, 5 original bundled checker individual replays, one actual fresh aggregate replay of the five modules plus their imports, and a complete defining-module inventory of 73 declarations (13/7/11/38/4 in producer target order) with full compiler types and transitive axioms limited to `propext`, `Classical.choice`, `Quot.sound`. The exact original commands, source/object/tool bindings, exit statuses and logs belong to the producer artifact; this handoff does **not** assert they were rerun in P0.

## Mathematical interfaces (not final upper bound)

These modules preserve the exact physical coefficient throughout majorant, reciprocal-totient density, coprime correction and signed distribution error. Their useful outputs include a Boolean policy identification, an absolute rough-coefficient compiler perturbation bound, the exact source/density normalization identity, the real-imbalance physical weight bridge, and a conditional `RealB` upper count. The last remains conditional on four **same-rho** inputs: pointwise majorant, actual normalized density cap, coprime correction payment, and signed distribution error payment. It must not be misrepresented as a proof of the actual `hUpper`, full K bound, or an unconditional error estimate.

The numeric pins remain `currentK = 8452171/1250000`, `currentC = 49044063/25000000`; the manuscript commit remains `ba6ec11d800eccc54406490631895e174de85766`, and proof baseline `1a80c1bcce67886f699d097fc37fd245cd3620bf`; Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, goldbach `09b97db5764ade1246bfb77206baa1b124760958`.

## Exact-root verification and outstanding obligations

The parent root `456eae4e174c8f409cfa2b3d0738b478e2e842ff` passed core CI run https://github.com/UyNewNas/goldbach-formalization/actions/runs/38344536329 (job `115122744230`) and variable-envelope run https://github.com/UyNewNas/goldbach-formalization/actions/runs/38344536349. Core raw job logs confirm build (219 s), original root leanchecker (503 s), full transitive axiom audit (30 s), Round3 types (248 s), Round4 types (252 s), and explicit Round4 targets (2 s), **all exit 0**. These parent-root checks must **not** be transferred to this new integration SHA.

For the new root, full build, original bundled root replay, full root axioms, existing Round3/Round4 types and variable-envelope verification are all **pending until exact-commit CI reports success**. The Round6 four fifth-history modules (70 owned declarations) and newly received P2 Prefix128 modules (481 owned declarations) still lack their own P0 full type-export receipts; producer type inventory cannot replace a P0 inventory. The verified `verification/parts/p0/check_round6_types.py` source exists but is not wired into the required core workflow; this round's attempted workflow update was blocked by platform safety checks and has not been treated as success. New P4 owned declarations likewise still need P0-root-specific compiler type export. Preserve existing proof gates and do not claim the Round6/Prefix128/P4 type-specific gates were executed.

The conditions `hLower`, `hUpper`, real adopted compiler/coverage, all adopted certificate rows, full arithmetic error payments, and exact density-coupling remain open. This integration accepts five *conditionally useful supplier modules*, not a completed 1+1.75 proof.
