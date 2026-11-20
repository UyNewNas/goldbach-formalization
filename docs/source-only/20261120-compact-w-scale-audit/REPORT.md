# P1.4 — actual compact presieve exponent versus five-factor obstruction

**P1.4 remains YELLOW. SOURCE_ONLY / UNEVALUATED / UNCOMPILED.**

## Recovery and actual sources read

- Baseline: `a1285c62408d60f6ad213036464b8a34a97d5994`, independent parent `chatgpt/p1-full87-changed-rough-level-obstruction-20261120-1510`; read its REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and full previous source, plus five-factor and causal-witness candidates.
- New source commit: `e2b3942f6408622b95bf9e3c687c90caaca4bf1c`, blob `1f11ea824a7f0070b72ac58222d2e205e84cf66a`, 152 lines, `P1Full87CompactWScaleAudit.lean`.
- Actual existing code read: `ImbalancedChen/ActualUpperCountingInputs.lean` (attachedUpperModuli/coefficient), `ImbalancedChen/P4ASameRhoCompact.lean` (attached_moduli_eq_firstExit), `ImbalancedChen/P4ACompactPhysicalIntegralLedger.lean` (precision supplier), `ImbalancedChen/P4ACompactPhysicalSupportLedger.lean`, `ImbalancedChen/RoughPrimeUniverse.lean`, `ImbalancedChen/ActualSmallRosser.lean`, `ImbalancedChen/FixedRoughCoefficients.lean`.
- Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Checked Sections on PP (around lines 256–314) and upper sieve (around lines 359–482).

## New mathematical correction of the earlier parameter diagnostic

The previous candidate proved the genuine conditional arithmetic bound `b >= w^5` for changed rough support, and raised a potential clash using `w=N^(19/96)` and physical level `N^(599/1000)`. That substitution was **not justified**.

The actual `attachedUpperModuli 1 thirdPrefixRho epsilon ...` has:
- small Rosser primes `p < w`, rough-prime carrier `w <= p < z`;
- `w = N^(epsilon^2)`, `z = N^thirdPrefixRho = N^(19/96)`, small Rosser level `L=N^epsilon`;
- real compact precision supplier `epsilon>0`, `epsilon<=2e`, `e<=1/384` (and epsilon<1/8).

The new candidate proves `5epsilon^2 <= 5/36864 < 19/96`; for every `N>=2`,
`(N^(epsilon^2))^5 < N^(19/96) < N^(599/1000)`.
Consequently the required **strict** premise `B < w^5` of the earlier low-carrier exclusion does *not* hold when the *real-level* `B=N^(599/1000)` and this compact w are used. This removes a **false apparent scale contradiction**, but it does not exhibit any changed rough modulus or prove a gain.

The last Lean candidate instantiates the previous true RAW/LICENSED arithmetic lemma at `w=N^(epsilon^2)`, `z=N^thirdPrefixRho`, yielding `N^(5epsilon^2) <= b` for any such changed b. This is expressly **conditional on choosing those parameters for the RAW/LICENSED policies**. It is not proof that the complete 87-domain policy actually shares this compact precision or the PP coefficient.

The compact family above comes from the project's third compact implementation. The frozen manuscript's full 87-domain eighth frontier and its physical density must still be matched to a fixed, actual compiler precision and coefficient. The physical `q=a*b` and rough `b` remain distinct; `N^theta_*` bounds active physical support only with the separate relevant support theorem.

## Verification

- Re-read source from GitHub by exact commit, blob matched `1f11ea824a7f0070b72ac58222d2e205e84cf66a`.
- Toolchain file `lean-toolchain` pins `leanprover/lean4:v4.33.0-rc1`; `lake-manifest.json` pins mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and goldbach `09b97db5764ade1246bfb77206baa1b124760958`.
- Execution in existing container: `lean --version` exit **127**; `lake --version` exit **127**; `elan --version` exit **127**; `git --version` exit **0** (2.47.3); cgroup `memory.max=4294967296`.
- Import closure for source-only candidates was not staged. **No elaboration, kernel replay, transitive axiom audit, independent review, CI, toolchain download, resource expansion or Codex**. No changes to master, existing proof packets or frozen c/K.
- Lean candidate theorem bodies remain **UNEVALUATED**. No numeric sanity test or static scan is Lean verification.

## Actual open mathematical obligations

1. Authenticate one fixed precision e/epsilon and same physical `rho_N` for full87 RAW/LICENSED final policy; do **not** infer this from the compact-third family.
2. Establish the true rough and full-q support ceilings and strict integer/real endpoint translations before applying any level exclusion.
3. Match changed-rough first disagreement at ranks 5/7/9/greater to original ordered owner occurrences and dynamic parents, covering changed/tagged/BOTH/inherited without losing signed multiplicity.
4. Identify the ordinary residual integral of the **same** actual source and pay primitive discrepancy, modulus-prime correction, signed outside net, producer invoice, ordered stops and independent compiler/density reserves against `H_N`.
5. Type-check source-only import closure on pinned Lean. Restore no external PNT/Mertens/BV/spectral proof.

**Next action:** audit `P4AOriginalFull87LicensedSixthPolicy.policy` producer installation into the *final* physical `actualSmallRoughRho` with its fixed e/epsilon and origin history, then map first odd disagreement by actual rank. Do not reuse the mistaken `w=N^rho_0` substitution.
