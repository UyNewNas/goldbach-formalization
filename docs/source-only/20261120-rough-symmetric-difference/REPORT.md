# P1.4 — actual true-d density charged only to changed rough carriers

Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Parent node P1.4 remains **YELLOW**.

## Verified recovery and exact provenance

- Verified predecessor HEAD `79c515ee26f363f4dc969d8df408f791e33e143c`, on `chatgpt/p1-full87-true-d-unit-bound-20261120-1110`; fully read predecessor source, REPORT, REGISTRY, INPUT_BOUNDARY and HANDOFF; also read the genuine `FixedRoughCoefficients`, `SmallRoughAttachment`, `ActualSmallRoughAttachment`, `SignSensitiveAttachment` and three-book net source.
- This branch was created **only** from that verified SHA: `chatgpt/p1-full87-symmetric-rough-density-20261120-1210`.
- Candidate source: `docs/source-only/20261120-rough-symmetric-difference/P1Full87TrueDRoughSymmDiffDensity.lean`; Git blob `bb6ab1209a8c09312e13dfdfad42ef97be49c42c`, **171 lines**; source-only commit `139c947e470bff84540cba276dc6cc2f515b021f`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Its `eq:current-PP` is for the same permitted causal physical rho in AP and coprime mean; a unit magnitude test does NOT confer such a licence.
- Unchanged Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000.

## Actual new finite mathematical candidate

Let S_old and S_new be the **original** fixed rough supports for the two causal policies, with the same actual small Rosser support, beta-plus/beta-minus, and physical small/rough decomposition. Let

  h_N(b) = mu(b)/phi(b) * [D_plus if mu(b)>=0, otherwise D_minus],

where D_plus/minus are the **actual** small-prime reciprocal-totient Rosser densities, not a newly chosen comparison sieve.

With the true physical coefficient difference delta-rho = rho_new - rho_old (not full-Q), the exact finite candidate is

  physicalDensitySum(D_delta, delta-rho)
     = sum_{b in S_new \ S_old} h_N(b)
       - sum_{b in S_old \ S_new} h_N(b).

This is obtained via the existing **trueDDeltaRho_test** for the SAME reciprocal-totient test, the two **actualSmallRoughRho_density_eq** lemmas, then one cancellation of the INTERSECTION of their original rough supports. It is not a subtraction of two unrelated upper/lower screening *inequalities*. The net is still SIGNED; no monotonicity of savings is asserted. No inherited-branch mask is added. The second public theorem substitutes the actual RAW `P4AOriginalFull87CompleteSixthDispatch.policy` and LICENSED `P4AOriginalFull87LicensedSixthPolicy.policy`, not a free fresh policy.

This removes the need to **charge the shared rough-carrier density contribution twice** in the candidate finite density ledger. It does **not** prove the residual changed-carrier sum is small compared with H_N, or that it equals the archived 87-cell signed saving.

## Actual verification and tool limits

- Remote source read-back confirmed SHA `bb6ab1209a8c09312e13dfdfad42ef97be49c42c`, 171 lines and no forbidden proof escapes. `REPORT`, `REGISTRY`, `INPUT_BOUNDARY`, `HANDOFF` are this packet's durable records.
- Current container ran `lean --version`, `lake --version`, `elan --version`, all **exit 127** (not installed). `/sys/fs/cgroup/memory.max = 4294967296`. No fixed-version dependency closure is cached. No Lean elaboration or matched-version compilation has taken place; no kernel replay, transitive-axiom audit or independent review.
- Mathlib lemma/definition typing in this candidate is untested. The finite proof body is **UNEVALUATED**, not certified.
- No CI/Actions, Codex, main/master write, toolchain update, extra cloud resource, merge or force push.

## Exact remaining obligations / next action

1. Under the fixed toolchain, stage `P1Full87TrueDUnitBound` and its source-only import closure in temporary `ImbalancedChen/` paths, run `lake env lean` on this source, and repair from actual diagnostics; do not label COMPILED before exit 0.
2. Relate the *actual* S_new \ S_old and S_old \ S_new rough moduli to the complete 87 owner states and the literal changed/tagged/BOTH/rank9/inherited actions **without quotienting the occurrence list**.
3. Match that signed changed-carrier density to the saved geometric ordinary-continuation integral and bound compiler/density reserve separately, with one H_N payment per genuine loss.
4. The LICENSED physical upper coefficient itself needs full causal PP class, common smooth W_N, and same-rho AP/coprime-mean admissibility. The raw ideal policy and delta difference are not automatically separately licensed PP coefficients; their density comparison does not require such a distribution claim.
5. Verify signed outside net, producer invoice, ordered stops, lower-half three corrections and saved87 original numeric archive, then kernel/axiom/independent validation.
