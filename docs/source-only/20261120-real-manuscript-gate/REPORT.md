# P1.4 — real manuscript half-product gate at the original full87 physical delta

Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Parent node **YELLOW**.

## Recovery and actual code
- Baseline checked and read: `f18d633ae6a2afe794ae61be3997663909064b06`, packet `docs/source-only/20261120-real-coprime-gate/`; original branch still at this verified head when resumed.
- This distinct branch: `chatgpt/p1-full87-real-manuscript-gate-20261120-2010`. New source commit `e475949efab606ba580802337a82ac73b5a403e3` (original source creation `eadb58966b7f367e53ff999c1d2999fb808615b5`, followed by removal of forbidden-token mentions in a source comment).
- Source: `docs/source-only/20261120-real-manuscript-gate/P1Full87RealManuscriptGate.lean`, Git blob `718461f9f06491f2270adfbe98dcc9feff44e74e` (189 newline-separated lines, including terminating empty line). Existing SOURCE_ONLY dependency imports require staging as `ImbalancedChen.P1Full87RealCoprimeGate` and its transitive source-only modules to elaborate; this has not been done.

## Actual new mathematics
1. **Exact real gate for ALL N≥1:** for `b>0` and `theta ≤ (1-kappa)*b/(1+b)`, the ORIGINAL `manuscriptHalfProductCutoff kappa N` is strictly positive and
   `N^theta ≤ (manuscriptHalfProductCutoff kappa N)^(b/(1+b))`.
   This uses its literal `2*N^(1-kappa)` source cutoff and the factor `2`. Unlike `eventually_manuscript_sieve_gate`, it does NOT round `N^theta` to `Nat.ceil`, and consequently does NOT require a STRICT exponent gap or an eventual-N argument.
2. **Quantitative frozen-rho0 margin:** if `b≥1/2` and `kappa≤1/4`, then
   `19/96 < 1/4 ≤ (1-kappa)*b/(1+b)`. The coefficient `19/96` is the frozen manuscript upper rough exponent `rho_0`. This is exact real rational arithmetic, without a change in `b,c,K`.
3. **Precision and physical parameter instance:** if `0≤epsilon≤1/8`, then `epsilon^2≤19/96`. For every N≥1, `w=N^(epsilon^2)`, `z=N^(19/96)`, `L=N^epsilon` satisfy `1≤w≤z`; the ORIGINAL `R=P4AOriginalFull87CompleteSixthDispatch.policy` and `S=P4AOriginalFull87LicensedSixthPolicy.policy` with their actual `Q` and `trueDDeltaRho` thus have *zero exact real coprime correction* for `T=manuscriptHalfProductCutoff kappa N`, under the displayed b/kappa/epsilon range. No separate hypothesis `z≤T^beta` remains in this concrete theorem.
4. The same original RAW/LICENSED real receiver sum is exactly original source cardinality times the same `high=Q.filter (w^5≤d)` reciprocal-totient density plus **one** same-rho high-d signed primitive distribution error, with the existing finite absolute invoice. Nothing else is paid or cancelled.

**Non-completion boundary:** This is the named full87 original pair with an *explicit parameter specialization*. It does NOT prove that the frozen final full87 constructor has actually selected this epsilon, cap, w, z, L or the same global physical rho. In particular the code-level identification of `thirdPrefixRho` and the final full87 precision/owner source remains to be certified. Nor is `rho_DELTA` a positive sieve majorant or an authenticated `eq:current-PP` coefficient. This run supplies neither `o(H_N)` primitive discrepancy, saved87 numerical gain nor independent reserves.

## Dependencies / source boundary
- Read: `P1Full87RealCoprimeGate.lean`, `P1Full87RealPrimitiveTail.lean`, `ImbalancedChen/ActualUpperCountingInputs.lean`, `ImbalancedChen/RealPhysicalUpperWeightBridge.lean`, `ImbalancedChen/P4ASameRhoCompact.lean`, and frozen `manuscript-body.tex`.
- Only existing mathlib / project numerical and rpow facts; no PNT, Mertens, BV, spectral or PP analytic theorem was implemented or assumed in the new proof.
- Original manuscript pin: `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No silent manuscript revision.
- Lean `leanprover/lean4:v4.33.0-rc1`; `lake-manifest.json` at this branch confirmed mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958` unchanged. `c=49044063/25000000`, `K=8452171/1250000` unchanged.

## Checks actually performed
- Source and existing reports/registry/input boundary and frozen manuscript read from the GitHub connector; baseline branch compared identical to `f18d633`.
- `lean --version`: **127** (not installed); `lake --version`: **127**; `elan --version`: **127**. `git --version`: 0 (git 2.47.3). Cgroup `memory.max=4294967296` bytes.
- No fixed-version Lean elaboration, dependency closure, kernel replay, transitive axiom audit, or independent proof review. A static banned-token scan is clean but does not prove Lean acceptance. SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
- No additional CI dispatch, Codex, toolchain upgrade, resource change, main/master edit, merge, or force push.

## Next exact target
Verify that the original full87 final coefficient and physical-support constructors actually instantiate `w=N^(epsilon^2)`, `z=N^(19/96)`, `L=N^epsilon` with the frozen precision and cap, and connect the actual code `thirdPrefixRho` to 19/96 where required. Then check the specific one-off `high-d` primitive discrepancy at `T=manuscriptHalfProductCutoff kappa N` for `H_N` payment and authentic causal PP class. Independently map rank5/7/9 actual first divergences to the 87 owner/changed/tagged/BOTH/inherited occurrences and certify the two distinct reserves. Do not promote parent P1.4.
