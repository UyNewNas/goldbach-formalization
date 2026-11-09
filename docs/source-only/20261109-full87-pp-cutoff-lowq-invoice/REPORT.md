# P1.4 — real RAW/LICENSED complete-q PP discrepancy: strict cutoff and low-q invoice

## Recovery and fixed objects
Read current predecessor branch `chatgpt/p1-full87-paired-coprime-pp-20261109` at matching HEAD `dcd7100c40b9d72aa47508dd142c74daf244abde`; read its complete 213-line candidate and full REPORT / REGISTRY / INPUT_BOUNDARY / HANDOFF. Rechecked its last source commit `2d9533ffd366d3bba2660e9e958d717261ba6553`, and original `ImbalancedChen/ActualSmallRoughAttachment.lean`, `ActualSmallRosser.lean`, `FixedRoughCoefficients.lean`, `ActualUpperPolicyFiniteBridge.lean`, original signed helper and physical high-q aggregate. Checked existing strict cutoff candidate; no prior high/low **primitive PP residual** split for actual paired rho was used as a duplicate. No AGENTS.md at root; prior pinned tree inspection reported no applicable AGENTS.md.

Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, exact §4 lines 253–276, 305–355, 397–485 read. Eq. `eq:current-PP` centres the very SAME signed full-q coefficient at the true q-dependent coprime prime-product mean. It does not, on its face, grant the same estimate separately to a q-filtered coefficient lacking a renewed admissibility proof.

New task branch `chatgpt/p1-full87-pp-cutoff-lowq-invoice-20261109` was created from `dcd7100c40b9d72aa47508dd142c74daf244abde`, never from the older navigation SHA `9649ab3`. Source commit `9d40ec83010d2343bce8eed20638bc99043f1d2e`, file `docs/source-only/20261109-full87-pp-cutoff-lowq-invoice/P4AOriginalFull87PPCutoffLowQInvoice.lean`, **Git tree blob** `0c1c419dafe526c0e08cb892799b0d51192403d6`, 212 LF lines, one true low-support definition and four candidate theorem bodies. All existing source and handoffs preserved, source-only [skip ci] only. No main/master mutation or new CI run.

## Real mathematical increment
Let R be the original RAW sixth dispatch and S the original LICENSED sixth policy, and M the union of their ORIGINAL complete small/rough modulus supports. Put Δρ(d) = supportedPhysicalRho(R,d) − supportedPhysicalRho(S,d) and E_W(d) = finitePrimitiveDiscrepancy(chenPrimePrefix(N+D),W,N,d). For an integer X, define H_X = {d∈M : X<d}, L_X = {d∈M : d≤X}. They are an **exact exhaustive partition**; the equality case d=X remains in the low complement.

1. The original support theorem, specialized to R/S, supplies **d>0, squarefree(d), gcd(d,N)=1 for every d∈M**, via existing actualSmallRoughModuli_squarefree and actualSmallRoughModuli_coprime_target. This prevents using the analytically meaningless totalized q=0 convention at a genuine supported q.
2. The same signed full rho has exact finite discrepancy split:
   
   Σ_(d∈M) Δρ(d)E_W(d) = Σ_(d∈H_X) Δρ(d)E_W(d) + Σ_(d∈L_X) Δρ(d)E_W(d).

   The filter is applied to the finished SAME complete modulus; no separate Rosser factor, new parent, deduplication or unrelated mask enters.
3. Plugged into the previous exact paired true-coprime sharp identity, this gives:
   
   ΔSharp − Σ_(M) Δρ(d) X_W^(d)/φ(d) = Σ_(H_X) Δρ E_W + Σ_(L_X) Δρ E_W + ΔLower − ΔUpper − ΔCentre.
   
   Every existing endpoint/centre correction stays ONCE; the q-dependent modulus-prime correction is already inside X_W^(d) and is NOT charged again.
4. A high-q invoice follows **without assuming the filtered rho itself is externally licensed**:
   
   |Σ_(H_X) Δρ E_W| ≤ |Σ_(M) Δρ E_W| + Σ_(L_X) |Δρ(d)| |E_W(d)|.

   Thus one may conditionally use a true full-rho PP bound only while keeping the literal low-q complement to be paid separately. Not every large-X choice makes this useful or legal.

## Checks: separate facts from evidence
- Exact Python Fraction synthetic regression with 1,800 two-policy finite lists: zero counterexamples for the exact split and the last absolute invoice; 553 cases at equality d=X, 2,437 policy-level repeat-occurrence cases, 1,745 cases with nonzero low complement, 1,796 cases with negative signed test coefficients. These are **synthetic finite algebra**, NOT actual full87 coordinates, the PP theorem or a Lean checker.
- Git connector fetched back 212 LF lines and the actual Git TREE for the source commit identified blob `0c1c419dafe526c0e08cb892799b0d51192403d6`; fetching that blob returned exactly 10,067 UTF-8 characters and the full source. Lexical scan detected zero prohibited escapes, four public theorems and one definition.
- On the actual local execution environment: `git --version` works; `lean --version`, `lake --version`, `elan --version` each exit **127 (not found)**. No pinned Lean/mathlib/native compilation is possible without their exact installed binaries and dependency objects; they were not downloaded, changed or replaced. SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No kernel replay or transitive axiom audit. No independent review.
- This packet's file is source-only and imports prior source-only module `ImbalancedChen.P4AOriginalFull87PairedCoprimePP`; it is NOT staged into the project import tree. No model/lexical/hash test is kernel evidence. No new axiom, sorry/admit, native_decide, unsafe escape; no CI, Codex, user-machine access or resource expansion.

## Remaining precise P1.4 gap
- The integer X in this theorem is **arbitrary**; the manuscript PP integer cutoff, original complete-q exponent family, fixed chart/Gevrey W and their N-uniform permissions have NOT been proved. Do not mark `legal_PP_integer_X_verified` true.
- Quantitatively pay the exact low-q complement and the high-q stopped plus five-frontier invoice against the SAME H_N without duplicate reserve debits; full-rho PP error and q-filtered error must not be conflated.
- Recover the original 87 saved numerical witnesses, full dynamic N-dependent parent/common history, actual source member occurrence and signed ordinary/residual integrals; prove raw/finite/filtered signed gain losses, rank9/changed/tagged and independent compiler/density reserves.
- Stage exact import closure with pinned Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 and native goldbach-lean 09b97db5764ade1246bfb77206baa1b124760958; typecheck, fix errors, then separately check kernel and transitive axiom dependencies. Current whole P1.4 node remains YELLOW.

Next targeted action: identify the manuscript's actual valid fixed W_N/chart and q family, prove its source membership on BOTH real original policies, and instantiate the legal N-dependent integer X. Then derive a bound for Σ_(L_X) |Δρ E_W| or show a valid authorized direct filtered-family input; never silently discard this low-q complement.
