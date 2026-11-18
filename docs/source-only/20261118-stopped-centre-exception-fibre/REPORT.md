# P1.4 — actual stopped centre exceptional q0 fibre (N ≡ 0 mod 4)

## Recovery / exact source boundary
Direct verified predecessor: `660476ae9f3d6040c1a6c299f6f094f88adec85c`, branch `chatgpt/p1-full87-stopped-centre-upperthird-20261118-0910`. Read its REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and complete 283-line source. Read earlier upper-third exact AP and centre support proofs, real fifth signed source, and fixed manuscript. Root, docs and docs/source-only AGENTS.md not found. The predecessor branch matched this SHA (ahead=0, behind=0); no rewind or main edit.

New source commit: `1c05652b978fd60cdacd5aad83481a2360d0ca7a`.
Branch: `chatgpt/p1-full87-stopped-centre-exception-fibre-20261118-1015`.
Source: `P4AOriginalFull87StoppedCentreExceptionFibre.lean`, 282 lines, verified Git blob `e41224b6dc37f0d0cf00979b9bb6a912b7d7471b`.

## Concrete new manuscript-side finite candidate proof
The preceding source proved complete q-coprimality for EACH actual `receiverTest N`-generated `sharedRankFour` fifth/sixth event and used it to kill upper-third centre correction when N ≡ 2 (mod 4). The remaining N ≡ 0 (mod 4) case was NOT covered by the fixed physical-rho <=1 invoice.

This continuation treats an even composite N divisible by four with N>=8. For every complete target-coprime d, the strict upper-third centre AP term is EXACTLY
```
upperThirdCentre N d = if d = (N-2)/2 then 1 else 0.
```
This follows from the original centre prime support theorem forcing P=2 and N-2=2d, and the prior exact count-one theorem at that one possible fibre. The N>=8 hypothesis ensures the strict N<3d gate at q0 and is not erased.

The explicit finite occurrence-level fibre
```
exceptionalFifthPlusFibre = Σ a ∈ largeFifthRosserIndices,
   if X < a*(p::pre).prod ∧ a*(p::pre).prod = (N-2)/2
   then actualSmallRosserPlus a else 0
```
is proved exactly equal to the original `largeFifthPlusAttachment` on the singleton arithmetic test, retaining all original PLUS-beta signs, complete a*b, strict X<q, equality exclusion and Finset indexing. The original `commonLargeSixthKernel` then sums these fibre payments over the unchanged ordered `remainingAfter` occurrence List with the genuine `signedTreeCoefficient true fifth.massAfter`.

The previous actual-history full-modulus coprimality is used to transport the original upper-third centre correction into this singleton test at EACH genuine stopped event. A nested List congruence establishes
```
actualFixedSignedFifthTail(..., upperThirdCentre N)
  = actualFixedSignedFifthTail(..., exceptionalCentreFibre N).
```
The generator on both sides remains `actualFifthSixthWithoutBoth ... (receiverTest N)`; no second producer, no physical rho identification, no count simplification, no dropped event multiplicity. Linear transport into the original four-source RAW-minus-LICENSED equation then isolates lower-third centre payment PLUS this ONE exact signed q0 occurrence coefficient, with no duplicate invoice.

**What was actually removed:** the need to treat all N/3<q<=N centre corrections as independent stopped terms when N%4=0. Their entire genuine event ledger has support on q0 only. **What is not removed:** the unknown size/sign of the actual stopped coefficient at q0; the physical-rho bound <=1 cannot be applied without a bridge.

## Verification / limitations
- GitHub source commit and 282-line blob readback confirmed, forbidden-token source scan negative.
- Local command checks: `lean --version`, `lake --version`, `elan --version` all exit 127 (command not found). No pinned v4.33.0-rc1 + mathlib + native dependency closure installed; source-only imports require staging. No local elaboration, compilation, kernel replay or axiom audit.
- Independent integer arithmetic: N=8,12,...,800, gcd(d,N)=1, 1<=d<=N; 32,624 genuine upper-third centre-fibre cases versus singleton, 0 failures and 199 nonzero special moduli.
- Additional 2,475 synthetic rational signed full-q weighted list comparisons using original strict X<ab and coprimality filtering: 0 failures. These do NOT execute the real fifth/sixth event generator or Lean proof bodies.
- Overall **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. No independent review, saved87 certificate replay, numerical H_N saving, certified asymptotic bound or full P1.4 closure.

## Fixed paper / external input / next exact work
Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob verified `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. External signed sharp-prime PP: labels `eq:current-PP`, `lem:current-sharp-prime`, `eq:current-sharp-pi`; actual same physical signed rho, complete squarefree coprime q<=N^theta (fixed theta<1), smooth-singleton/endpoint premises and original H_N normalization. **REGISTERED_NOT_PROVED_NOT_CALLED**. No external PNT/Mertens/BV/spectral project.

Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000 unchanged.

**NEXT exact actions:** obtain the true stopped q0 coefficient bound/possible exclusion from actual fifth history and all signed occurrences, NOT a free physical rho <=1 bound. Pay remaining 3q<=N centre strip and high-q primitive / modulus-prime, ordinary residual integral, full87 actualParent and saved87 source/certificate, three physical outside bills, two independent reserves, rank9 changed/tagged. Stage and compile with the exact pinned toolchain if locally available. No master/main, merge/force, CI, Codex, increased resources or other jobs.
