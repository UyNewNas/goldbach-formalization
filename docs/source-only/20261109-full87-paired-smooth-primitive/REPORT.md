# P1.4 — true paired smooth primitive recentering on one full-q population

## Recovery and fixed versions
Read actual predecessor branch `chatgpt/p1-full87-physical-q-aggregate-20261109` at HEAD `ab98eb970b9c946c2116c0d54d7cbfe81c5c585c`, including its source, REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF. Re-read actual source of `P4AOriginalFull87WeightedPrimitiveRecentering`, `P4AOriginalFull87WeightedSharpSmooth` dependencies, `P4AOriginalFull87EighthPrimeMeanLedger`, same-rho endpoint/centre correction, original physical q aggregate, actual common-history and saved87 archive-index records. Checked applicable AGENTS.md locations (none found). Prior `9649ab3` is a recovery landmark only, not a reset.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. This round read its actual §4 upper-sieve and complete-rho input, without switching versions. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`; c=`49044063/25000000`, K=`8452171/1250000` unchanged.

## Source and mathematical increment
New `P4AOriginalFull87PairedSmoothPrimitive.lean`, 181 LF lines, source blob `131f81dd5d55cdf7aedfd51441d06e24c3d076f4`, source commit `a60a99b563c5e64a0a771c05721cb3b9f394e651`, 1 public candidate theorem and 1 genuinely used private common-support proof.

Take ORIGINAL RAW policy R and LICENSED policy S, the same actual finite physical parameters N,D,cap,w,z,L, an arbitrary smooth weight W, and nonprime centre N. Set MR and MS to their actual `actualSmallRoughModuli`, M = MR union MS. Let `rho_R` and `rho_S` be the genuine `supportedPhysicalRho` (zero outside their own support), not a surrogate, and set:
- `A(d)=finitePrimitiveDiscrepancy (chenPrimePrefix (N+D)) W N d`;
- `C(d)=weightedModulusPrimeMass N D d W / totient(d)`;
- `T=weightedPrimeMass N D W`;
- `V_P=sum_(d in M_P) rho_P(d)/totient(d)`.

The candidate proves the exact finite SAME-q equation
```
(originalSmoothLiteral(R)-originalSmoothLiteral(S)) - T*(V_R-V_S)
 = sum_(d in M) (rho_R(d)-rho_S(d))*A(d)
   - sum_(d in M) (rho_R(d)-rho_S(d))*C(d).
```
This is NOT the erroneous equation without the modulus-prime term. It explicitly retains the MINUS correction and the exact coprime average, and does not take absolute values before the two signed coefficients meet at the same complete modulus. The two authentic earlier per-policy primitive recentring equalities are applied to the same W and prime prefix, and the support-union lemma is applied to their genuine TWO arithmetic tests. The nonprime N premise is an actual finite centre condition, not a new number-theory input.

The result removes a finite paired smooth arithmetic bridge gap left by the previous arbitrary-F high-q source. It neither bounds the AP discrepancy nor makes a full-q PP support cutoff X legal. In particular, this result is UNTRUNCATED and cannot be silently substituted for a legal high-q truncation.

## Verification performed / limitations
- Remote source Git blob returned as `131f81dd5d55cdf7aedfd51441d06e24c3d076f4`; 181 LF lines; forbidden proof escapes absent; delimiter balance passed; signatures checked against the real imported source.
- Independent exact Fraction arithmetic model: 2,500 nonprime-N two-policy cases with actual finite prime prefixes, exact totients, rational (including signed) W, AP fibres, coprime fibres, weighted modulus-prime corrections and repeated signed q occurrences; 0 failures. 3,883 populations contained duplicated occurrence moduli; 2,160 cases shared moduli across policies; 2,494 cases had nonzero difference; 2,491 contained signed W; 107 had D=0. This is NOT Lean elaboration, saved87 geometry or proof acceptance.
- `lean --version`, `lake --version`, `elan --version` each returned exit 127 (command not found) in the current container. Required pinned Lean/mathlib toolchain not installed; no compile, kernel replay, transitive-axiom audit or independent review. Mark SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
- No CI or Actions dispatch, Codex, user computer, upgrade, broader compute, main/master mutation, merge, or reserve charge.

## Actual unclosed mathematics
1. Original 87-row source geometry, each N-dependent dynamic parent/actual witness, prime occurrence and signed source gain must still be authenticated independently of the archive rational total.
2. Couple this full-q paired smooth identity to the SAME legal integer PP cutoff X, original prime test W/F, same-rho primitive discrepancy estimates, target-centre and endpoint expenses and H_N normalization. No o(H_N) or numeric reserve payment established. The cited §4 signed PP input remains REGISTERED_NOT_PROVED / NOT_CALLED.
3. Preserve raw/finite/filtered sixth losses, ordinary residual integral, rank9, changed/tagged and TWO independent compiler/density reserves. P1.4 parent stays YELLOW.

Next concrete action: with an already available matching pinned Lean environment, stage actual imports and compile this source plus dependencies; fix true Lean errors before claiming COMPILED. Mathematically, use the exact paired AP-minus-modulus-prime identity to analyze legal-X truncation and the unchanged original source-specific invoices, rather than wrongly treating primitive discrepancy alone as the smooth mean error.
