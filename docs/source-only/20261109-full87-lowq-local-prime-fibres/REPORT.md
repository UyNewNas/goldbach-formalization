# P1.4 — literal local prime-fibre envelope on the original low-q first-disagreement books

## Recovery and fixed boundary
- Verified predecessor branch HEAD: 274c2797c2cccce71dd7cb19d5ba0148ba774c5d at \`chatgpt/p1-full87-lowq-real-ledger-envelope-20261109\`. It is the previous metadata commit, NOT the initial 9649ab3 navigation point. Original predecessor REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF and complete Lean source were read. The original same-q and cutoff proofs, source dictionary, active-eighth history, the signed Rosser helper and Chen prime-source supplier were also inspected; root AGENTS.md is absent in the pinned branch tree.
- Frozen paper: \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/manuscript-body.tex\`, blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`; no switch to the later release. Constants \`c=49044063/25000000\`, \`K=8452171/1250000\`.
- Fixed local toolchain requirement: \`leanprover/lean4:v4.33.0-rc1\`, mathlib \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`, native \`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958\`.
- Independent continuation: \`chatgpt/p1-full87-lowq-local-prime-fibres-20261109\`; source commit \`aaa0d641fa05d54e07c5b4755e72757dc1c23bbb\` [skip ci], \`docs/source-only/20261109-full87-lowq-local-prime-fibres/P4AOriginalFull87LowQLocalPrimeFibres.lean\`, Git blob \`8c0b7e84f14ba3ff4507efcfae231c2d10b404d1\`. Source is 212 LF-ended lines, one public candidate proof and four private support proofs. Git data tree and branch update were non-force, with an expected exact predecessor HEAD; the source was read back.

## Actual new finite proof candidate
Previous bound: \`|E_high| <= |E_full| + 2*T_W*Σ_(q<=X)B(q)\`, using the full absolute mass \`T_W = Σ_{p∈chenPrimePrefix(N+D)}|W(p)|\` at EVERY low q. It is generally too coarse to infer an H_N payment.

Define a real, modulus-sensitive prime-fibre charge, for d>1:
\[
C_W(d)=
\sum_{\substack{p\in\mathrm{chenPrimePrefix}(N+D)\\p\equiv N\ (d)}}|W(p)|
+\frac1{\varphi(d)}
\sum_{\substack{p\in\mathrm{chenPrimePrefix}(N+D)\\(p,d)=1}}|W(p)|,
\quad C_W(1)=0.
\]
It uses the same original prime prefix and original coprime normalization as the frozen manuscript. For all positive d the candidate proves \`|finitePrimitiveDiscrepancy (chenPrimePrefix (N+D)) W N d| <= C_W(d)\` from the two literal finite-sum absolute inequalities, and the existing proven exact zero at modulus one. This leaves any signs of W intact in the discrepancy; absolute values enter only the safe invoice.

For original RAW and LICENSED policies and SAME complete signed physical coefficient \`Delta rho(d)\`, reuse the existing actual pointwise book \`|Delta rho(d)| <= B(d)\`, where B is precisely the one-sided stopped first-disagreement plus RAW-outside/87 Cell producer/LICENSED-outside occurrence invoice. Because the actual q support is positive, the candidate gives
\[
\boxed{
|E_{\rm high}|
\le |E_{\rm full}|+
\sum_{\substack{d\in M_{\mathrm{RAW}}\cup M_{\mathrm{LICENSED}}\\d\le X}}
B(d)\,C_W(d).
}
\]
The q=X equality belongs to low q. The q=1 charge is zero. There is no new rho, class mask, policy, parent or numeric certificate, and no duplicate payment of the prior global 2*T_W invoice. For d>1 the local bound cannot exceed the old 2*T_W by elementary positivity and phi>=1, but that comparison was not separately kernel-checked. It is not asserted to be o(H_N).

## Validation actually performed
- Remote read back: Git blob \`8c0b7e84f14ba3ff4507efcfae231c2d10b404d1\`; 212 LF-ended lines; no forbidden proof-escape token; (), [], {} balanced (static-only).
- Independent exact Fraction synthetic model: 1500 scenarios, positive coprime moduli and a genuine finite prime prefix with mixed-sign W; all individual \`|D_W(d)| <= C_W(d)\` and full/high/low paired-envelope inequalities passed. 62,808 synthetic positive-modulus charges strictly lower than the 2*T_W fallback; 1500 q=1 checks had zero primitive discrepancy and zero charge. These are algebraic tests of the envelope, NOT original saved87 replay.
- Local environment \`lean --version\`, \`lake --version\`, \`elan --version\` all returned 127 (command not found); no matching pinned Lean/mathlib/native build available in the 5.8GiB container. No local Lean elaboration or compile, no kernel replay, no transitive axiom audit, no independent review. Status **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; there is no proof-acceptance credit from the finite tests.
- No CI dispatched, no Codex, no branch merge, main/master mutation, force push, new cloud resources, toolchain/pin change or external classic analytic proof.

## Concrete remaining proof obligations
1. Prove an actual asymptotic estimate for \`Σ_(d<=X) B(d)*C_W(d)\` on the single H_N ledger. This local charge can still be enormous. The valid Gevrey W_N and integer PP X have NOT been instantiated.
2. Authenticate original saved87 affine/source witness rows and their N-dependent actual eighth-state membership, full dynamic parents, common history, signed selected/residual integrals and archived gains; no synthetic archive sum supplies that link.
3. Establish the actual external PP input's fixed-policy permissions and call it ONLY on licensed \`E_full\`, not on each B term; separately control lowq, the highq five-class frontier, center/endpoints, raw/finite/filtered, rank9, changed/tagged and two independently funded reserves.
4. In a previously authorized environment *already containing* exact pinned dependencies, stage source-only imports under \`ImbalancedChen\` paths and execute a targeted \`lake env lean\`. Record real errors and fix locally before using COMPILED; kernel and axiom audit remain separate.

P1.4 parent remains YELLOW.
