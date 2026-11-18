# P1.4 — exact exceptional centre coefficient and modulo-four obstruction

## Recovery / scope
Read the predecessor's complete 203-line source, REPORT.md, REGISTRY.json, INPUT_BOUNDARY.md and HANDOFF.md at `fd2314bc48b6e3ae81dbd366729261cb310f110e`; checked the branch is exactly that commit before creating an independent continuation. Also examined original `ImbalancedChen/ChenInitialPrimeSource.lean`, `ImbalancedChen/ActualSmallRoughAttachment.lean`, the even upper-third exact receiver source and the frozen manuscript blob. The ancestor AGENTS.md paths queried were absent.

New isolated branch `chatgpt/p1-full87-upper-third-centre-parity-exact-20261118-0815` starts **exactly** at `fd2314bc48b6e3ae81dbd366729261cb310f110e`. New Lean source first commit `cd47f22bdba26e027af829b965983a9008af4240`. No main/master modification, merge, CI dispatch, Codex, pin changes, or other automation work.

## New finite mathematics
Previous theorem: for a non-prime centre N, a complete modulus d coprime to N and strict N<3d, a centre divisor prime P in the original AP fibre must be P=2 with N-2=2d; hence only d0=(N-2)/2 may contribute and the physical invoice has absolute value <=1 for each fixed policy.

New results, all Lean candidate proof bodies:
1. If N % 4 = 2 then d0 is even while N is even. Therefore d0 is NOT coprime to N. For every actual complete coprime d under N<3d, the original `chenCentrePrimeAPCount N N d` is exactly **zero**.
2. If N is even, 2<=N, non-prime, d coprime N, N<3d and N-2=2d, the original centre AP fibre is **exactly {2}**, not only a subset; its real count equals 1.
3. Extract the exact single-complete-modulus identity on the unchanged original `actualSmallRoughModuli` and `actualSmallRoughRho`. For even non-prime N the physical high-third correction is `rho(d0)` exactly when d0 is in the actual support AND both strict gates N<3*d0, X<d0 hold; otherwise it is 0. Coefficients, Rosser/beta attachments, policy and full modulus remain unchanged.
4. In the class N%4=2, each actual physical high-third centre invoice and the RAW-minus-LICENSED centre correction both equal **zero**, strengthening the former <=1/<=2 payments without adding an extra invoice. The N%4=0 case retains the previous <=1/<=2 general bounds and the exact single coefficient.

This is a genuine error-invoice refinement, **not** an H_N-relative smallness estimate, a proof of signed prime cancellation, or a bridge to the actual stopped fifth/sixth occurrence ledger. The physical coefficient cannot be substituted for an occurrence coefficient without proving the exact connection. There is no implicit payment of the primitive or modulus-prime components.

## Diagnostic checks, not proof acceptance
- Independent integer enumeration: even composite N=4..800, all 1<=d<=N with gcd(N,d)=1 and strict N<3d: **43,328 pairs**, zero exceptions to the exact 0/1 exceptional-fibre formula; **199** nonzero fibres, all at the one modulus d0 and none with N%4=2.
- Random finite *synthetic* support and signed rho diagnostic (not the actual tree): **1,197** trials, exact single-coefficient identity and mod-four zero both held with zero failures.
- The new source is 190 lines, blob `bc6d84e6788c3f2511f3f1436e640e796e041626`, SHA-256 `ecdae24be8dbca22ad1020f8d5c576dbaa05199638922cd84ed85fab2ad44112`. Fetched back from GitHub and blob matches local `git hash-object`; static forbidden-token scan negative.
- Actual commands `lean --version`, `lake --version`, `elan --version` all exited **127**, `command not found`. The fixed Lean/mathlib/native closure is absent. Source-only ancestor would need staging under `ImbalancedChen.P4AOriginalFull87UpperThirdCentreInvoice` before a matching pinned compilation. No elaboration, kernel replay, transitive axiom audit, saved87 archive replay or independent review.
- **Verification level: SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Source can contain elaboration/tactic errors.

## Frozen identity and next precise obligation
Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` at `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000. No changes.

The only analytic input registered is the original signed sharp-prime PP at this exact manuscript pin (full squarefree coprime q<=N^theta with fixed theta<1, smooth-singleton, original H_N normalization and same original rho). Its status remains `REGISTERED_NOT_PROVED_NOT_CALLED`; there is no callsite.

NEXT: (a) Lean-stage/import and compile this source in the exact fixed environment if available, correcting any real elaboration errors without a new CI; (b) prove or safely bound the actual same-`sharedRankFour` and original fifth/sixth stopped centre correction by grouping COMPLETE q with occurrence multiplicities, rather than replacing it by the physical <=1; (c) bound original high-third switched signed prime sum and N^theta<q<=N/3 band; (d) primitive/modulus-prime errors, ordinary integral/actualParent, saved87, all three outside bills, distinct compiler/density reserves, rank9 and changed/tagged.

**P1.4 remains YELLOW.**
