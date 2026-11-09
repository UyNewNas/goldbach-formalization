# P1.4 — same-prime signed low-q cancellation on the original complete rho

## Recovery, fixed versions, and new source
- Exact predecessor HEAD **dd7e601d489c857a93df578e0004c69686f322de**, branch `chatgpt/p1-full87-lowq-local-prime-fibres-20261109`. Read its REPORT, REGISTRY, INPUT_BOUNDARY, full Lean source and HANDOFF. Branch HEAD re-read before creating the independent continuation; no concurrent advancement observed at that moment.
- Independent branch: `chatgpt/p1-full87-lowq-primewise-signed-20261109`. New source commit **4039b0d28def9c4994e3831f88abd4f849e81a02** [skip ci], path `docs/source-only/20261109-full87-lowq-primewise-signed/P4AOriginalFull87LowQPrimewiseCancellation.lean`, Git blob **89308c3f40d11ccccfc74bcc944bdf3ba56fcc58**, 192 LF lines. Two public candidate theorems, three private supporting proofs, one explicit arithmetic kernel definition. Remote source read back matched that blob.
- Pinned paper `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, verified blob **d529bea2ecfcc74d64fc1664ac770a3becaa7c79**. No migration to November 6 paper.
- Required Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants c=49044063/25000000 and K=8452171/1250000 unchanged. No AGENTS.md found at repo root or under docs/source-only at the confirmed baseline.

## What is actually reduced

The predecessor's local bound charges each low complete modulus independently:
[
|E_{m high}|le |E_{m full}|+
 sum_{dle X} B(d),C_W(d).
]
Those absolute values erase possible signed cancellation among the SAME original low-q physical coefficients when viewed at a fixed prime.

Let (kappa_N(p,d)=mathbf 1_{pequiv N;(d)}
 -mathbf 1_{(p,d)=1}/arphi(d)) with the project's actual totient, and let
(Deltaho(d)=mathrm{supportedPhysicalRho}_{RAW}(d)
 -mathrm{supportedPhysicalRho}_{LICENSED}(d)). The new source establishes
the candidate finite Fubini identity on the original prime prefix (T_N):
[
 E_{m low}
 =sum_{din Q_{le X}}Deltaho(d),
       mathrm{finitePrimitiveDiscrepancy}(T_N,W,N,d)
 =sum_{pin T_N}W(p)
       sum_{din Q_{le X}}Deltaho(d),kappa_N(p,d).
]
It then pays an alternative per-prime envelope:
[
oxed{|E_{m high}|le |E_{m full}|+
 sum_{pin T_N}|W(p)|,
 left|sum_{din Q_{le X}}Deltaho(d)kappa_N(p,d)ight|.}
]
The modulus set is precisely the original union of RAW/LICENSED physical supports filtered by `d ≤ X`; `d=X` is low. Full Rosser beta, signs, the actual fifth/sixth policy, the original 87 Cell ledger's physical rho, and every occurrence multiplicity remain in `supportedPhysicalRho`. The original full-rho PP input is not applied to a new filtered family. The `d=1` kernel vanishes automatically for positive physical q.

This is a **different, potentially sharper finite invoice** than `Σ_low B(d)C_W(d)`, not an additional fee. By a separate elementary finite triangle argument it is no larger than a per-q exact-contrast absolute invoice, but that comparison and any strict saving for ORIGINAL data are NOT formalized or claimed. This packet does not supply a bound (o(H_N)), certify the saved87 affine geometry, or prove original PP permissions.

## Actual checks / status
- Source-only blob matched GitHub read-back at the source commit. Static scan: no `sorry`, `admit`, `native_decide`, `unsafe`, or new `axiom`; balanced () and []; 192 LF lines. This is not a parser, elaborator or kernel check.
- `python3 CHECK_SYNTHETIC.py`: 1200 exact Fraction synthetic tests of q-then-prime versus prime-then-q, `|low|≤primewise`, high/full split, and primewise ≤ per-q exact-contrast envelope; 0 model counterexamples; 901 scenarios had a strict synthetic saving. No actual original saved87 data was tested.
- `lean --version`, `lake --version`, `elan --version`: each **exit 127**, command not found; no installed pinned toolchain/dependency graph. No compilation or kernel acceptance. Status **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Transitive axioms and independent review not checked.
- No Codex, new Actions/CI runs, toolchain upgrade, main/master mutation, forced ref update, or external analytic proof.

## Exact remaining obligations
1. Obtain the actual N-dependent saved87 87-row geometric certificate and full dynamic parent/common history/source membership; equate the corresponding true signed selected/residual ordinary integrals and original archive gains. Synthetic reductions do not certify them.
2. Determine a genuine same-(H_N) bound for the new *original* signed low-q prime kernel, or for the predecessor's (B(d)C_W(d)) fallback, without treating signed cancellation as automatic. The new envelope itself may still be large.
3. Prove the original full-q family and real (W_N) comply with fixed-before-N singleton PP/Gevrey conditions and legal integer X; PP remains external and only applies to licensed full (E_{m full}).
4. Pay actual high-q stopped/five-frontier, endpoints/centre, raw/finite/filtered, ordinary, rank9, changed/tagged and separate compiler/density reserves once each.
5. In a preexisting matching environment stage `ImbalancedChen/P4AOriginalFull87LowQPrimewiseCancellation.lean` plus its original source-only imports and run a targeted `lake env lean`, then kernel replay, transitive axiom audit and independent review. No COMPILED label before success.

**P1.4 remains YELLOW**; all new Lean theorems remain candidates.
