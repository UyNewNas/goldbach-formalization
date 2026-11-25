# P2.9 — original Gamma5 integer support and geometric Family

Manuscript: `chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`, release-20261106. Source baseline: `goldbach-formalization@a929011ec95843553fc2e10b7291c8077e0952c0`.

## Current verification status

**IN PROGRESS. The two light modules below have passed all validation gates, with 19 owned declarations. Three additional radial modules have now passed normal compilation, stock leanchecker, named kernel replay and complete owned/transitive-axiom audit, with 42 owned declarations. Core and geometric Family remain pending. Full P2.9 remains open.**

| Module | Current evidence |
|---|---|
| `P2FiniteMarkedGamma5IntegerSupport` | Accepted, 7 declarations; source `ecdb5e50b1f4dcb645767dfb7ecf8dd9d90f560f54c8d358c568f0610d5c0315` |
| `P2FiniteMarkedGamma5AllRankEulerBudget` | Updated owner accepted, 12 declarations; source `27aa18059ed29e5a053b6f0388983dfebb93f3784dad135106a1d6cdadc2b33b` |
| `P2Gamma5AdmissibleFamilyCore` | Exact 823-byte structure retained; missing ContDiff scope and direct real-power/log import repaired; validation queued |
| `P2FiniteMarkedGamma5GeometricFamily` | Source reviewed; new validation task `a40329930dfa4f9fa8a4fd41bd355296` |

The complete accepted evidence is in `evidence-b/manifest.json` and
`evidence-b/all.tar.gz`. The 166849-byte archive has SHA256
`37462aecf0d1217dd54eb6310df967dbef5073a0860833693fa78611c4fe78e3`.
It preserves exact sources, dependency/object bindings, full declarations,
types, stock replay and standard-axiom records. Its two modules contain
19 distinct owned declarations. The existing Euler proofs are reused;
the added API is only a public zero-function forwarder.

The exporter retains generic Winner9 coverage fields. Those are exporter
context, not new P2.9 obligations or a request to redo the 17,572 original
rows. Core and Family are excluded from the accepted-module list.
`second-family-compile.log` preserves all diagnostics before the transfer
payload; the exact complete stdout is retained beside the evidence.
`DIRECT_IMPORT_REPAIR.json` records the minimal next repair.

## Mathematical increment

For the unchanged original `finPhysicalProfile`, nonzero weight on a natural tuple implies every coordinate is positive. Every indexed coordinate divides the positive complete product; the existing original product gate therefore gives

\[
W(u)\ne0\implies
1\le u_i\le\left\lfloor e^{\mathrm{width}}N\right\rfloor_{\mathbb N}.
\]

This proves finite support on **all natural tuples**, retaining repeated entries and the empty old/tail block cases. The prime-support field is a subset of that support, without adding a primality filter to the smooth weight.

The Family module constructs the original `P5Z.AdmissibleAllRankIntegerGeometricFamily.Family K`, preserving the original structure declaration byte for byte. For each fixed `(k,r)`, `a>0`, fixed `0<width≤1`, arbitrary fixed `logQ : ℕ → ℝ`, and `k+2+r≤K`, its active-rank function equals the original profile at every scale above the existing threshold

\[
N_0(a)=\max(e,2^{2/a}).
\]

Other ranks and the finite initial set of smaller scales are zero. The structure uses `aStar=a`, `lower=1/2`, `upper=exp 1`. Existing smoothness, real support, and Euler estimates plus the new finite integer support discharge the fields. The natural derivative constant is chosen before the moving scale, endpoint function, split, word, and point; the logarithmic exponent is `B=0`. Width is fixed before that constant is chosen.

No Family, support conclusion, Euler budget or prime-product target is assumed as a new premise. This is a geometric construction for a fixed split, not a claim that all arithmetic histories, their collar costs or their PP estimates have been admitted.

## Reuse and provenance

The static closure is 15 project modules: 11 exact previously accepted sources, one existing owner needing revalidation after a public API addition, and three new modules. It imports no additional native research modules.

`docs/source-only/20261125-p2-9-geometric-family/` preserves the exact original structure, previous full owner, new owner postimage, original accepted Euler owner and the exact additive forwarding declaration. Its manifests distinguish static source preservation from Lean acceptance. Heavy consumers of the old Family owner must select the new postimage; their compatibility is not newly accepted here.

## Remaining P2.9 boundary

- Actual marked-history source admission and the original profile/coordinate dictionary require their full existing history dependencies to be qualified.
- Collar and ordinary-mass estimates, the original same-rho signed PP/VM estimate, and W1/W2 directed count debts remain distinct analytic responsibilities.
- The current native-Wu Binder still assumes 29 H247 comparisons and further integral inputs. These are sufficient conditions for that Binder route; the missing adaptation between native moving boxes and the manuscript's actual finite enhanced families prevents treating them as the sole equivalent manuscript target.

See `MANUSCRIPT_SEMANTIC_BOUNDARY.md` for exact definitions, quantifier ordering, and source references. It does not assert that the 29 comparisons are false or that the manuscript is false. Further work should supply count licences on the original finite marked families, with their actual Q, labels, gates, ceiling and Theta.

`REVIEW.md` records the independent static mathematical/interface review. No global board promotion or full-P2.9 completion follows from this increment.


## Subsequent manuscript-internal source work

The actual U4 source adapter is preserved in `docs/source-only/20261125-p2-9-actual-family/`, with its independent review in `ACTUAL_SOURCE_REVIEW.md`. It derives its source rank and reuses the old plateau. Its large arithmetic-history closure remains unqualified and its new proof credit is zero.

The radial collar candidates are preserved in `docs/source-only/20261125-p2-9-radial-collar/`. They use the actual original floor and rank, the existing unrestricted fixed-band compatibility supplier, and the original multiplicity bound. FrozenConstants, PrimeDivisorFloorCore and the repaired RoughMass now pass every normal/kernel/owned/stock gate. Their exact 42-declaration acceptance is recorded in `docs/verification/20261125-p2-9-radial/ACCEPTANCE.json`; the tuple/profile/natural consumers remain source-only. The exact natural-prime support/sum dictionary remains source-only. The already existing sharp Gamma5 cost and seed-conversion proofs are reuse inputs.

`NEXT_PROOF_FRONTIER.md` records the precise radial shell, manuscript double-limit order, provider selection and the distinction between a single-ambient payment and the complete marked-history/J chain. `SCOPE_REPAIR.json` records the failed first Family compile and the exact scope-only correction; no successful Family receipt is inferred from that correction.

The exact original marked-mass root-cell partition is in
`docs/source-only/20261125-p2-9-actual-root-cells/`. It is source-only and
retains all actual p-dependent positions, marks and repeated products.
The existing native supplier's P1 binding receipt and exact FixedCompat
source are in `docs/verification/20261125-p2-9-native-supply/`; those are
reused supply, with zero new manuscript theorem credit.
