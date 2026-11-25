# P2.9 — original Gamma5 integer support and geometric Family

Manuscript: `chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`, release-20261106. Source baseline: `goldbach-formalization@a929011ec95843553fc2e10b7291c8077e0952c0`.

## Current verification status

**IN PROGRESS. The integer-support module has passed normal Lean compilation, independent stock leanchecker replay, and the complete owned-declaration/transitive-axiom audit. The geometric Family batch is queued. Full P2.9 remains open.**

| Module | Current evidence |
|---|---|
| `P2FiniteMarkedGamma5IntegerSupport` | Job `888004360c524fdf8aa007deec31fcd0`, exit 0; 7 owned declarations; exact source SHA256 `ecdb5e50b1f4dcb645767dfb7ecf8dd9d90f560f54c8d358c568f0610d5c0315` |
| `P2Gamma5AdmissibleFamilyCore` | Exact extraction and independent source review; joint compilation/replay/audit pending |
| `P2FiniteMarkedGamma5AllRankEulerBudget` | One public forwarding theorem added to the accepted owner; new source requires new acceptance |
| `P2FiniteMarkedGamma5GeometricFamily` | Source implemented and independently reviewed; job `5b7bff2cca7f4a9dade3b8c2b391a13a` queued |

The eventual evidence package will preserve distinct gates, exact sources, project dependency bindings, full owned declarations, types and transitive axioms. Source-level counts and dependency-cache reuse are not new proof acceptance.

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
