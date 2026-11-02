**SOURCE_REVIEW_PASS — narrow static source scope only.** Task `compact_jensen_bounds`, independent reviewer `/root/k_review_moments`, 2026-11-02. The overall task and P2.4 remain **OPEN**. `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `verification_inherited=false`; concrete finite guards are **UNEVALUATED**.

This verdict accepts the frozen source route for the original selected Q80 Jensen option and the elimination of its internal analytic/denominator premises. It does not certify elaboration, the complete transitive source chain, a numerical run, the final all-candidate enclosure, or the historical endpoint. No blocking defect was found in the reviewed local mathematical scope.

The frozen delivery is in `docs/source-only/20261102-certificates-l/compact_jensen_bounds/`.

| Source | Raw SHA256 |
| --- | --- |
| `P2OriginalCompactQ80JensenMoments.lean` | `654b25f7603671670eea362b343d5da7efe9284f5e74bae4bb8d6bf0a8a33406` |
| `P2OriginalCompactQ80JensenSelection.lean` | `174fa022e86cc7d5dcef8e2155aa33159bd94e5b9292d98ecfaac92df425697a` |
| `P2OriginalCompactQ80JensenGeometry.lean` | `42daa3847edee6ca3e9f2d6f2598404f6b2509416d2bb8870b2c04d5c17b2f45` |
| `P2OriginalCompactQ80JensenBounds.lean` | `1c693b414c85c7f31a1598cdc209d63c99702083943e6db5fad60262a5987e87` |

- `REGISTRY.json`: `2eeab629dd6d732a5ed12d0c43a3fbedf675ff103fbd7545e6570e9cee3ff47b`.
- `REPORT.md`: `28626806654a673c00f685715b0a23a87e52c2488b7752dda6fee6f97b4fdebb`.
- The read-only hash/length audit matched **all 64 registered pin occurrences covering 55 distinct files**, including the four source files, report, direct imports, selected upstream suppliers, manuscript/producers, and registered native APIs. The registry's own hash also matches the author's freeze.
- `EXTRA_TASKS.json`, task `compact_jensen_bounds`, and its shared-interface policy were read; raw SHA256 `aca79870afff90dc8cb27d8255f2a1bb0b6abe8e19e49da25df6860cb4e068c9`.

The accepted export is `ImbalancedChen.P2OriginalCompactQ80JensenBoundsSourceOnly.jensenDifferenceUpper_sound` (Bounds:264–286). Its only inputs are the original coordinate `Geometry box`, literal full-domain guard `inside box`, and literal result `jensenDifferenceUpper box = some j`. It concludes nonnegativity of `val j` and
`∫ rootCell box compactKernel ≤ val j * realChargedMass box`.
The result equation identifies the original selected option; it does not assume its soundness. There is no desired candidate/full-leaf estimate, supplied mean identity, probability normalization, query bound, cap minorant, endpoint range, or chord-slope sign hidden among the exported premises.

The original mathematical source `extended-prefix-upper.tex` 8–40 and current numerical-completion context were checked against the original `certify_extended_prefix.py` and its `certify_conservative_chen.py` arithmetic. The target remains the actual ordered compact integral with `Theta=299/500`, `mu=25/128`, `rho=19/96`, cutoff `1/100`, normalized lower sieve factor extended by zero at two, actual gated cap `min(Theta,A)`, and factor `4/(x*y*z²)`. The actual source and public producer have identical raw SHA256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`. No alternate P112/P160 quadrature or historical output supplies a premise.

The chosen affine row comes from the existing source `find?`, filter, and strict midpoint fold. Selection:22–160 preserves the order x, y, xy, xyz, xz, yz, B, the first rising branch at equality, and the previous row at midpoint ties. The above-mu branch is the actual fall-x tuple. Geometry:193–238 proves the ordinary minorant against the actual cap; below mu it uses the ordered-domain six-tent identity and original branch/root tests, and above mu it uses the surviving v(x) comparison. Equality at mu is not replaced by a global fixed-cap identity.

The mass and moments are genuine integrals. The existing BoxMoments source derives normalization of restricted Lebesgue measure with density proportional to `1/(x*y*z²)`, then derives x, y, 1/z, x/z and y/z moments. The ordered prism has a separately derived probability law, with true max/min moments. Geometry:35–156 binds the raw means to physical coordinates: x/y/max means gain D while inverse-z mean loses D, so the arguments are dimensionless. Bounds:69–81 identifies the actual ordered-half mass, including factor4. These are neither assumed `hMass`/`hMeans` fields nor independence claims about ordered x and y.

Jensen has the required direction. The actual lower factor is concave only on `[2,∞)`; the original full-cell corner test implies NEW≥2. Consequently `E f(NEW) ≤ f(E NEW)`. OLD uses a lower endpoint chord and is then subtracted. In the strict-chord branch, the original noncrossing guard and `oldHigh>2` imply `oldLow≥2`; global concavity across two is never used. The `oldHigh≤2` branch, including equality, uses nonnegativity of the actual OLD factor. These routes are composed explicitly in Bounds:83–188 and 207–286.

The symmetric branches retain the historical kernel. Below mu, the source square chord is exactly the average of the selected tent's and its x/y partner's **true ordered chords**, which have the same endpoints. Both are bounded against the same actual OLD integral. The average identity needs no ordering of the lower-query outputs. B uses its true equal-coefficient sum mean. Above mu, the proof uses
`E max = 2*(b*log(b/a)-b+a)/log(b/a)^2`
and the true ordered argument. It never asserts symmetry of the raw asymmetric cap/history kernel, nor halves that raw kernel without a justified domain argument.

All Q80 arithmetic remains literal. Moments:59–85 proves exact integer equality for Python scalar `__rmul__` operand order through the four corner products and both outward roundings. The actual mesh16384/max12 table, original 32-term log interpreter, rational num/den endpoint queries, every intermediate interval operation, signed division, clipped weight and signed endpoint difference are retained. Moments:194–264 derives the upper NEW query and lower OLD chord. The old chord uses the lower endpoint after general signed interval multiplication, so no `flo≤fhi` assumption is introduced.

The division guards are derived from original geometry. The chosen rows satisfy `0<e≤256`, `b<e`, and `c<e`. One integer x step and the positive residual yield
`oldHigh-oldLow ≥ 1/(e*z1) ≥ 1/Q`.
This proves strict span and positivity of the rounded chord denominator (Selection:145–234). Parent LogGuards derives `log.lo≥2^40` from raw lattice width and the first original series summand, and hence a positive rounded squared-log lower endpoint. Bounds:35–62 consumes these proofs and exports `source_jensenAssertions` without external guard hypotheses. The equal-endpoint chord branch is unreachable under the strict-width exported Geometry; zero-width domains remain separate null-domain cases. No concrete guard was evaluated.

The exact parent bindings used here are:

| Parent source | Raw SHA256 |
| --- | --- |
| `P2OriginalCompactQ80Encloser.lean` | `9a83abd21750ff9ed799dc283e4c3130fc02749eedc9ef246d98af0b310ae9f8` |
| `P2OriginalCompactQ80Leaf.lean` | `22625cbdbd57f6412e0074440fc30723e7c868506ec297026986368dd393bad4` |
| `P2OriginalCompactQ80LogGuards.lean` | `f0c816bde7fb64b89c3d6a65a3d59d7902f53e6d793e43538bc3edcb8666c4db` |
| `P2OriginalCompactQ80Symmetry.lean` | `568a270796611264c366940d95d8a84037100f3e4938bfdaccd2dc21acc7e595` |

The native Mathlib source was read at
`\\wsl.localhost\Debian\home\slava\codex-lean-ve\native-packages\mathlib\Mathlib`.
The repository manifest specifies Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; repository and native Mathlib toolchain files both read `leanprover/lean4:v4.33.0-rc1`, with SHA256 `62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef`. This review ran no Git command and makes no independent HEAD assertion. It binds the actual raw API bytes. In particular `Analysis/Convex/Integral.lean` has SHA256 `1b3115887fabf0dccc2fed689d1f1ddc7a114b5de4594e752c02908a445aafb4`; its `ConcaveOn.le_map_integral` at 208–211 has the probability, integrability, support and direction used here. The derivative-concavity, measure-density, product-integral, ordered-division and coordinate-cancellation APIs were also inspected; their exact raw pins are recorded in the JSON review.

Remaining obligations are explicit:

- User-owned installation, elaboration, kernel verification, and complete import/axiom audit of these uncompiled source candidates.
- Final composition of every candidate minimum and lower bound, actual mass endpoints, odd half rounding, and final integer floor/ceiling. The original parent AST retains these operations; this local export stops at `val j * realChargedMass`.
- The actual complete reachable forest/queue/run, table initialization assertions, all decisive finite certificate checks, and the historical compact endpoint `144590669409566793572719/2^80`. Their finite status remains UNEVALUATED.
- Complete P2.4 and broader density/counting targets remain OPEN. No resource-feasibility result or improved final constant follows from this review.

Only `L/reviews/compact_jensen_bounds.json` and `.md` were written. No Lean/compiler/meta execution, producer replay, numerical checker, Git, subagent, or quota operation was used. The frozen K saving19 review remains SOURCE_REVIEW_HOLD and byte-unchanged: JSON `19bda540a0bd807a43fdf8a4a75106a16837cd82fbfdf5f6e1c12ad02b684e48`, Markdown `8cdf16556427f88ae1c2d259c7c7804fad0dffc1835a7587ad3cdbf171bc86d8`.
