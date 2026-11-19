# P2.9 — H246 finite single-face wall sum

SOURCE_ONLY=true; COMPILED=false (UNCOMPILED); KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; INDEPENDENT_REVIEW=NOT_PERFORMED. New and inherited proof bodies and row matches are UNEVALUATED. This packet does not pay the two-face walls, complete marked-book wall, whole W2 collision licence, H247 endpoint or P2.9-wide acceptance.

## Baseline and input boundary

Continuation branch `chatgpt/p2-9-causal-successor-20261119-1640`, baseline `d2546838330c42ee9de44c39a18bd06880f39eec`, previous proof `c3fc719f402d26103978170a66f45566460a63e1`. The preceding report and complete Lean source were read together with `P2OriginalHalfOpenProfileCarrier.lean`; the predecessor supplies source-only candidate face uniqueness and a full same-Q pair atom bound, not a wall sum. Exact lower wall: x0=a0 for ordered lanes 0 and 2; x0=a0 or x1=a2 in lane 1; x0=a0 or x1=a1 in lane 3. The one-face estimates below apply also to any subset, enabling the later second-face-minus-first intersection partition without counting the intersection twice.

The historical `4ccc54e1423db03315957dc79138a89d4dab7efd` ledger records 29 original H247 upper comparisons unpaid at that snapshot. For zero-based index 50, s=101/50 the precise target is `(iterate designatedW1 designatedW2 247 true 50 : Real)/tableQ ≤ wuImprovementLimit true delta (101/50)`, with Q80 `1208925819614629174706176`, the fixed original `0<delta≤1/10`, and saved H184 numerator `36351464408527643182652`. Wu's printed 0.0223939 at 2.2 is a classical sufficiently-small-delta lower bound, below H184/Q80; it does not itself pay the target. A proof needs the actual signed cost, seed and same-source limit comparison, and the classical full box at `Q=N^(1/2−delta)` cannot be used without adaptation for enhanced Q or restricted descendants. The registry and selected functional source at `32d541884c85748e3fb18f7a83801b2f8b16e359` leave the 29 goals open. No endpoint is eliminated here; no assertion is made about uninspected later work.

The inherited manuscript pin matches the requested `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b:paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Its original common-Q and W2 lane geometry and signs are retained; no source version, c or K is changed.

## New candidate proof bodies

`P2Historical246WallFaceSum.lean`, SHA-256 `3b8d1fa7590a93ebcb3bf1a947948f225eb0ca615f985dd9db06b30737231fc9`:

* `face_reciprocal_sum_le_box` proves that, for any finite subset of one actual fixed normalized-coordinate face, projection to the other coordinate is injective and its image lies in the original N-deleted one-dimensional prime box. Consequently the reciprocal sum `sum 1/(p_other−1)` is at most the actual `actualPrimeBoxMass N (L/10) (3L/5)`. It does not identify two pair occurrences or impose prefix coprimality.
* `face_atom_sum_bound` combines this with the previous same-Q H246 atom bound. For N>1, d=`parentProduct old`>0, L>0, Q=d*N^L, and `4≤N^(L/10)`, every subset S of a single face has
  `|sum_{p∈S} oldPairAtom| ≤ |thetaAtom(N,Q,d)| * (80*floorBound(H246)/N^(L/10)) * actualPrimeBoxMass(N,L/10,3L/5)`.
  The factor 80 follows from the original `2/(p0−1) * 2/(p1−1) * 10*floorBound` and `1/(p_fixed−1)≤2/N^(L/10)`. No fresh/repeat distinction is discarded, and the empty face is included.
* `single_face_wall_atom_sum_bound` identifies the complete literal lower wall for k=0 or k=2 with x0=a0, retaining signed atoms. `successor_single_face_wall_uniform` uses the actual successor source, positive floor and existing fixed-box prime-mass limit to choose one threshold T before N, nu, marks, source tuples, row j and either k. It supplies `|wall sum|≤epsilon*thetaAtom(N,N^nu,d)` for each individual successor parent, in original BoxRows and nu≤1 scope. This is BEFORE any sum over marked parents and BEFORE original W2 `/5`; it is not a payment of the two-face lanes or complete marked Θ.

No Q80 `/4` or replacement payment is added. The two-face intersection, other prefix collisions, strict ceiling, true child count bridge and signed base/seed remain untouched. No endpoint is claimed paid.

## Inputs, validation, next action

No new outside analytic hypothesis. Existing source candidates `fixed_face_other_injective`, `full_pair_atom_bound`, fixed-box mass convergence, actual successor geometry and same-Q positivity are inherited, uncompiled and not kernel-verified here. Registry pins Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. No PNT/Mertens/BV/spectral proof is undertaken.

`lean --version` and `lake --version` each exit 127; raw logs included. Text search found no forbidden proof placeholders or native/unsafe tokens in the new source; it is not type checking. No kernel replay, axiom inspection, independent review, numerical producer/certificate replay, CI, Actions, pin change or resource increase occurred.

Next: elaborate this exact closure in the pinned environment, repair scoped errors, replay and inspect axioms, and independently review. Partition lanes 1 and 3 into first-face plus second-face-minus-first, invoke the subset theorem twice, keep their intersection once and combine the two errors. Then sum the four actual lane results and labelled marked source against the same Θ, applying original W2 `/5` exactly once. Separately prove the other collisions, strict ceiling, actual child count-to-profile bridge, signed base/seed, Gamma5 and unclosed Gamma9–15, reserve accounting and actual `BankEndpointLicences` calls. Overall P2.9 remains yellow.
