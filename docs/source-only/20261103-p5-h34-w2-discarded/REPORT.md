# P5.6 / h34 — W2 endpoint/repeat deletion and strict fresh tuple supply

Date: 2026-11-03.
Base: `0c6bfd80f786c4d1e0d5499574008656dce5b2cc`.
Repository: `UyNewNas/goldbach-formalization`.
Intended branch: `chatgpt/p5-h34-w2-discarded-20261103`.

**PARTIAL_SOURCE_INCREMENT. Full h34 remains OPEN.**
Four Lean files: 957 lines, 38 theorem declarations and 37 definitions/abbreviations.
Scope: manuscript-internal proof generation; extra-manuscript inputs are
recorded in EXTERNAL_INPUTS.md, not implemented or silently marked verified.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`.
All new proof bodies and inherited finite checks are UNEVALUATED in Lean.
No Lean/Lake executable is on PATH. There was no compilation, kernel replay,
transitive axiom audit, independent reviewer, child agent, Codex/computer job,
CI dispatch, or numerical table replay. Commit requests `[skip ci]`.
Production files, earlier packets, P1.4 and P3.6 remain unchanged.

The governing manuscript was read at `paper/source/manuscript-body.tex:795-881`
in `UyNewNas/chen-imbalanced-semiprimes`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. It retains the same positive marked
family, true alpha, unchanged Q, three singleton and four good pair domains,
the separate switched bases, preceding generations, closed minima, row budget12
and one common 430+11 approximation. Nothing here replaces those requirements.

## Exact gap advanced

W1's d*N-masked half-open -> strict carrier correction was supplied in 0c6bfd8.
W2 is different: its original R16/S18 arithmetic rows are N-masked and retain
old-prefix repeated primes, in addition to the half-open lower endpoints.
Those rows are not equal to fresh strict physical children.

This packet supplies an EXACT disjoint finite decomposition and a quantitative
same-Q payment for the deleted endpoint/repeat part of all seven W2 feedback
occurrences. It then transfers the old selected bank estimate to strict fresh
TUPLE rows. It does not yet prove their complete equality with production
singleChildren/pairChildren, or with original selected count histories.

## 1. Elementary obstruction budget

`Part5OriginalH430PrimeObstructionBudget` uses primes p in [A,N], with A>0.
A coordinate is obstructed if p divides the old prefix d or its normalized
logarithm equals one of a0,a1,a2. The last three are the only possible lower
coordinate faces needed to cover the four W2 pair domains.

Each equality fibre has at most one prime by actual logarithmic injectivity.
The union therefore has cardinality at most omega(d)+3, and, for 0<d<=N,

    sum_bad 1/p <= (log N/log 2 + 3)/A.

The unrestricted other coordinate is bounded by the existing library theorem

    sum_pool 1/p <= 1+log N.

For arbitrary finite pair subfamilies whose first OR second coordinate is bad,
the reciprocal-product sum is at most twice the product of these two bounds.
Intersection fibres may be counted twice in this MAJORANT. They are not counted
twice in the exact decomposition below. No prime-distribution result is proved.

The explicit rate

    R_a(N) = (log N/log 2 + 3)(1+log N)/N^a

is a finite linear combination of the existing log^m(N)/N^a limits, m=0,1,2.
The proof only combines those supplied limits. The input boundary is recorded
separately; the backend is not expanded or replaced.

## 2. Original W2 carrier decomposition

`Part5OriginalH430W2DiscardedCarriers` starts with the exact original
`actualPrimeBoxTuples` and `singleHalf`/`pairHalf` tests. It defines:

- fresh strict interior;
- rejected lower endpoints (whether or not they also repeat an old prime);
- strict interior repeated-prefix terms.

`removed_partition` gives disjointness: endpoint/repeat intersections belong
only to the endpoint lane. `single_sum_split` and `pair_sum_split` preserve
EVERY signed test exactly before estimation. The profile's 401 closed query
atoms are retained; only the DOMAIN endpoint coordinates are removed and paid.
Query-knot values are never discarded by a measure-zero argument.

`fresh_iff_coprime` proves that on the original N-masked box the added Fresh
test is exactly coprimality with N*d. It does not introduce a selected mask.
`box_in_primePool` derives both p>=A and p<=N from the original box, L<=1 and
the stated lower floor. No unproved natural-prime truncation is supplied.

The exact atom identity is

    arithmeticRow(.inr j,b) = freshRow(j,b) + removedRow(j,b).

The fixed 4/5 and 1/5 point terms are unchanged. All three singleton and four
pair occurrences retain their labels and the SINGLE original factor 1/5.
The complete carrier itself is unchanged: fresh+removed reconstructs it.

## 3. Actual same-Q mass and coefficient payment

`Part5OriginalH430W2DiscardedMass` reuses thetaAtom_single/thetaAtom_pair with
localPrimeFactor d p and localPrimeFactor (d*p) q. On primes >=4 and the actual
original domains, the source proof gives

    theta(d*p)   <= 4 theta(d)/p,
    theta(d*p*q) <= 20 theta(d)/(p*q).

The pair denominator uses the original 1-u-v>=1/5 margin. It does not reset
alpha or replace a repeated singular factor with a fresh one.
Writing K_N=log N/log 2+3 and H_N=1+log N (local budget notation only), the
removed singleton atom is bounded by 4 theta(d) K_N/A, and each removed pair
atom by 40 theta(d) K_N H_N/A. These are raw, nonnegative arithmetic sums.
The seven-term row assembly gives the conservative per-atom bound

    removedRow_b <= 40 (K_N H_N/A) theta(d).

This constant40 is an ERROR majorant only, NOT a replacement row norm.
`freshRow_bounds` separately proves 0<=freshRow_b<=originalRow_b.

`rowGap` takes absolute values at every atom before applying the actual old
arrays. A symbolic finite envelope over g<430 bounds their atom L1 sizes;
no saved endpoint or 430-round interpreter is evaluated. Setting
A=N^(Lmin/10), `uniform_W2_rowGap` chooses one pre-N threshold and proves

    sum_b |originalRow_b-freshRow_b| |oldAtomValue_g,b| <= epsilon theta(d).

No division by theta(d), no old-table monotonicity assumption and no signed
cancellation are used. This is a local arithmetic-feedback comparison, not a
new H/h count-defect licence.

## 4. Selected frozen-root Member consumer

`Part5OriginalH430SelectedFreshW2Supply` calls the prior selected bank theorem
at epsilon/2 and the new deletion estimate at epsilon/2. The existing root
support provides d>0, d<=N, the common residual floor, L<=1 and Q=d*N^L.
There is no new caller-supplied mass/error hypothesis.

`uniform_selected_W2_freshTuples` supplies

    selected fresh coefficientwise error <= epsilon selectedTheta,
    every fresh coefficient >= 0,
    sum_atom fresh row <= 12 selectedTheta,
    selectedTheta=0 -> error=0 and every fresh coefficient=0.

The exact row norm12 is preserved because the deletion is nonnegative.
`uniform_selected_outer_W2_freshTuples` aggregates only selected W2 slots,
after per-cell estimation. Each root cell retains its own Q.
Generation maps g and nonnegative marks sigma remain explicit until they are
constructed from the COMPLETE original selected count history.

## Remaining MANUSCRIPT-INTERNAL obligations

1. Identify the fresh tuple interiors with the actual production
   singleChildren/pairChildren, including unchanged query profiles, pair order,
   physical ceiling/product gates and full/selected inherited filters. The
   exact Fresh/coprimality equivalence is not that full reindexing theorem.
2. Construct the full original U3/U4 selected-count family, its g/sigma/owner
   assignments and multiplicities, rather than accepting arbitrary Member
   subfamilies as the original source.
3. Supply all bank literal weight/point/floor/candidate-to-profile and
   ordinary/fixed/switched base connections and the analytic seed application.
4. Supply native-history proper/equality/inherit mass control, native outer
   integral/Theta/count correspondence and ONE nested 430+11 causal refinement.
5. Complete manuscript-local instantiations of external analytic inputs. Do not
   reclassify the manuscript's own same-rho/positive-product assembly as an
   external theorem to remove an internal gap.
6. Stage the unchanged held closure, compile, kernel-replay and inspect axioms.

The extra-manuscript proofs themselves are out of scope and remain recorded
inputs. No new Lean axiom or target-equivalent licence record is introduced.
This packet does not assert the eventual U3+U4 bound or hLower.
Original c, K, root norm7/2, row norm12 and depth440/441 are unchanged.

## Validation and staging

The source modules should be staged in this order under ImbalancedChen:
PrimeObstructionBudget, W2DiscardedCarriers, W2DiscardedMass,
SelectedFreshW2Supply (each with Part5OriginalH430 prefix).
Copying these files alone is not a complete import installation.
Use the unchanged toolchain/dependency pins; do not upgrade them for this task.

Static delimiter/token/whitespace and additive-patch checks only check text.
They are NOT parsing, elaboration, proof checking or an independent review.
Exact raw-byte SHA256/Git hashes and reused dependency pins are in REGISTRY.json.
No new green node or formal credit is claimed.

Suggested narrow source-only status delta:

    蓝｜W2七项N-window的strict fresh／端点／内部repeat精确拆分与原1/5系数保持
    蓝｜W2端点/repeat同Q显式付款、430代共同阈值及selected fresh元组12Theta供应
    黄｜严格fresh元组到生产子载体、完整原计数历史/过滤与共同441实现

The publication commit identifies these exact sources; full h34 remains yellow.
