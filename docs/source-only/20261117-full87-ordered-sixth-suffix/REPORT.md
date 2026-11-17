# P1.4 actual combined history + sixth suffix ordering

Baseline confirmed commit: 0bc10f56c703b61646ad7ad38488977a35158b25.
Independent branch: chatgpt/p1-full87-ordered-sixth-suffix-20261117.
Candidate source commit: 74bd82ff746d74e8aa1eed746dca89deb71c4a80.
Source: P4AOriginalFull87OrderedSixthSuffix.lean, blob ca2807c76bf27819697abebf1f52b910e2110b02.

## New finite proof candidates

Earlier fifth/sixth suffix work only supplied membership in the rough universe. This packet proves the strictly stronger original ordered combined-history invariant by two finite inductions on the **unchanged** firstFifthEvents and fifthSixthWithoutBoth producers:

  selectedAfter.reverse ++ remainingAfter <+ pre.reverse ++ remaining

for first-fifth events, and the analogous eventSelected.reverse ++ eventSixthSuffix for fifth/sixth events, including actual sixthFromBoth, with original prefix, mass, sign and occurrence order. The common actual sharedRankFour state and existing FirstExitDepthFrontier sublist invariant place the combined list inside the genuine roughPrimeUniverse, which is strictly decreasing. It follows for every actual event that EVERY unprocessed p is smaller than EVERY selected r.

A separate arithmetic induction proves p^selected.length <= selected.prod. For any real fifth-exclusive event this applies to its genuine sixth candidates. At selected.length=5 this gives the new sixth rough product inequality:

  ((p::selected).prod)^5 <= (selected.prod)^6.

The final theorem explicitly retains the length-five condition; its derivation from the actual first-fifth producer is the next integration task, not an invented proof field.

## Quantitative meaning and obstruction

Let b5 denote the fifth selected product. The length-five bound implies b6 <= b5^(6/5). With the earlier conditional fifth odd-gate bound b5<N^(299/500), the best general result is b6<N^(897/1250)=N^0.7176 before a<N^epsilon. This is stronger than a naive upper cutoff p<z when z is large, but DOES NOT establish the necessary below-3/5 PP level or eliminate even-sixth high-q. The power argument alone can give a*b6<=N^(3/5) only with an additional fifth exponent <= (5/6)*(3/5-epsilon) = 1/2-5*epsilon/6 and proper strict endpoints. Nothing here proves that condition globally.

## Version and verification

Manuscript: UyNewNas/chen-imbalanced-semiprimes at 9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. Frozen upper section sets Theta=299/500; licensed PP local support is below 3/5.
Lean 4 v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native 09b97db5764ade1246bfb77206baa1b124760958. c=49044063/25000000, K=8452171/1250000 unchanged.
Previous REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and relevant complete Lean sources inspected; prior branch HEAD confirmed unchanged before creating task branch. AGENTS.md at root/docs/docs-source-only not found.

Actual environment checks: lean --version, lake --version, elan --version exit 127, command not found; pinned build dependency closure unavailable. Static prohibited-escape check negative. New source remotely read back with blob ca2807c76bf27819697abebf1f52b910e2110b02. SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no elaboration, kernel replay, axiom audit, actual 87-domain archive replay or independent validation. Potential elaboration errors remain. No CI, Codex, main/master edit, force-push, new external mathematical foundations or added resources.

## Remaining exact obligations

1. Derive selectedAfter.length=5 from the original actual event-source rank-four state, then integrate the fifth-power bound with original strict plus-beta high-q support to cut only genuinely small fifth products. Keep the remaining large tail in the identical signed physical rho.
2. Treat sixthFromBoth direct terminals and RAW eighth plus all early physical support at an actually licensed exponent; no even-rank odd-gate substitution.
3. Fixed epsilon and density/compiler reserves; same-rho signed PP exact coprime/endpoints/smooth singleton and centre-/modulus-prime corrections; ordinary residual integral, weighted actualParent loss, saved87 original archive, rank9, changed/tagged.
4. Pinned compilation, kernel replay, transitive axiom audit, independent review. P1.4 stays YELLOW.
