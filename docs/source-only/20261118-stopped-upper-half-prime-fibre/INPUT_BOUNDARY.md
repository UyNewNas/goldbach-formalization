# Input boundary — P1.4 stopped upper-half ORIGINAL prime fibre

## Frozen versions (unchanged)
- Manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
- Frozen constants c=49044063/25000000, K=8452171/1250000; manuscript upper rho0=19/96. No silent substitution of z=N^rho0 for the actual rough lower w.

## Internal proof obligations actually addressed
- Original additive prime carrier P with P<N, Prime P, Coprime P N.
- Exact full modulus q=a*(p::pre).prod=N-P, with original beta and original `largeFifthRosserIndices` support. For each P and actual (pre,p), q/b is the **only** possible index, conditional on q/b in original support and (q/b)*b=q.
- Strict X<q and 2P<N (equivalent to N<2q). Equality cases stay excluded from the upper band.
- `fifth.remainingAfter` remains an ordered List; actual signed sixth mass and repeated occurrence counts retained. The event generator remains the original receiverTest one, via preceding fixed-stopped source.
- This source-only result performs a finite signed reindex, not a prime asymptotic estimate or receiver/centre/primitive budget payment.

## External input REGISTERED_NOT_PROVED_NOT_CALLED
Frozen signed sharp-prime PP: `eq:current-PP`, `lem:current-sharp-prime`, `eq:current-sharp-pi` in the pinned manuscript; precise displayed form at lines 257–273 is a sum over the **same signed rho_N(q)** of prime-products in residue N modulo q minus X_W^(q)/phi(q), with an O_{A,W}(N log^{-A} N) error. Premises include a fixed finite smooth W_N on k labelled original primes >=cN^{a_*}, product O(N), fixed polylogarithmic mixed Euler derivatives, no additional arithmetic filter, one fixed policy/physical support and normalization.

The reindexed P sum has extra arithmetic restrictions (a quotient in an original Rosser support and exact divisibility, X<N-P, 2P<N). **No PP theorem is invoked here**; an actual manuscript-compliant weight and separate admissible full-modulus q range must be proved before any PP call. No replacement input structures, new axioms or unproved H_N smallness fields.

Other PNT/Mertens/BV/spectral foundations are not implemented. Ordinary asymptotic identification, actual source matching, error budget, reserve payment and numerical archive verification remain manuscript-side obligations.

## Evidence labels
- SOURCE_ONLY; UNEVALUATED; UNCOMPILED (Lean, Lake, Elan commands each 127).
- Exact randomized finite arithmetic diagnostic: 10,300 tested and zero mismatches, 2,475 nonzero left-hand sums. Not the Lean producer, not formal proof verification.
- Kernel replay, transitive axioms, independent review, saved87 numerical replay: NOT DONE.
- No CI, Codex, main/master changes or dependency changes.
