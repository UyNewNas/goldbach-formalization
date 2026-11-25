# Root review: original sharp Gamma5 source inverse

Exact source: `f5b78e0867db4aa6e6ba48147df45a25e0c41862`;
SHA256 `f31a222651df94ec41568e2a8cdc11dab226e1c3c66988b0830300b89a7030ab`.

Root read all 108 lines, the original logarithmic source API and the new
README/REGISTRY. Independent review separately checked all original
geometry and arithmetic hypotheses. The source retains:

- positive original prefix d and two fresh prime coordinates coprime to N;
- original lower a0 and strict upper a2 cutoffs;
- strict fresh pair order and inclusive bad-square inequality;
- inclusive complete-product cap, with positive real denominator;
- nondecreasing prime tail, including empty and repeated-prime tails;
- exact badLabels, roughNumbers and canonical primeFactorsList conclusions.

Existing tuple/window characterization, prime_divisor_floor and sorted
prime-factor uniqueness are reused. No target-coprimality condition is
added to the tail, no product injectivity is assumed, and no rank, mass,
J or PP estimate is an input.

This is **source-only, uncompiled, zero new formal credit**. It is a
pointwise reverse dictionary, not yet the marked finite-sum transport.
The old arithmetic dependency closure and conditional owner postimages
must still be selected and qualified coherently. No exact-owner or
standard-source match is promoted into an object receipt.
