# Input boundary — P1.4 frozen upper rho0 versus rough-universe endpoints

Manuscript: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex, Git blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. Upper rho0 = 19/96, c = 49044063/25000000, K = 8452171/1250000. No repin.

Native rough universe: ImbalancedChen/RoughPrimeUniverse.lean has w≤p<z, p∤N, p prime, p<cap. w is the LOWER presieve boundary. z is the UPPER boundary. The frozen upper sieve's rho0=19/96 describes its upper cutoff; it cannot be silently assigned to the source-level lower w. A producer caller may choose parameters with different endpoints and requires actual code-level identification.

The Lean witness is intentionally exact, finite and input-free: N=2^24, w=3, cap=100, z≥26; six primes 3,5,7,11,13,17 are in the actual rough universe, d=255255<N and actual receiverTest N d>0 using prime P=16521961. The separate exact numerical comparison z=N^rho0>26 follows 26^4=456976<2^19=524288, but is NOT elaborated in Lean this packet. None of these lemmas asserts an original fifthExclusive stopped event or PLUS-Rosser admissibility. The prior literal-w zero lemma remains conditional on its *lower* w, not on z.

All original beta signs, stopped List occurrence multiplicity, full a*(p::selected).prod, strict/weak bounds, actualParent, same fixed parameters before N, saved87, frozen sharp-prime PP and two reserves remain untouched. New generic event fields or invented smallness premises are forbidden.

External signed sharp-prime PP: anchors eq:current-PP, lem:current-sharp-prime, eq:current-sharp-pi; original full squarefree N-coprime q≤N^theta at fixed theta<1, same signed rho and H_N normalization, smooth-singleton/endpoint restrictions. Registered from frozen manuscript only; REGISTERED_NOT_PROVED_NOT_CALLED. No external PNT/Mertens/BV/spectral proof added.

Lean leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958. SOURCE_ONLY, UNEVALUATED, UNCOMPILED. No kernel/axiom/independent evidence.