# P1.4 physical weighted failure — precise scope and external boundary

## Fixed sources

Manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, §4, upper first-exit identity and physical density `g_N(p)=1_{p>2,p∤N}/(p-1)`. Formal source exact finite `halfProductDensity` and existing `chenInitialBoundingSieve_prime_density`: `ImbalancedChen/ChenInitialPrimeSource.lean`. Existing failed-event recursion and correction sum: `docs/source-only/20261106-full87-failed-attempts/P4AOriginalFull87FailedAttempts.lean`. Frozen actual eighth carrier: `docs/source-only/20261106-full87-actual-eighth-carrier/P4AOriginalFull87ActualEighthCarrier.lean`. These two source-only imports are NOT accepted root modules as-is.

## Internal obligations, current status SOURCE_ONLY / UNEVALUATED

Physical continuation initialized at actual eighth state with `s.mass * ∏selectedPrefix halfProductDensity`, then each successful selected post-eight prime contributes exactly once; failure contributes `halfProductDensity(rejected)` exactly once; remaining smaller primes appear once in Euler product. The same ordered failed-event keys are produced by unit-weight recursion, retaining sign and occurrence multiplicity. The even-target and exact target-deleted carrier imply all these *post-eight* primes are >2 and do not divide N. We do NOT assert a full-root weighted frontier mass identity; source-root to eighth reweighting is an unproved internal bridge. All selected eighth primes' raw-prime membership/weight normalization across that bridge still require an audited proof.

Prior strict finite bound at rank≥11: `N<p^(261*3^(m+2)+1)`; the independent finite multiplier `targetDeletionFactor N p hi` is bounded once in predecessor `44731a0f9184b3ac7588f4ca1b3af815a45aa332`. This packet makes **no claim** that multiplying it onto an event is already justified. Rank-nine historical square failures and physical signed-saving/remaining integral/payment are still unproved.

## External input ledger — registered only, no new axiom

- Ordinary upper/lower Rosser density, manuscript §4 `eq:current-raw-density`: normalized same raw weight `V_N^+(R,y)/V_N(y)=F(log R/log y)+o(1)` (fixed s>1; lower f at s≥2). Reference/version/target uniformity and normalization: UNVERIFIED; NOT INVOKED HERE.
- Mertens/PNT, §4 `eq:current-mertens`: `V_N(N^u)=2 exp(-gamma) C_N / (u log N) (1+o(1))`, for fixed u>0 with claimed even-target uniformity. Independent source/precise hypotheses: UNVERIFIED; NOT INVOKED HERE.
- Signed prime-product progression, §3 `eq:current-PP`: weighted sum with **the same rho** in AP and exact coprime mean, claimed `O_{A,W}(N (log N)^(-A))` for original admissible families; source theorem/parameter ranges/normalization: UNVERIFIED; NOT INVOKED HERE.

The manuscript-internal common parameters, first-exit source identification, same-event signed transport, real g_N coefficient and all error/reserve accounting remain IN SCOPE. No PNT/Mertens/BV/spectral proof attempted.
