K/u6_active_cap supplies two static Lean candidates. The principal new result pays **both prime corrections of J's full original same-E17572 coefficient at every rough rank**, without assuming an active-modulus cap. A separate source file proves actual rank-sensitive physical caps, including the original piecewise L6 cap at rough rank at most two. The full original h6/L6 supplier and full adopted-policy PP licence remain OPEN. `local_step_complete=true`, `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`.

The principal file is `P5OriginalRetainedU6FullPrimeCorrections.lean`. Its final theorem strengthens J's actual sifted-count inequality to

    rawMain - delta * primeScale + signedPP - kappa * singularNormalization <= U6(actual E17572).

The raw main, full signed PP, whole pair-dependent policy, original mask, strict source and both correction definitions are J's literal objects. Neither L6, h248, an analytic raw-main endpoint, a PP estimate nor the desired count inequality is an input. For prescribed positive delta, kappa and epsilonMax, the theorem chooses one epsilon and one N0 before all N, eta>=0 and policies. The correction threshold itself precedes eta, epsilon and every policy. Policies may vary with N.

The substantive source and correction arguments are:

- `physical_prime_upper` proves that every prime of an actual full modulus q=b*k is below N^(59/250). The selected pair contributes the original larger-prime band bound; J's strict-small attachment theorem puts every divisor prime below N^(417/5000). This is a prime-factor restriction, not an assertion that q itself is below a power of N.
- `support_subset_sievePrimorial` derives divisibility by the actual `sieveProduct N N` from this restriction, J's proved squarefreeness and target coprimality. The primorial can have divisors much larger than N. The proof deliberately does not infer a modulus-size cap from primorial membership.
- `modulusPrimeCount_le_power` counts the actual available prime labels and gives `chenPrimeDivisorCount N q <= 2*N^(59/250)`. The existing proved logarithmic reciprocal-totient mass of the sieve primorial then gives `|modulusCorrection| <= 2*C*N^(59/250)*log N`, uniformly in the full policy. No rough-rank bound is used here.
- `centreCorrection_le_divisors` pools physical-modulus incidences over the genuine centre primes P|N. At an even N>=4, P=N is impossible and N-P is positive. The q-fibre is a subset of `(N-P).divisors`, irrespective of q's allowed support size. The existing proved tau subpower bound at exponent 1/2 gives `|centreCorrection| <= (D/log 2)*N^(1/2)*log N`.
- The existing power-log normalization theorem pays both full costs inside any kappa*H_N. The proof uses the upper bound for the signed correction only after proving the absolute bound. Consequently the subtraction sign in J's lower count is preserved.

This removes the complete prime-correction dependency on a full active-modulus cap. It does **not** remove the independent physical support/class requirements of the signed PP theorem. The primorial and divisor-incidence arguments cannot be used to infer those distribution licences.

`P5OriginalRetainedU6ActiveRankCap.lean` separately supplies the literal rank geometry. `factorPairs` is the existing active sign-sensitive small/rough convolution; it attaches beta-minus to a positive rough atom and beta-plus to a negative one. `sigma_at_factor` identifies its coefficient with J's unique physical scalar sigma. The short supports are images of restrictions of these active factors, never replacement policies or replacement lower weights.

For a rough factor r with j distinct prime factors, squarefreeness and the real upper prime cutoff give `r <= N^(a*j)`. Actual beta nonvanishing gives `s < N^(a*epsilon)`. The full modulus therefore satisfies

    b*s*r < N^(u+t+a*epsilon+a*j).

On the genuine strict source, `u+t <= 833/2500-eta`. With epsilon<1/8, this proves the individual original L6 cap for j<=2, the original global 153/256 cap for j<=3, and a subunit 15/16 cap for j<=7. The second and third caps are not identified with the possibly smaller individual nonenhanced L6 level.

The individual cap proof preserves the original root

    V = max(v(t),v(t+u),153/256-3*a/8)  if t<mu,
        v(t)                          otherwise.

It proves V>53/100 separately in these two branches. `original_residual_power` keeps the exact equality `N^(V-u-t)=N^V/(p1*p2)`. `active_rank_two_residual_cap` gives the actual divisor cap at this residual and retains the original alpha>=2. Above mu the residual is `57/64-(5/2)t-u`; no `1/2-t-u` Runbo factor is substituted. The rank file also gives an exact signed correction split and proves that every nonzero atom in its complement has at least eight rough primes. Its rank-limited correction consumer is superseded, for correction payment only, by the all-rank result in the principal file. The principal file imports J directly and does not depend on the rank file.

The manuscript comparison used the authoritative body SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, lines 630-686, 691-996 and 1000-1299, and `global-chen-lower-completion-20261010.txt:239-285`. The same 6091+11481=17572 half-open cells and their complement are inherited from J's exact mask identity. The manuscript's prime corrections, lower sign attachment, fixed physical root and alpha are retained. The historical saved whole L6 integer, discarded-floor payment, and 248/430 occurrence policy are untouched. The original c=49044063/25000000 and K=8452171/1250000 are unchanged.

J/h6's independent narrow SOURCE_REVIEW_PASS was read at its frozen source/registry/report pins. That review correctly left both full correction payment and the full PP cap/class open. This packet closes the former by an actual source argument, and only part of the latter's elementary cap geometry. No review or kernel credit is inherited. The Mertens inverse-interval bound is reused through the existing `P4BPrimorialDivisorEnvelope.exists_sievePrimorial_divisor_mass_le_log`; the proved divisor subpower estimate is reused through `Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow`. Neither theorem is an assumed internal h6 estimate. No new external hypothesis or axiom is introduced.

The exact remaining blockers are:

- Construct and identify the complete independently adopted mixed W/tent L6 causal policy, immutable history and positive marked-family h248 count induction. Uniformity over policy data is not its adoption proof.
- Prove full original physical/selected support and coefficient-class licences for the same signed PP coefficient, including all higher-rank atoms and the original endpoint/smoothing transfer. Full active modulus caps are no longer needed merely to pay these two prime corrections, but still matter to that independent distribution argument.
- Prove common causal approximation and identify J's entire raw physical density with the original saved L6 lower estimator. The buffered ordinary Runbo main remains a different object.
- Pay the raw-density boundary/tail loss from the strict retained source, and bind the actual same-mask saved-floor subtraction `savedL6-4*replacementSavedFloorPayment`. Positive count deletion alone does not preserve this saved endpoint. Negative U10/U11 parent accounting remains separately owned.
- Complete the prime-prefix PNT normalization of primeScale, the actual PP saving, endpoint reserve assembly, independent review, installation and compilation/kernel verification.

Only this K directory was written. Validation was static source/interface inspection, declaration/forbidden-token scanning and raw SHA256 metadata generation. No Lean compiler, lake/build, CI, finite decision execution, numerical certificate replay, bulk literal generation, Git operation, subagent or quota call was used. No original binary certificate was authenticated or evaluated. REGISTRY.json records actual source locations for the uninstalled J import and all direct imports, with inspected critical sources pinned separately.
