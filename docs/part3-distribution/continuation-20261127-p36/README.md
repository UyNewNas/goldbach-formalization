# P3.6 continuation: rounded count and actual warm Rosser admission

**Accepted scope: three new modules, 43 complete declaration records.** All
passed strict compilation, independent kernel replay, full type and transitive
axiom inventory, and local verification of the recovered evidence archive.
The cumulative accepted P3.6 scope is now 38 owners and 770 unique declaration
records. The whole P3.6 node remains open.

Base commit: `525747fe88f8a6847c479bfe4a5bcc15aa13003a` on
`work/p3-6-warm-payment-20261126`. The 35 previously accepted defining modules
and their 727 declaration records are reused. This continuation does not
certify closure of the whole P3.6 node.

## Mathematical result

`ImbalancedChen.P3OriginalU5RoundedPrimeCorrection` proves the exact coprime
mean identity for the rounded coefficient at the **complete** modulus
`(p₁ * p₂) * k`. It includes the marked primes in the prime-divisor correction.
It bounds the sum of the signed prime-divisor and centre corrections by a
nonnegative cost charged only to nonzero rounded coefficients.

For each original pair, the nonzero quotient integers form a subset of
`[1, floor(X / (p₁ * p₂))]`. The accepted reciprocal-totient pair mass bound,
together with the existing elementary atom-cost estimate, gives

\[
  \operatorname{correctionCost}
  \le \frac{2H}{\log 2}N^{599/1000}\log N.
\]

Consequently, for every positive `eta`, the correction cost is at most
`eta * singularNormalization N` for all sufficiently large `N`, uniformly
in the later policy and rounding parameters whenever the same nonzero
coefficients obey the full-modulus cap. This is a sufficient sublinear
bound; it does not claim the manuscript's sharper separate correction
estimates.

`ImbalancedChen.P3OriginalU5RoundedCountReserve` uses the existing rounded
pair-density reserve to supply that cap, without a new cap hypothesis.
Its theorem `exists_original_U5_rounded_count_reserve` fixes
`mesh`, positive `kappa`, positive `eta` and positive `epsilonMax`, then
chooses `epsilon`, `tau0` and `N0` before every subsequent even `N ≥ N0`,
receiver `R`, bank and positive `tau ≤ tau0`.

For the exact policy `selectedPolicy R bank (1/1000) false N`, it proves

\[
\begin{aligned}
 \operatorname{fullProjectedMainSum}
 &- |\operatorname{chenPrimePrefix}(N)|
       \frac{\kappa\,\operatorname{singularSeries}(N)}{\log N}\\
 &+ \sum_{t\in\operatorname{pairSupport}(N)}
       \operatorname{rowSignedPrimitive}(t)
 -\eta\,\operatorname{singularNormalization}(N)
 \le \operatorname{currentChenUpsilon5}(N).
\end{aligned}
\]

The primitive term retains the **signed rounded coefficient of this same
output**. The theorem also returns its correction-cost bound and the
`N^(599/1000)` cap. Original pair labels and their multiplicities are
preserved. The prime-prefix factor in the density-loss term is explicit;
no prime-counting asymptotic is substituted silently.

`ImbalancedChen.P3OriginalU5WarmRosserAdmission` supplies the finite link
from the literal warm trace to the ordinary Rosser predicate. For every
accepted actual rough prefix `H`, its public candidate-free theorem derives
the complete ordinary lower-prefix admissibility at
`Q(H) = N^(incoming(H).cap)/(p₁*p₂)`, together with the strict cutoff bound.
It covers empty and terminal histories. Its second public theorem proves
the next-prime warm admission test equals the ordinary parity policy at
that same **incoming** level. The proof derives the concrete cap monotonicity
and divides out the external pair exactly once. The full three-frontier
retained-polynomial identity and its positive-density estimate remain to
be supplied. See `warm-admission/README.md` for the exact finite scope.

## Validation and provenance

All three final source files passed strict compilation on P1, with
`-t0 -j1 -DwarningAsError=true`, Lean `4.33.0-rc1`, and Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

| Owner | Strict compilation job | Exit | Complete declarations |
|---|---|---|---|
| `P3OriginalU5RoundedPrimeCorrection` | `job_a5d9344407cb44998e911a48f7b30483` | 0 | 17 |
| `P3OriginalU5RoundedCountReserve` | `job_5f4cc0a8fa2746c68cd2a23ba2c0d61b` | 0 | 1 |
| `P3OriginalU5WarmRosserAdmission` | `job_26da48e776ab43fd9929c382abc9fd61` | 0 | 25 |

`OWNED_SOURCE_PINS.json` and `warm-admission/OWNED_SOURCE_PINS.json`
bind these sources, their actual object files,
the generated audit, the unchanged original validator helpers and the
previously accepted kernel checker. `COMPILE_TERMINALS.json` and
`GUARD_REPAIR_EVIDENCE.json` retain compiler terminal metadata and the
correction object's checksum readback.

The isolated P1 overlay is
`/workspace/p36-rounded-correction-20261127`. Its dependencies reuse the
accepted warm source and objects in `/workspace/p36-original-u5-20261125`.
Preflight matched all 286 project source files and all 286 project object
files. The audit driver checks the actual overlay paths against those
same accepted object hashes before and after verification. No accepted
source or warm object is edited.

The first inventory attempt was cancelled after independent review found
that the initial driver checked original dependency paths without binding
the live overlay entries. It receives no acceptance credit. The amended
driver also pins the checker digest and writes a fresh run ID before
reading inputs. The two targeted regression checks failed before the
repair and pass afterward. `DRIVER_REVIEW.md` records the independent
disposition. A 24 GB reservation for
`job_de8997c7a8384311be4575b845a995f0` was rejected before execution by the
resource scheduler. Its dependent exporter rejected the incomplete report.
The final replay/inventory retry uses 16 GB and is
`job_5f9c0d1eb4cc49348095b29f16fcd481`. It succeeded with exit zero in
687.855 seconds, at a sampled peak of 6,851,584,000 bytes. The complete
inventory contains 17 declarations in the correction owner and one in the
count owner. Its transitive axiom union is exactly `propext`,
`Classical.choice`, `Quot.sound`.

`accepted-rounded/LOCAL_VERIFICATION.json` records the successful local
round-trip check. The 184,228-byte archive has SHA-256
`0b150578fedae5045f73490f680c4ec32816c3e16e8b93379eca1fb69fc771b0`.
The original audit stdout's entire final JSON equals the archived report;
the actual export payload and both current local source hashes also match.
The combined export/bridge task `job_e35dfe4561d14f04b908f7f3706d2030`
exported that complete archive, then exited with code 1 when the separate
warm/Rosser candidate failed its first compile. That candidate receives no
credit from this receipt. `OWNED_SCOPE_STATUS.json` keeps the accepted and
historical scopes explicit.

The final warm/Rosser candidate subsequently passed its entire combined
compile, kernel replay, full inventory and export task
`job_26da48e776ab43fd9929c382abc9fd61`, exit zero. Its 25-declaration audit
took 632.493 seconds, and its local recovered-evidence check also passed.
`warm-admission/accepted/LOCAL_VERIFICATION.json` binds the complete original
stdout, exact strict compile, source/object pins and archived report. Both
groups have the same three-element transitive axiom union. The final new
module sources contain no prohibited proof escapes.

P3 and the designated fallback returned MCP SSE 429 errors. These jobs
are P1 jobs; no P3 verification is claimed.

## Remaining whole-node boundary

The current count inequality is useful without assuming its raw main term
is positive or its signed primitive term is small. Closing P3.6 still
requires the actual fixed selected-policy positive main term, positive
mass for the sparse/query-specific families, physical common-`Q`
whole-word atomization and admission with complement payment, and the PP
estimate for the same rounded output. A full-modulus cap alone is not a
distribution licence. Native-coefficient admission theorems cannot simply
be applied to the rounded coefficient.

`NEXT_P36_BOUNDARY.json` states these remaining obligations precisely.
`SOURCE_REVIEW.md` reviews the two mathematical contracts, and
`MANUSCRIPT_SUPPLIER_AUDIT.md` records the pinned 1106 manuscript references
and the distinction between native-level fibres and fixed common levels.

The P3 closed-node PR and whole-P3.6 completion status must retain their
prior state until the missing suppliers are constructed and verified.
