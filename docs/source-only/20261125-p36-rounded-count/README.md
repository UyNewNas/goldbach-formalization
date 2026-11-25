# Actual rounded-output U5 count insertion

**Source only. Not compiled, not kernel verified, and no formal acceptance
credit.** This packet adds one candidate module; it does not modify the
canonical source set or any running validation task.

## The precise new connection

`P2LowerFiniteCellBetaCompiler` already defines the actual finite-cell
rounded rough coefficient with its sign-sensitive small Rosser attachment
and proves its physical divisor-sum minorant. The old raw-policy U5 count
theorem does not automatically apply to this different output.

The candidate reuses that actual minorant, the original U5
`attachment_gates`, the existing arbitrary-coefficient quotient Fubini
identity, and the original ordered-pair U5 count dictionary. It derives
the finite count entrance for the rounded output directly. It never
identifies the rounded coefficient with a raw retained-policy coefficient.

For the original ordered pair `t` and quotient modulus `k`, write
`q = fullModulus t k`. The row estimator is the signed sum of
`rho_round(k) * (AP(N,q) - Centre(N,q))`. The candidate proves

\[
 E_t=M_t+D_t-C_t,\qquad \sum_{t\in\mathrm{pairSupport}(N)}E_t
 \le \mathrm{currentChenUpsilon5}(N),
\]

where the **same actual rounded rho** appears in all three terms:

- `M_t` uses the literal `finiteCoprimeMass (chenPrimePrefix N) 1 q / phi(q)`;
- `D_t` uses `finitePrimitiveDiscrepancy` at that full physical modulus;
- `C_t` is the signed, unchanged centre-prime correction.

The final theorem puts the sums of those three terms directly below the
original `currentChenUpsilon5 N`. Original pair labels and multiplicities
are preserved by summing the existing labelled source, without replacing
it by an unlabelled image of physical moduli.

The minorant theorem needs only `2 <= N` and `0 < epsilon < 1/8`.
Small-level and cutoff legality are derived from the old U5 supplier;
there is no final-count, raw/rounded-identity, density, admission or PP
hypothesis. The algebra is valid for any real `tau`; positivity of a mesh
and its geometric uses are separate obligations.

## Existing work reused and deduplication

The narrow search covered the fixed main and read-only donor's U5 count,
causal quotient, actual rounding/compiler, finite AP and primitive
discrepancy interfaces. No existing direct rounded-output U5 count entrance
was found. In particular, the ordinary Rosser count and raw causal count
have different displayed coefficients and do not license this output by
renaming it.

The new code does not reprove the lower tree, sign-sensitive attachment,
one-bound, quotient injectivity or the old Fubini theorem. It directly uses:

| Existing interface | Use |
| --- | --- |
| `P2LowerFiniteCellBetaCompiler.rho_minorant` | The actual rounded output's proved minorant |
| `P5OriginalU5CausalFinite.attachment_gates` | Actual U5 small-level and cutoff gates |
| `P5CausalRhoQuotientBridge.quotient_sum_physicalDivisorSum` | Exact arbitrary-coefficient Fubini on the literal quotient source |
| `chenSiftedQuotientPrimeSource_eq_coprime_filter` | The same sifted arithmetic source, including its target-coprimality mask |
| `currentChenUpsilon5_eq_siftedQuotientPrimeSource` | The original ordered pair count dictionary |
| `finitePrimitiveDiscrepancy` | The literal coprime mean and signed remainder definition |

The small-indicator conversion in the new caller uses the existing
`actualSmallPrimeProduct_coprime_natAbs_iff` and
`currentChen_actualSmallPrimeProduct_eq_sieveProduct` identities. No new
number-theoretic theorem is asserted there.

## Exact limits

This count connection does **not** prove that the exact mean has the
required numerical lower bound. In particular it is not
`fullProjectedMainSum` of a newly invented policy. The old rounded density
reserve still contains its explicit rounding loss and absolute beta term.

The exact coprime numerator has not been replaced by the total prime mass
or `li(N)`. Therefore no modulus-prime correction is silently removed;
such recentering and any subsequent payment remain separate if needed.
The signed centre term is also retained and is not estimated here.

The old finite-cell labels round the residual prime word for each outer
pair. They do not by themselves create Cartesian boxes for the entire
external-pair/residual word. This packet supplies no fixed whole-word
tensor identity, bounded-rank alphabet, physical modulus cap, common Q,
family admission, enhanced U5 density evaluation or signed PP bound.
It also supplies no PP result for the earlier literal `selectedPolicy`.

## Manuscript and source binding

The manuscript is
`chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`,
`paper/release-20261106/en/`. The finite minorant-to-count connection is the
finite arithmetic step following `sv:physical-lower` in the sieve
appendix. The coefficient appendix requires the same coefficient in the
count and exact coprime mean. The candidate only formalizes that finite
connection; the analytic consequence mentioned in the manuscript remains
unproved by this packet.

The immutable source index binds the main mathematical snapshot
`072863fe9c8cbef6c4dc1f5ce42cc5b7c18c6c8c`, read-only donor
`d6a9d76c56621992a8445c9628d4a2058db72eb6`, and both manuscript blobs.
The donor's two existing rounding/compiler source files were read, not
edited or copied to canonical paths.

## Static preflight

The candidate project closure has **146 modules**: **143 existing main
sources**, **2 existing donor sources**, and **1 new candidate**. It has
no missing project source, no import cycle and no additional explicit
external import over the current main manifest.

Four modules are outside the current selected main manifest: the new
candidate; the two existing donor rounding/compiler modules; and the
already-present main `UpperCoefficientPerturbation` source. That last
source is reused, not newly implemented. The preflight binds every actual
chosen source hash and does not grant object-cache reuse permission.

The source declaration list contains **10 explicit public declarations**:
two abbreviations, four definitions and four theorems. This is a text
inventory, not the later elaborated defining-module inventory.

During preparation, no Lean process, kernel replay, remote task, stage,
commit or board update was performed for this candidate. Subsequent
publication or validation must be recorded separately. Future integration still requires exact
dependency selection, fresh strict owned compilation, bundled kernel
replay, full declaration/type inventory and transitive-axiom checking.
