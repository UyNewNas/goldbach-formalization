# Historical singleton: exact medium residual

**SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.**

Publication directory:
`docs/source-only/20261126/p1-historical-exact-medium-residual/`

This packet reduces the original historical singleton distribution terms to
their **literal original medium sum**. It supplies an arbitrary-logarithmic
Atlas-trim bridge, combines the existing trim/proper-power/one-long interfaces
with the reviewed remaining-Type-I payment, and preserves the two original
physical-count receivers and their selection schedule. The medium sum itself
is still unestimated.

## Frozen files

The SHA-256 values below bind the exact bytes reviewed and prepared for
publication. This README is additional documentation; the four files below
are unchanged.

| File | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `P1OriginalSingletonAtlasTrimLogAccuracy.lean` | 91 | 4270 | `55b1e5fda52d2d7aa2f4fd74e12611dce202192da4d8f31b95cb8916862477e9` |
| `P1OriginalHistoricalExactMediumResidual.lean` | 315 | 16801 | `c531ae6657bde3c42928a29e8fe3aeac22b0fdd3cfef385812fa5f5d3eed2195` |
| `implementation_notes.txt` | — | 7189 | `c1b9ce62dc18e5fa5961ea93a88d1142be775af17430bc95177380a961739f77` |
| `INDEPENDENT_EXACT_MEDIUM_REVIEW.json` | — | 5756 | `69822d733dc8b3bdb2c2ffdd7c4321ba7155751af6e3b346ff8eb86dfb80cdfd` |

The independent review found no concrete mathematical or Lean static blocker
in these two drafts. That result is a source review, not an elaboration,
normal-build receipt, kernel audit or full-owned acceptance.

## Exact object retained

`mediumAtlasSum kap zeta K N Q c` is exactly the sum over
`js ∈ chartBank (2*N) 1` of

```lean
mediumAtlas (actualLicence kap 6 N) K (2*N) N kap
  (originalMediumLow zeta js) (originalMediumHigh zeta js)
  Q (fun q => (c q : ℂ)) js
```

`historyMedium B kap zeta K old fresh N cap w z L` specializes this object
to the original `historicalModuli B old fresh N cap w z` and
`trueDDeltaRho old fresh N cap w z L`. It preserves the original physical
target `N`, source cap `2*N`, collar order `6`, pre-HB order `K`, complete
product, signed coefficient, moving residue and exact coprime mean.

The smoothing parameter is the same `kap` in both `actualLicence` and the
complete-product eta. In every application of the new remaining-Type-I
theorem, **`kap0 = kap`**.

## Exported conclusions

The following are statements supplied by the proof-source drafts. Their
imported source proofs and their own elaboration remain to be accepted.

| Declaration | Conclusion and scope |
|---|---|
| `eventually_original_singleton_atlas_trim_logAccuracy` | For fixed `0 < kap0 < 1`, natural accuracy `A` and `eps > 0`, the original trim norm is at most `eps*N/log(N)^A`, uniformly after the threshold in `kap`, collar order `B`, `Q ⊆ Icc 1 N` and real `rho` with `|rho| ≤ 1`. |
| `historyDistribution_sub_medium_eq_remaining` | Exact signed identity: `historyDistribution - historyMedium` is the reviewed historical remaining-Type-I `sourceChannel`, with `kap0 = kap`. |
| `eventually_historyDistribution_sub_medium_logAccuracy` | Under the displayed remaining-geometry gate, this difference has norm at most `N/log(N)^A`. |
| `eventually_historyRemainder_sub_medium_logAccuracy` | With `0 < kap < 1`, the original `+trim`, remaining-Type-I and `-properPower` terms are paid, giving the same arbitrary-logarithmic rate. |
| `eventually_policyRemaining_sub_medium_logAccuracy` | With `1 ≤ K`, also applies the original one-long remainder theorem to the original smoothed signed discrepancy `policyRemaining`. |
| `exists_original_count_medium_residuals` | Both actual physical receivers differ from their own literal `historyMedium` by at most `u*singularNormalization N`, with the original omissions and history-selection schedule. |

For fixed admissible `kap`, `zeta`, `K`, geometric `kappa` and requested
accuracy, the historical log-accuracy thresholds precede the historical
cutoff `B`, both old/fresh policy functions, and `cap,w,z,L`. Thus the
original policies that depend on `N` may be instantiated after that
threshold. These conclusions assume no desired medium, row, mass, signed-PP
or target-error estimate.

## The same-kap application gate is a real restriction

The new remaining-Type-I result requires

```text
0 < kappa
kappa ≤ zeta / 10000
zeta ≤ 1 / 20000
kap < kappa / (4 * (1 + kappa))
```

The trim, policy and count conclusions additionally retain the positive
smoothing conditions stated in their declarations. The older kernel and
count interfaces allow every fixed `0 < kap < 1`; they do **not** imply this
extra geometry gate for an arbitrary already-fixed `kap`.

`exists_small_original_smoothing` provides a compatible free choice. For
`zeta > 0`, set

```text
kappa = zeta / 20000
kap   = kappa / (8 * (1 + kappa))
```

It proves `0 < kap < 1`, `kappa ≤ zeta/10000` and the required strict gate.
To apply the historical results, retain the original `zeta ≤ 1/20000`
ceiling as well. The choice can be fixed once before histories and `N`:
the old `exists_original_kernel_receivers` and
`exists_original_count_distributions` place their universal smoothing
choice after the universal cutoff `B` and before the subsequent selection
schedule. No parameter is changed during an identity or comparison, and no
unrestricted closure of the older forall-`kap` statements is claimed.

## Existing budgets and accuracy accounting

The trim bridge calls the existing public
`original_singleton_trimReserve_eq_prefix`,
`exists_prefix_primitive_budget`, `eventually_originalLowerCut_lt` and
`eventually_powerLog_le_logAccuracy`. It keeps the original discarded weight
`(1-eta)*smoothNatural`. The strict cut is below `N` before the prefix budget
is applied. At divisor exponent `kap0/2`, the three terms are

```text
3*C*N^(1-kap0/2)
12*N^(1-kap0)
12*N^(1-kap0)*log N
```

Each receives the old scalar rate with tolerance `eps/3`. The original
divisor, zero-difference, prefix reindexing and power-log proofs are reused.

The exact remainder identity is

```text
historyRemainder - historyMedium
  = trim + remainingTypeI - sum(properPower)
```

The three terms are used at accuracy `A+1`; the existing generic
`eventually_inverse_log` absorbs their fixed factor `3`. The policy theorem
combines the old one-long and new remainder residuals at `A+1` and absorbs
factor `2` by the same supplier.

Proper powers use the original public
`P1OriginalSingletonAtlasProperPower.eventually_original_singleton_atlas_properPower_logAccuracy`.
The natural order is passed as a real exponent and converted with
`Real.rpow_natCast`. Its strict modulus range and unit coefficient bounds
are obtained from the original historical support and unit-bound theorem.

## Actual counts and omission schedule

The actual-count result keeps the rate **`u*singularNormalization N`**.
It does not assert an arbitrary `N/log(N)^A` rate for the physical counts.
Its proof calls the old count-distribution interface at tolerance `u/2`,
then uses the new distribution-minus-medium bound at accuracy `3` and the
old log-cube-to-singular-normalization comparison at tolerance `u/2`.

Both policy orders are unchanged:

- comparison receiver: `(S false, R false)`;
- gain receiver: `(eight false, six false)`.

The same returned `s,r,E`, bound `E ≤ 11/64000`, three omission budgets,
`FilteredSourceSupply`, and `e/q0/q/a/n0/n/m0/m` selection order are kept.
The eventual physical threshold still precedes `Even N` and the original
`cap,w,z,ell` constraints, with `L = N^ell`.

## Open boundaries

- **Literal medium remains unestimated.** This packet identifies it as the
  remaining term; it supplies no bound on `mediumAtlas` or `historyMedium`.
- **Proper-power P3 acceptance remains HOLD.** Calling its existing public
  theorem does not create a P3 normal, kernel or full-owned receipt.
- **The original FixedM source bytes have not been restored.** Existing
  missing-source, Fourier owner, provider postimage and unique-owner import
  obligations remain in force.
- **No Lean acceptance or complete P1.5 result is claimed.** These are
  source-only proof drafts with an independent static review.
