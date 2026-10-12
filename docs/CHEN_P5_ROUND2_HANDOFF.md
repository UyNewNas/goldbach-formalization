# Part 5 round 2: verified independent inputs and remaining mean obligations

## Fixed checkpoints and scope

| Item | Complete SHA |
| --- | --- |
| Unchanged common proof baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| First-round proof source | `3857bfe99b6a7adbb0c3c0443b27b99d96a44f86` |
| First-round handoff | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` |
| Immediate verified Buchstab delivery to P2 | `db97d0fe03250f4d9a8aea34b23e9c20f67010b8` |
| Verified complete finite ledger and scale checkpoint | `bd83a110ee52626daf9e68535c007eb73a93daca` |
| P0 first Buchstab acceptance inspected | `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` |
| P0 verified first-cell and Buchstab-bridge acceptance inspected | `c9f407efe66240c08c2e8a678330ba7b98b74db5` |
| P0 separate uncompiled LongSlot repair inspected | `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` |
| P1 fixed source-candidate handoff inspected | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |
| P2 source inspected | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| P3 second-round source inspected | `7d70a2545fd819706e473eb41e4d430ad19119d8` |
| P4 latest handoff inspected | `c942b4c51d9d0005f0bd566906a3f0c88eeb1dba` |
| Frozen manuscript | `ba6ec11d800eccc54406490631895e174de85766` |

The source branch remains `chatgpt/chen-p5-lower`. The user has not
supplied a replacement common proof baseline. Reading later Part 0
acceptance records does not change the baseline of this branch.

**Validation status:** Buchstab, the complete finite eleven-term ledger,
the lower-scale module, and the actual InitialSource component have each
passed strict compilation, bundled kernel replay and the transitive axiom
audit. Buchstab and the finite ledger/scale were already published at the
separate checkpoints above. The separate first-row eventual mean remains
a source candidate whose additional supplier closure has not been
validated. The complete adopted-mask mean and final `hLower` remain open.

## 1. Immediate P2 delivery: complete actual Buchstab tail

The complete compiler-confirmed type at the published Buchstab SHA is:

```lean
ImbalancedChen.currentChen_buchstab_eleven_twentieths :
  ∀ {s : ℝ}, 7 / 3 ≤ s →
    11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

The proof covers the whole base window `[7/3,10/3]`, then the whole
unbounded tail by the actual weighted delay integral. It uses the
logarithmic formula on `[7/3,3]` and the existing global `1/2` lower
bound on `[3,10/3]`. No sampled values, new Buchstab function or
unproved monotonicity is involved.

The only source repair was the real strict-compiler sequencing
diagnostic: `field_simp [hxp.ne'] <;> ring` became the same two
sequential tactics. The corrected source SHA256 is
`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`.

| Actual check | Result |
| --- | --- |
| Official frontend through stock Lake, `trustLevel=0`, warnings as errors | Exit 0; reused P0's source-identical target compile |
| Original bundled `leanchecker --verbose` | Exit 0; target declarations replayed against their imports |
| Defining-module inventory and transitive axiom audit | Exit 0; all 5 declarations, including the private helper |
| Axiom set for each declaration | `propext`, `Classical.choice`, `Quot.sound` only |

The [small handoff](CHEN_P5_BUCHSTAB_HANDOFF.md),
[full receipt](../verification/parts/p5/round2/buchstab/receipt.json), and
[compiler types](../verification/parts/p5/round2/buchstab/compiler-types.txt)
are part of the published commit. P0's later fixed acceptance records
the identical source/object hashes and imports this component into its
own aggregate root. P0 explicitly leaves its full-root verification and
both main asymptotic suppliers open.

## 2. Complete eleven-term finite component

The full support and requirement ledger remains
[CHEN_P5_MEAN_LEDGER.md](CHEN_P5_MEAN_LEDGER.md). The definitions keep the
literal additive-prime carrier `chenAdditivePrimeCarrier N`, the natural
receiver `N-p`, all tuple labels and their multiplicities, and the actual
sifted quotient sources. They do not replace tuple counts by an indicator.

With `A=N^(417/5000)`, `H=N^(19/125)`, `D=N^(59/250)`, `C=N^(1/3)`,
the signed vector is exactly

```text
(3, 1, -1, -1, 1, 1, -2, -1, -1, -1, -1).
```

The two masked rows retain the complement of the same predicate:
row 6 uses `¬ E (p1,p2)`; row 11 uses `¬ E (p3,p4)` for the fully
labelled increasing four-prefix. Its fourth prime ranges over `[H,D)`.
No contraction of the negative endpoint or extra product triangle is
inserted into the current rectangular sixth row. The older contracted
Wu weight would require the strict retained product condition and the
same complementary non-strict deleted condition in both paired rows.

The principal complete type below is confirmed by successful compilation
and the actual environment audit. The full elaborator-printed inventory,
including generated and private declarations, is in
[compiler-types.txt](../verification/parts/p5/round2/finite/compiler-types.txt):

```lean
theorem currentChenPairedPrimeSum_eq_upsilon (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E =
      3 * currentChenUpsilon1 N + currentChenUpsilon2 N - currentChenUpsilon3 N -
        currentChenUpsilon4 N + currentChenUpsilon5 N + currentChenUpsilon6 N E -
        2 * currentChenUpsilon7 N - currentChenUpsilon8 N - currentChenUpsilon9 N -
        currentChenUpsilon10 N - currentChenUpsilon11 N E
```

The joint last-row interface remains one upper bound on the real sum,
with no invented individual numerical endpoints:

```lean
theorem currentChenPairedPrimeSum_ge_of_joint_last_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : ℝ)
    (h₁ : l₁ ≤ currentChenUpsilon1 N)
    (h₂ : l₂ ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ u₃)
    (h₄ : currentChenUpsilon4 N ≤ u₄)
    (h₅ : l₅ ≤ currentChenUpsilon5 N)
    (h₆ : l₆ ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ u₇)
    (h₈ : currentChenUpsilon8 N ≤ u₈)
    (h₉ : currentChenUpsilon9 N ≤ u₉)
    (h₁₀₁₁ : currentChenUpsilon10 N + currentChenUpsilon11 N E ≤ u₁₀₁₁) :
    3 * l₁ + l₂ - u₃ - u₄ + l₅ + l₆ - 2 * u₇ - u₈ - u₉ - u₁₀₁₁ ≤
      currentChenPairedPrimeSum N E
```

The normalized variant pays `2*delta*singularNormalization N` for
the joint last two rows. With the first nine rows this totals
`14*delta*singularNormalization N`, exactly the absolute coefficient sum.
Positive rows 1, 2, 5, 6 require lower estimates; negative rows 3, 4,
7, 8, 9, 10, 11 require upper estimates. The coefficient of row 7 is -2.

## 3. The factor-four conversion

For `W_N=currentChenPairedPrimeSum N (E N)` and
`H_N=singularNormalization N`, the unchanged count bridge is

\[
W_N\le4D_{1,2}(N)+246\frac{N}{N^{417/5000}-1}+4.
\]

Consequently the required weight coefficient is

\[
4c=\frac{49044063}{6250000}=7.84705008,
\qquad c=\frac{49044063}{25000000}.
\]

Both exception costs are divided by four: `246/4=123/2`, and the
unit-receiver contribution `4/4` is exactly one. The existing normalized
count-error theorem is uniform in the selector, so it applies to the
actual `N`-dependent adopted mask.

The existing finite-budget declaration now has its complete type confirmed
by successful compilation and the environment audit:

```lean
theorem currentChen_lower_scale_of_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon etaMean etaCount : ℝ}
    (hbudget : etaMean + etaCount ≤ 4 * epsilon)
    (hweight : (4 * currentC - etaMean) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E -
      etaCount * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```

Once the actual row suppliers exist, `delta=epsilon/7` loses `2*epsilon`
on the weight mean; another `2*epsilon` pays the uniform count error.
Their sum is `4*epsilon`, giving the desired `epsilon` after division.
This round does not add another theorem assuming the missing complete
eventual mean. The finite inequalities above remain finite algebra.

## 4. Actual first-row source components and a separate mean candidate

[CurrentChenInitialSource.lean](../ImbalancedChen/CurrentChenInitialSource.lean)
separates the actual source comparison, singular-series identification,
exact sieve coefficient and prime-factor error absorption into five
independent declarations. Their short closure uses the already proved
prime-factor product bound directly, followed by the usual logarithm
inequality; it does not depend on P1's history/grid modules or the full
beta lower-sieve supplier. Their public types are unchanged by the split.

The following types are compiler-confirmed in namespace
`ImbalancedChen`, with the declared upstream `LiLiuOnePlusOneNine` and
`GoldbachBig` contexts. The complete defining-module inventory is in
[InitialSource compiler-types.txt](../verification/parts/p5/round2/initial-source/compiler-types.txt).
The separate eventual mean below remains explicitly source-only:

```lean
theorem currentChen_goldbachS1_le_sifted_add_primeFactors
    (N : ℕ) (tau A z : ℝ) (hN : N ≠ 0) (htau : 0 ≤ tau) (hAz : A ≤ z) :
    (goldbachS1 (goldbachDifferenceCarrier N tau) N z : ℝ) ≤
      ((chenSiftedPrimeSource N A).card : ℝ) + (N.primeFactors.card : ℝ)

theorem eventually_currentChen_primeFactors_negligible
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N.primeFactors.card : ℝ) ≤ epsilon * singularNormalization N
```

The other three compiler-confirmed statements identify the actual
singular series for every natural N and evaluate the actual coefficient:

```lean
theorem currentChen_twinPrimeConstant_eq_liuUniversalProduct :
    twinPrimeConstant = MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct

theorem currentChen_singularSeries_eq_liuSingularSeries (N : ℕ) :
    singularSeries N = MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N

theorem currentChen_initial_sieve_coefficient :
    (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
        dimensionOneLowerLinearSieveFactor 4 =
      (33 / 4 : ℝ) * Real.log 3
```

[CurrentChenInitialMean.lean](../ImbalancedChen/CurrentChenInitialMean.lean)
imports those declarations and retains the candidate proof of the
following complete source declaration:

```lean
theorem eventually_currentChenUpsilon1_ge_initial_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      ((33 / 4 : ℝ) * Real.log 3 - epsilon) * singularNormalization N ≤
        currentChenUpsilon1 N
```

This is a nonzero mean bound for the actual first row, with no policy,
distribution, integral, common-K or whole-mean hypothesis. Its proof
uses the pinned `goldbachS1_beta_fixed_normalized_lower` at `s=4` and
cutoff `N^(4/33)`. Since `417/5000<4/33`, the sieve cutoff comparison
has the lower-bound direction required for the current first row.

The source identification is proved, rather than assumed. Both actual
singular series have the same convergent odd-prime product and the same
finite divisor correction; no extra factor two is inserted. The upstream
sieve ignores prime divisors of N, so the noncoprime receiver part is
deleted using the proved `goldbachBadCount_le_primeFactors`. Its cost is
paid by taking logarithms of the already proved prime-factor product
bound and applying the existing power-log absorption. The actual
lower-sieve factor at four has an integral over
`3..3`, giving the exact coefficient `(33/4)*log 3`.

This ordinary coefficient is not identified with the adopted numerical
`L1` endpoint. It does not close the other ten rows. Its candidate or
verified status is determined by the actual recorded execution, not by
the fact that the proof body has no displayed analytic hypotheses.

The required ordinary beta supplier has an existing proof in the pinned
dependency source. Its complete **source-extracted, not compiler-confirmed**
type, in namespace
`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig`, is:

```lean
theorem goldbachS1_beta_fixed_normalized_lower
    (s δ : ℝ) (hs4 : 4 ≤ s) (hslt : s < (33 / 8 : ℝ)) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε) *
              dimensionOneLowerLinearSieveFactor s - δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ))
```

The source is fixed at goldbach dependency SHA
`09b97db5764ade1246bfb77206baa1b124760958`, with file SHA256
`2d6935310615d6626bedee37700cdc935a198dea7e9b15d69d11c6b580887821`.
The candidate instantiates `s=4`, `δ=epsilon/4`, and
`tau=min (1/2) (epsilon/(4*((33/4)*log 3)))`. The source truncation
cost is at most `epsilon/4`; the supplier error is `epsilon/4`;
the actual noncoprime-source correction is paid by `epsilon/2`.
Their total is exactly the displayed first-row error budget.

Its missing compiled closure is a validation backlog,
not a new analytic assumption in the displayed first-row declaration.
The long independent supplier queue was stopped through its original
tool session when shared memory approached the actual 8 GiB limit, so
the finite P5 and short InitialSource checks could proceed. Its first
Bombieri--Vinogradov node completed normally. The later S1Carrier attempt
was interrupted before a completed frontend record or object existed;
the tool session returned 130, which is not a Lean proof-failure verdict.
The interruption receipt preserves that distinction. No unchanged
supplier proof was patched and no full-queue retry was launched.

## 5. P2 alignment and the missing local comparison

The original P2 checkpoint `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e`
includes all 17,572 raw rows and a generic
`PairedIntegralCertificate.sum_check_sound`. P0's later fixed acceptance
`c9f407efe66240c08c2e8a678330ba7b98b74db5` repairs and verifies the five
P2 first-cell modules (182 actual defining-module declarations), followed
by the two-declaration `CurrentPairedBuchstabBridge`. Each production
module has strict trust-zero compilation, original bundled replay and
a full defining-module axiom audit. This is a newly received successful
first-cell result; it does not promote the original unmodified P2 branch
or the complete adopted table to verified status.

The accepted cell is row 0, E0, t-index 422 and u-index 510. It cannot
stand in for E0's 6,091 plus E1's 11,481 cells. The fixed receipt and
compiler-output inspection is recorded in
[upstream/receipt.json](../verification/parts/p5/round2/upstream/receipt.json).
Those are P0's actual executions, not additional P5 recompilations.

The coordinate dictionary is:

| Actual labelled object | P2 coordinates |
| --- | --- |
| Sixth-row pair `(p1,p2)` | `(t,u)=(log_N p2,log_N p1)` |
| Eleventh-row prefix `(p1,p2,p3,p4)` | `(t,u,z,w)=(log_N p4,log_N p3,log_N p2,log_N p1)` |
| Both outer mask tests | The same `(t,u)` rectangle; row 11 tests `E_N(p3,p4)` |
| Buchstab argument | `(1-t-u-z-w)/z`, required to be at least `7/3` |

The P2 integral already contains `K/80=K*(1/20)*(1/4)`. A gain `g`
in those Chen-quarter units contributes `4*g` to the weight coefficient.
Neither another quarter factor nor the replaced old `12/5` increment
is added. The withdrawn `1.9728` branch is not used.

The full-mask Lean checks and exact rational sum are still needed.
The complete generic aggregation type below is now **compiler-confirmed
at P0's repaired acceptance SHA**, in namespace
`ImbalancedChen.Certificates`; the original P2 source alone did not
provide that execution evidence:

```lean
theorem PairedIntegralCertificate.sum_check_sound {ι : Type*}
    (s : Finset ι) (c : ι → PairedIntegralCertificate)
    (hchecks : ∀ i ∈ s, (c i).check = true) :
    ((∑ i ∈ s, (c i).lower : ℚ) : ℝ) ≤
        ∑ i ∈ s, pairedLocalIntegral ((c i).K : ℝ)
          (c i).a (c i).tl (c i).tr (c i).ul (c i).ur (c i).Z ∧
      (∑ i ∈ s, pairedLocalIntegral ((c i).K : ℝ)
          (c i).a (c i).tl (c i).tr (c i).ul (c i).ur (c i).Z) ≤
        ((∑ i ∈ s, (c i).upper : ℚ) : ℝ)
```

The still-missing `hchecks` must cover the actual complete adopted
index set and its actual records, with the common K and coordinate
dictionary, not an arbitrary checked subset. The finite sum additionally
needs the actual ownership/disjointness identification with the adopted
union integral.

The new bridge composes the accepted actual first-fibre support with
P5's global Buchstab result. Its two complete compiler-confirmed types,
in namespace `ImbalancedChen.Certificates.PairedV2`, are:

```lean
theorem first_fibre_buchstab_eleven_twentieths {t u z w : ℝ}
    (hs : firstFibreSupport t u z w) :
    (11 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z)

theorem first_fibre_buchstab_gain {t u z w : ℝ}
    (hs : firstFibreSupport t u z w) :
    (1 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2
```

The same acceptance confirms:

```lean
theorem ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤
      ImbalancedChen.Certificates.PairedV2.firstIntegral ∧
    ImbalancedChen.Certificates.PairedV2.firstIntegral ≤
      (31704 / 1000000000000 : ℝ)
```

This is the independently weaker rational enclosure, not the stored
tighter Q160 interval. The bridge has real variables `t,u,z,w` and
`firstFibreSupport` as its input; it has no natural target, adopted
arithmetic mask, prime tuple, U6 or U11 parameter. Its successful
composition is therefore received at precisely this continuous first-cell
scope. The bridge receipt explicitly leaves the entire adopted mask
and actual arithmetic parent as separate inputs.

The actual adopted negative parent must also be constructed and proved
to dominate the retained local fibre under the appropriate priority,
square, prime-ceiling and physical-level gates. P2 does not yet define
that fully adopted parent. The new Buchstab theorem supplies its lower
barrier input; it does not prove this distinct upper-parent comparison.

The saved Q80 floor is a saved lower-policy contribution. It is not an
upper bound for the deleted actual sixth-row count. A valid retained
sixth-row lower estimate must come from the actual restricted family
and its policy/integral/distribution proof. The same mask and parent
ownership must be used for the retained eleventh-row upper estimate.

P0's earlier real strict frontend attempt at the original P2
`RationalLogCertificate.lean` returned 1, at source SHA256
`525d4eb7e87932aef7c2ecee816c8f1eb3dee5fcfc679c275444e278b06094c2`:
line 66 reported `unnecessarySeqFocus`, and line 102 reported a
`linarith` failure. P0 has now repaired those actual diagnostics and
validated source SHA256
`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`
at `c9f407efe66240c08c2e8a678330ba7b98b74db5`. The original failure
remains in P0's history receipt; it is not the status of the newly accepted
repaired source. P5 has not edited or copied P2's production files.

## 6. Precisely open suppliers and their receivers

| Supplier -> receiver | Open actual input |
| --- | --- |
| P1 -> P5/P2 | The adopted lower policies at `a,h`, historical joint supports/integrals, restoration and finite feedback identities, with actual physical levels and support gates |
| P2 -> P5 | All concrete adopted mask checks, actual integral certificates and aggregation, saved-floor semantics, same-parent local restriction, and the full negative-cost cover |
| P1/P3 -> P5 | Membership of the actual selected sieve rows in `ChenQuotientRows`: full `p*e` or `(p1*p2)*e ≤ Q`, with `Q ≤ panModulusCutoff N B` |
| P3 -> P5/P4-A | The actual high-modulus signed prime-product supplier, common intervals/phases/packets, and legal rough/smooth decompositions; new auxiliary large-q bounds do not supply the missing small-q rough `1`/Möbius input |
| P4-A -> P5 | One actual final `rho`, its pointwise majorant, supports and coefficient controls, and actual density at `K=8452171/1250000`, including the real compiler reserve |
| P4-A/P3 + P5 -> P5 | Insert that same `rho` into the positive switched families and compute their actual labelled masses for rows 7-11, with all multiplicities and boundary corrections |
| P5 -> P0 | Every oriented actual row estimate (or the joint last two), the complete adopted-mask weight mean at coefficient `4*c`, then final `hLower` |

P1 now has a fixed source handoff at
`70ad4d737a2ff4a77413a5975af2fb41bdfb7d66`, directly based on the
unchanged common baseline. Its four new production leaves remain
**source candidates at that checkpoint**. The following complete
relevant type is source-extracted, not compiler-confirmed:

```lean
theorem ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_ceil_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixLowerDensity N (Nat.ceil ((N : ℝ) ^ (b : ℝ)))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

This supplies a candidate ordinary-parent lower-fourth density limit for
fixed cells and checks. Its normalization is `log N / singularSeries N`;
the actual prime-source mean still needs its source/density/distribution
connection in `singularNormalization N` units. The actual adopted table,
whole-box checks, historical composition and numerical L1 endpoint are
not instantiated by this type. The P1 handoff provides no new completed
S1 beta supplier closure for P5's separate InitialMean candidate.

P3's latest source still requires `Part3CurrentLowerRows N Q S3 S4 S5 S6`
in its current Y3-Y6 remainder theorem. Its `UniformPrimeProductTarget`
is still a `Prop` target, not a supplied theorem for the adopted `rho`.
P0's separate `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` adds a
LongSlot repair candidate with strict compilation, replay and audit all
pending. It does not supply a newly verified actual signed-distribution
input. Its exact candidate record is included in the fixed upstream
inspection receipt.
P4's latest checkpoint changes only its handoff documentation: the
full-policy density theorem still has `hIntegral`, `hCertificate` and
`hgap` inputs, and the final compiled coefficient still needs its own
reserve. There is no new unconditional common-K supplier to receive.

Two important open types can be stated directly in the existing
definitions. These are requirements for the real selected construction,
not new premises in a claimed proof of the complete mean.

For P1/P3, the actual row supports must satisfy the existing condition:

```lean
def ChenQuotientRows {α : Type*}
    (N : ℕ) (A : ℝ) (Q : ℕ)
    (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ) : Prop :=
  ∀ t ∈ T,
    S t ⊆ ((sieveProduct N (Nat.ceil A)).divisors.filter
      (fun d => b t * d ≤ Q))
```

The `b` here is the actual prime or full prime-pair product. P3's current
supplier also requires `Q ≤ panModulusCutoff N B`, preserving the pinned
one-half level and all logarithmic factors. It cannot be instantiated by
checking only the residual divisor, nor used as a supplied high-modulus
signed prime-product theorem.

For P4-A, after constructing the actual common
`Q : ℝ → ℕ → Finset ℕ` and `rho : ℝ → ℕ → ℕ → ℝ`, the open density
input has this exact form:

```lean
∀ delta : ℝ, 0 < delta →
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    physicalDensitySum (Q delta N) (rho delta N) ≤
      (currentK + delta) * (singularSeries N / Real.log (N : ℝ))
```

Its same actual `rho` must also satisfy the physical majorant, support,
coefficient and signed-distribution inputs. This density statement is
not supplied at the inspected P4 checkpoint. Evaluating a raw density
without the compiled coefficient's reserve would leave a different
input unproved. Part 4-B's `hUpper` is not needed.

For a fixed actual adopted `E : ℕ → (ℕ × ℕ → Prop)`, the missing row
statements have the precise form, for every `delta > 0`, eventually on
even N: lower bounds `(b_i-delta)*singularNormalization N ≤ U_i N`
for i=1,2,5,6, and upper bounds
`U_i N ≤ (b_i+delta)*singularNormalization N` for i=3,4,7,8,9,
plus the actual joint bound
`U10 N + U11 N (E N) ≤ (b1011+2*delta)*singularNormalization N`.
Here each `b_i` must be the certified value of the actual adopted
functional; these are requirements, not new assumptions in a purported
complete-mean theorem. The source candidate in section 4 proves a
different ordinary first-row coefficient and makes no adopted-endpoint
identification.

The final unproved export remains the following statement, which is not
declared as a theorem by this delivery:

```lean
∀ epsilon : ℝ, 0 < epsilon →
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```

Part 4-B's `hUpper` is not a required input to any of this work.

## 7. Execution boundaries

The finite component's three gates have completed successfully:

| Target or audit | Actual strict frontend | Actual bundled kernel replay | Audited own declarations |
| --- | --- | --- | ---: |
| `CurrentChenMeanLedger` | Exit 0, 171.955 seconds | Exit 0, 74.535 seconds | 93 |
| `CurrentChenLowerScale` | Exit 0, 205.151 seconds | Exit 0, 80.788 seconds | 5 |
| Combined `ChenP5Audit` | Exit 0, 214.417 seconds | Not a separate proof target | 103 across these two modules and the unchanged Buchstab module |

The 103-declaration inventory includes all five Buchstab declarations.
It additionally prints and transitively audits the two unchanged imported
count bridges, separately from those 103 declarations. Every collected
axiom belongs to `propext`, `Classical.choice`, `Quot.sound`. The complete
[finite receipt](../verification/parts/p5/round2/finite/receipt.json) binds
the final sources, compiled objects, commands, toolchain pins and audit.
Raw success logs, the 23 necessary baseline dependency-compilation logs,
both real MeanLedger strict failures and the cache-search failure are
archived alongside that receipt.

Only six MeanLedger proof bodies were repaired: four hidden-decidability
instance matches and two tactic-sequencing diagnostics. Its 34 public
theorem headers and 16 definitions are unchanged. The complete LowerScale
source is unchanged and passed on its first strict attempt. Source-header
comparison evidence is labelled separately from the compiler-printed
type inventory; the latter is the acceptance type record.

The independent actual-source component has also completed all three gates:

| InitialSource check | Actual result |
| --- | --- |
| Strict trust-zero frontend, warnings as errors | Exit 0, 258.283 seconds |
| Original bundled kernel replay | Exit 0, 210.823 seconds |
| Independent `InitialSourceAudit` | Exit 0, 680.789 seconds; 8 actual own declarations |

Its source SHA256 is `4b11a63cc976a0866068337c12d616578dace6c80736574311f4cca13f7d8956`;
its object SHA256 is `8b9ee7b0e4f18ea06057a99f075e87065131e12873221e114b9c5d5c46a8ef39`. Both are identical
through compilation, replay and audit. The accepted type inventory comes
from the actual environment. The [InitialSource receipt](../verification/parts/p5/round2/initial-source/receipt.json)
and archived logs record the completed commands, exact import hashes,
source-matched cache reuse and all actual dependency compilations.

The initial strict target attempt returned 1 after 428.784 seconds.
Only two repairs were needed: normalize the product-support nonmembership
hypothesis to the exact upstream condition before rewriting, and open the
existing parent namespace of `goldbachDifferenceCarrier`. The five public
declaration texts are unchanged. The complete failure log and the
[diagnostic repair record](../verification/parts/p5/round2/initial-source/actual-diagnostic-repair.json)
are retained. This namespace fix was also applied to the separate
InitialMean candidate; it does not constitute a compilation of that file.

The first-row mean candidate's current source SHA256 is
`5358e4dbbda436b335620de19884624df3260386d5ab5e478a85f70599da6137`. Its complete source declaration,
actual pinned supplier type and resolver-visible validation backlog are
recorded in [initial-mean-candidate.json](../verification/parts/p5/round2/initial-source/initial-mean-candidate.json).
This candidate is not included in either successful declaration inventory.
The source-level redundant-tactic fix and the interrupted supplier
attempt each retain their own earlier hashes and evidence.

The original Lean 4.33.0-rc1 toolchain and pinned dependencies are used.
Official frontend compilation explicitly sets trust level zero; new
proof targets are checked with warnings as errors. The bundled checker
replays each target's declarations against its imports. The audit uses
the actual elaborated environment and transitive axiom collection,
including private/generated declarations. It is not a regex inventory
or a claim of `--fresh` checking every imported declaration.

Already completed P0/P1 objects are reused only with matching source and
object provenance. Necessary missing finite dependencies are built in
P5's separate output directory. A real namespace-search cache issue
(`Counting.olean` missing from the selected local namespace directory)
was corrected by copying verified, unchanged cache objects; the failed
attempt and cache provenance remain recorded. No dependency proof was
edited to make this environment repair.

The Buchstab commit's Actions runs `38200419493` and `38200419496`
initially failed on attempt 1 with runner ID zero and no executed steps.
At the separately recorded 2026-10-12 04:24:32 UTC snapshot, attempt 2
had real runners: the variable-envelope run had succeeded, while the
core run was still building, with its later replay and audit steps pending.
This thread did not trigger a rerun. The snapshot and precise coverage
are recorded in [the CI scope receipt](../verification/parts/p5/round2/ci/scope.md).

The successful variable-envelope artifact covers eight listed VE modules
and 358 declarations. Its 20 reported source hashes match the fixed
Buchstab commit, but it contains no compiled objects or Lake cache.
Neither that workflow nor the core root import closure covers the new
P5 Buchstab, mean-ledger or lower-scale modules, or the required S1 beta
supplier. The P5 checks above therefore use their own hash-bound official
frontend, bundled checker and audit records. No P5 result is inferred
from an unrelated green CI job or from a cache-restore step alone.

The original toolchain, manifests, shared definitions, manuscript,
`CurrentMainTheorem.lean`, `CurrentNumericalTransfer.lean`, root imports
and workflows remain unchanged on this Part 5 branch. No Codex CLI or
Codex task is started.
