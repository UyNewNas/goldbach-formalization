import ImbalancedChen.P4BArbitraryWidthUpperPairProfile
import ImbalancedChen.P5ActualUpperPairHBLogTransport
import ImbalancedChen.P4BActualSmoothPhysicalPPA3

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

At EVERY legal width from the current real-b upper consumer, normalize
only the all-group HB numerator by the original group logarithms. The
left side remains the RAW physical smooth pair with its identical
attachedUpper coefficient. Quantitative trim/proper-power/rough-prime
payment and retained arithmetic PP are still internal open obligations.
-/
namespace ImbalancedChen.P4BArbitraryWidthUpperPairHBNormalization
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open P4B P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P5Z.ActualIndependentGroupLogNormalization
open P5Z.ExistingIndependentFamilyLogNormalization
open P5Z.AdmissibleAllRankIntegerGeometricFamily
open P5Z.AllWordAmbientOccurrenceBound P5Z.GroupedOccurrenceLogShift
open P5Z.LicensedOriginalIntegerProfile P5ActualUpperPairHBLogTransport
open P5Z.PerGroupIntegerHBAtlasPushforward
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.OriginalPrimeAllGroupHBDiscrepancy P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.IndependentPrimeSourceWordDictionary
open Part3.AllKLambdaChartCorrection Part3.OriginalProperPowerActualChart

def normalizedProfile (b kappa width : ℝ) (N : ℕ) : (Fin 2 → ℝ) → ℝ :=
  normalize (profile b kappa width N)

def normalizedIntegerWeight (b kappa width : ℝ) (N : ℕ) (u : Fin 2 → ℕ) : ℝ :=
  integerWeight b kappa width N u / ∏ i, Real.log (u i : ℝ)

theorem exact_integer_normalization (b kappa width : ℝ) (N : ℕ)
    (u : Fin 2 → ℕ) :
    normalizedProfile b kappa width N (fun i => (u i : ℝ)) =
      normalizedIntegerWeight b kappa width N u :=
  normalize_nat (profile b kappa width N) u

theorem normalized_smooth {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) :
    ContDiff ℝ ∞ (normalizedProfile b kappa width N) :=
  normalize_smooth _ (smooth hb hnu hr hwidth hgap N)

def normalizedLicence {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) :
    Licence 2 (normalizedIntegerWeight b kappa width N) where
  ambient := normalizedProfile b kappa width N
  smooth := normalized_smooth hb hnu hr hwidth hgap N
  agrees_on_primes := by intro u hu; exact exact_integer_normalization _ _ _ _ _

theorem normalized_support {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    {p : Fin 2 → ℝ} (hn : normalizedProfile b kappa width N p ≠ 0) :
    2 ≤ N ∧ p ∈ positivePrimeOrthant ∧
      (∀ i, (N : ℝ) ^ (nu * r) < p i) ∧
      (N : ℝ) ^ (1 - kappa - width) < p 0 * p 1 ∧
      p 0 * p 1 < Real.exp width * (N : ℝ) :=
  nonzero_data hb hnu hr hwidth hgap (normalize_nonzero hn)

theorem normalized_finite_integer_support {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) :
    Set.Finite {u : Fin 2 → ℕ | normalizedIntegerWeight b kappa width N u ≠ 0} := by
  apply (finite_integer_support hb hnu hr hwidth hgap N).subset
  intro u hu
  rw [← exact_integer_normalization] at hu
  exact normalize_nonzero hu

/-- Uniform in all genuine HB owner maps, including repeated owners.
The weight and width are the actual upper consumer's, not selected D.width.
Original group reciprocal logs cost a fixed factor, no extra width loss. -/
theorem normalized_occurrence_width_budget (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ N m (owner : Fin m → Fin 2) (U : Fin m → ℝ)
        (w : List (Fin m)) z, w.length ≤ q →
        |occWord w (fun y => normalizedProfile b kappa width N
          (fun i => groupProduct owner U i y)) z| ≤ C / width ^ q := by
  obtain ⟨K, hK, hnormalize⟩ := normalize_occurrence_bound 2 q
  obtain ⟨C, hC, hraw⟩ := mixed_width_budget q
  refine ⟨(K : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap N m owner U w z hw
  have h := hnormalize 2 le_rfl m owner U (profile b kappa width N)
    (smooth hb hnu hr hwidth hgap N) (C / width ^ q)
    (div_nonneg hC (pow_nonneg hwidth.le _))
    (fun v p hv => hraw b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap N v p hv)
    w z hw
  calc
    _ ≤ (K : ℝ) * (C / width ^ q) := h
    _ = ((K : ℝ) * C) / width ^ q := by ring

/-- Exact denominator transport at all natural original group products,
including 0 and 1. The reciprocal-log extension is smooth, while this
integer equality uses Lean's totalized division without extra filters. -/
theorem listExtension_normalization {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) (ns : List ℕ) :
    listExtension (normalizedLicence hb hnu hr hwidth hgap N) ns =
      listExtension (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N) ns / wordLog ns := by
  by_cases hlen : ns.length = 2
  · have htest :
        listExtension (normalizedLicence hb hnu hr hwidth hgap N)
            (List.ofFn (wordVector 2 ns)) =
          listExtension (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
              (List.ofFn (wordVector 2 ns)) / wordLog (List.ofFn (wordVector 2 ns)) := by
      simp only [listExtension_ofFn, wordLog_ofFn, integerExtension]
      exact normalize_nat (profile b kappa width N) (wordVector 2 ns)
    simpa only [ofFn_wordVector hlen] using htest
  · simp only [listExtension, dif_neg hlen, zero_div]

theorem all_group_normalization {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ)
    (chi : ℝ → ℝ) (z : ℝ) (cjs ns : List ℕ) (F : List Row → ℂ) :
    atlasEval chi z cjs ns (fun rows =>
      (listExtension (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N) (originalProducts rows) : ℂ) * F rows) =
      numeratorAtlas chi z cjs ns (fun rows =>
        (listExtension (normalizedLicence hb hnu hr hwidth hgap N)
          (originalProducts rows) : ℂ) * F rows) := by
  rw [actual_atlas_denominators]
  symm
  calc
    _ = numeratorAtlas chi z cjs ns (fun rows =>
        ((listExtension (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
          (originalProducts rows) : ℂ) * F rows) / (wordLog ns : ℂ)) := by
      apply numeratorAtlas_congr_on_originalProducts
      intro rows hrows
      simp only [listExtension_normalization, Complex.ofReal_div, hrows]
      ring
    _ = _ := numeratorAtlas_div_const chi z cjs ns _ _

section Source
variable {b kappa nu r width : ℝ}
variable (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
variable (hgap : 2 * width ≤ baseline b kappa - nu * r)

def normalizedAtlas (N K : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ integerWords N 2,
    numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
      (fun rows =>
        (listExtension (normalizedLicence hb hnu hr hwidth hgap N)
          (originalProducts rows) : ℂ) *
        (P5Z.ActualEtaPsiOccurrenceBudget.eta
          (((originalProducts rows).prod : ℝ) / (N : ℝ) ^ (1 - kappa0)) : ℂ) *
        wordKernel Q rho N (originalProducts rows))

theorem rawAtlas_eq_normalized (N K : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    allGroupAtlas (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N) K N N kappa0 Q rho js =
      normalizedAtlas hb hnu hr hwidth hgap N K kappa0 Q rho js := by
  unfold allGroupAtlas normalizedAtlas
  apply Finset.sum_congr rfl
  intro ps hps
  simpa only [mul_assoc] using all_group_normalization hb hnu hr hwidth hgap N
    P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps
    (fun rows =>
      (P5Z.ActualEtaPsiOccurrenceBudget.eta
        (((originalProducts rows).prod : ℝ) / (N : ℝ) ^ (1 - kappa0)) : ℂ) *
        wordKernel Q rho N (originalProducts rows))

/-- Explicit exact restoration; no reserve is erased or assumed paid. -/
def restoredAtlas (N K : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℂ :=
  trimReserve (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N) N N kappa0 Q (fun q => (rho q : ℂ)) +
    ∑ js ∈ chartBank N 2,
      (normalizedAtlas hb hnu hr hwidth hgap N K kappa0 Q (fun q => (rho q : ℂ)) js -
        properPowerReserve (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js +
        roughPrimeReserve (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js)

theorem original_pair_normalized_HB {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (Part3.primeProductSignedError 2 N N Q rho
      (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
      restoredAtlas hb hnu hr hwidth hgap N K kappa0 Q rho := by
  rw [original_signed_source b kappa width hN Q rho]
  rw [original_prime_allGroup_discrepancy
    (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N) K N N kappa0 Q rho]
  unfold restoredAtlas
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [rawAtlas_eq_normalized]

/-- The current hUniformPP source, at its unchanged epsilon, retain and
cap, now has a derived all-group normalization for EVERY legal width.
This is an exact identity, not an assumed estimate for its right side. -/
theorem attachedUpper_normalized_HB {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
      restoredAtlas hb hnu hr hwidth hgap N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) :=
  original_pair_normalized_HB hb hnu hr hwidth hgap hN K kappa0 _ _

theorem attachedUpper_physical_fibre_normalized_HB {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ((∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N q *
        finitePrimitiveDiscrepancy (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N
            (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width))
          N q) : ℂ) =
      restoredAtlas hb hnu hr hwidth hgap N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [P4BLabelledOuterPushforward.signed_productWeight_eq_primeProductSignedError]
  exact attachedUpper_normalized_HB hb hnu hr hwidth hgap hN K kappa0 epsilon retain cap

end Source
end
end ImbalancedChen.P4BArbitraryWidthUpperPairHBNormalization
