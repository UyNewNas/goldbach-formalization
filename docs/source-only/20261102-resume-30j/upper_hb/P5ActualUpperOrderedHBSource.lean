import ImbalancedChen.P5AllGroupOrderedRectangleReindex
import ImbalancedChen.P5ActualUpperPairOriginalHBSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal attachedUpper independent-prime pair source reaches the full
ordered individual HB rectangles. The temporary cap is removed from the
actual normalized smooth profile, rather than from a lower singleton
analogy or an assumed Family/source-cover equation. All original reserves
and the same signed complete-modulus kernel are retained.
-/
namespace ImbalancedChen.P5Z.ActualUpperOrderedHBSource
noncomputable section
open Classical Filter
open scoped BigOperators
open P5ActualIndependentUpperPairProfile
open P5ActualUpperPairHBLogTransport P5ActualUpperPairOriginalHBSource
open AllGroupOrderedRectangleReindex PerGroupIntegerHBAtlasPushforward
open LicensedOriginalIntegerProfile ExactOriginalSmoothDyadicPartition
open IndependentPrimeSourceWordDictionary OriginalPrimeAllGroupHBDiscrepancy
open ImbalancedChen.Part3.OriginalProperPowerActualChart

/-- The exact H normalized numerator, with no change to the physical rho. -/
def upperTest (D : Parameters) (b : Band D) (N : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (rows : List Row) : ℂ :=
  (listExtension (ActualIndependentUpperPairLogFields.licence D b N)
    (originalProducts rows) : ℂ) *
    (ActualEtaPsiOccurrenceBudget.eta
      (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ) *
    wordKernel Q rho N (originalProducts rows)

/-- The two ORIGINAL group logarithms, including totalized unit cases.
No HB occurrence log and no physical residual denominator replaces them. -/
theorem upperTest_original_group_logs (D : Parameters) (b : Band D) (N : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (rows : List Row) :
    upperTest D b N kappa0 Q rho rows =
      ((listExtension (P5ActualIndependentUpperPairProfile.licence D b N)
          (originalProducts rows) : ℂ) / (wordLog (originalProducts rows) : ℂ)) *
        (ActualEtaPsiOccurrenceBudget.eta
          (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ) *
        wordKernel Q rho N (originalProducts rows) := by
  unfold upperTest
  rw [actual_listExtension_normalization, Complex.ofReal_div]

/-- Genuine support of the existing actual upper profile removes the
original enumeration cap. This is valid for EVERY Row list, not merely
prime replacements or the HB rows that happen to be visited later. -/
theorem actual_upperTest_capSupported (D : Parameters) (b : Band D) (N : ℕ)
    (hscale : Real.exp (selected D).width ≤ (N : ℝ)^D.theta)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    CapSupported N (upperTest D b N kappa0 Q rho) := by
  intro rows row hrow hlarge
  by_contra htest
  have hWc : (listExtension (ActualIndependentUpperPairLogFields.licence D b N)
      (originalProducts rows) : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htest).1).1
  have hW : listExtension (ActualIndependentUpperPairLogFields.licence D b N)
      (originalProducts rows) ≠ 0 := by
    intro hz
    exact hWc (by rw [hz]; rfl)
  have hlen : (originalProducts rows).length = 2 := by
    by_contra hn
    exact hW (by simp only [listExtension, dif_neg hn])
  have hnorm : ActualIndependentUpperPairLogFields.profile D b N
      (fun i => (wordVector 2 (originalProducts rows) i : ℝ)) ≠ 0 := by
    change integerExtension (ActualIndependentUpperPairLogFields.licence D b N)
      (wordVector 2 (originalProducts rows)) ≠ 0
    rw [← listExtension_ofFn, ofFn_wordVector hlen]
    exact hW
  have hraw : P5ActualIndependentUpperPairProfile.profile D b N
      (fun i => (wordVector 2 (originalProducts rows) i : ℝ)) ≠ 0 :=
    ActualIndependentGroupLogNormalization.normalize_nonzero hnorm
  have hc := nonzero_coordinates_lt_N D b hscale hraw
  have hm : row.factors.prod ∈ originalProducts rows :=
    List.mem_map.mpr ⟨row, hrow, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hm
  have hi2 : i < 2 := by omega
  have hs := hc ⟨i, hi2⟩
  have heq : wordVector 2 (originalProducts rows) ⟨i, hi2⟩ = row.factors.prod := by
    simpa only [wordVector, List.getD_eq_getElem _ _ hi] using hget
  rw [heq] at hs
  have hsmall : row.factors.prod < N := by exact_mod_cast hs
  omega

/-- The actual normalized source on full individual rectangles. Each
recursive group retains its own real cube cutoff and original smooth psi;
the complete-product eta remains in upperTest. -/
def upperOccurrenceAtlas (D : Parameters) (b : Band D) (N K : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  fullEval ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js
    (upperTest D b N kappa0 Q rho)

/-- Real source identity for the independently defined H upper atlas.
No all-rank Family, rectangular cover, support field or equality with a
candidate source is assumed. Only the explicit growing scale threshold
already proved for this production smooth family is used. -/
theorem actual_upper_atlas_eq_occurrences (D : Parameters) (b : Band D)
    (N K : ℕ) (hscale : Real.exp (selected D).width ≤ (N : ℝ)^D.theta)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ)
    (hjs : js.length = 2) :
    normalizedAllGroupAtlas D b N K kappa0 Q rho js =
      upperOccurrenceAtlas D b N K kappa0 Q rho js := by
  unfold normalizedAllGroupAtlas upperOccurrenceAtlas
  simpa only [hjs, upperTest] using
    numerator_source_eq_full_rectangles N ActualEtaPsiOccurrenceBudget.chi
      (beforeHBCutoff K js) js (upperTest D b N kappa0 Q rho)
      (actual_upperTest_capSupported D b N hscale kappa0 Q rho)

/-- All three original corrections remain in exactly the same chart bank. -/
def upperRestoredOccurrences (D : Parameters) (b : Band D) (N K : ℕ)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℂ :=
  trimReserve (P5ActualIndependentUpperPairProfile.licence D b N)
      N N kappa0 Q (fun q => (rho q : ℂ)) +
    ∑ js ∈ chartBank N 2,
      (upperOccurrenceAtlas D b N K kappa0 Q (fun q => (rho q : ℂ)) js -
        properPowerReserve (P5ActualIndependentUpperPairProfile.licence D b N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js +
        roughPrimeReserve (P5ActualIndependentUpperPairProfile.licence D b N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js)

theorem actual_restoredAtlas_eq_occurrences (D : Parameters) (b : Band D)
    (N K : ℕ) (hscale : Real.exp (selected D).width ≤ (N : ℝ)^D.theta)
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    restoredAtlas D b N K kappa0 Q rho =
      upperRestoredOccurrences D b N K kappa0 Q rho := by
  unfold restoredAtlas upperRestoredOccurrences
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [actual_upper_atlas_eq_occurrences D b N K hscale kappa0 Q
    (fun q => (rho q : ℂ)) js (words_spec _ _ _ hjs).1]

/-- The raw production prime caller reaches full ordered HB rectangles
with its literal attachedUpper coefficient in count AND exact mean. -/
theorem attached_upper_source_occurrences (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N)
    (hscale : Real.exp (selected D).width ≤ (N : ℝ)^D.theta)
    (K : ℕ) (kappa0 nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width) : ℂ) =
      upperRestoredOccurrences D b N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [attached_upper_pair_normalized_HB D b hN K kappa0 nu r epsilon retain cap,
    actual_restoredAtlas_eq_occurrences D b N K hscale]

/-- Noninjective physical product fibres and their labelled multiplicities
are unchanged when this source reaches the new ordered rectangle atlas. -/
theorem attached_upper_physical_fibre_occurrences (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N)
    (hscale : Real.exp (selected D).width ≤ (N : ℝ)^D.theta)
    (K : ℕ) (kappa0 nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ((∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N q *
        finitePrimitiveDiscrepancy (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N
            (P4B.smoothPhysicalPairOuterRamp b.val N
              (manuscriptHalfProductCutoff D.kappa N) (selected D).width)) N q) : ℂ) =
      upperRestoredOccurrences D b N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [attached_upper_physical_fibre_normalized_HB D b hN K kappa0 nu r epsilon retain cap,
    actual_restoredAtlas_eq_occurrences D b N K hscale]

/-- The scale threshold is actually discharged. One original-family
threshold precedes b, all chart/order choices and the physical coefficient
parameters, with no new ordering between the two trim exponents. -/
theorem eventually_attached_upper_source_occurrences (D : Parameters) :
    ∀ᶠ N : ℕ in atTop, ∀ (b : Band D) (K : ℕ) (kappa0 nu r epsilon : ℝ)
      (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      (Part3.primeProductSignedError 2 N N
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)
        (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
          (selected D).width) : ℂ) =
        upperRestoredOccurrences D b N K kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^D.theta) atTop atTop :=
    (Real.tendsto_rpow_atTop D.theta_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (Real.exp (selected D).width),
    Filter.eventually_ge_atTop (2 : ℕ)] with N hscale hN
  intro b K kappa0 nu r epsilon retain cap
  exact attached_upper_source_occurrences D b hN hscale K kappa0 nu r epsilon retain cap

end
end ImbalancedChen.P5Z.ActualUpperOrderedHBSource