import ImbalancedChen.P3OriginalU5JointCellCoefficient
import ImbalancedChen.P3OriginalU5RoundedPairDensity

/-! The joint marked rough coefficient on the original U5 carrier receives
the actual sign-dependent small Rosser coefficient. This physical rho is
used in the divisor sum, the full-totient density and the original count. -/

namespace ImbalancedChen.P3OriginalU5JointBetaAttachment

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding (raw universe_rough)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P3OriginalU5CommonPhysicalRoot (policy)
open P3OriginalU5JointCellCoefficient (roughCarrier coefficient coefficient_le_raw coefficient_abs_le_one)
open P3OriginalU5RoundedCountInsertion (roundedSupport)
open P3OriginalU5RoundedPairDensity (fullModulus_density_eq)
open P5OriginalU5CausalFinite (pairSupport cutoff smallCutoff smallLevel attachment_gates)
open P5OriginalU5PlateauPrimeBV (fullModulus markedProduct)

abbrev small (N : ℕ) (epsilon : ℝ) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon)

abbrev betaPlus (N : ℕ) (epsilon : ℝ) : ℕ → ℝ :=
  actualSmallRosserPlus N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (smallLevel N epsilon)

abbrev betaMinus (N : ℕ) (epsilon : ℝ) : ℕ → ℝ :=
  actualSmallRosserMinus N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (smallLevel N epsilon)

variable (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
  (m N : ℕ) (epsilon tau : ℝ)

def rho (t : ℕ × ℕ) : ℕ → ℝ :=
  smallRoughRho (small N epsilon) (roughCarrier N epsilon)
    (fun d => coefficient R bank b m N epsilon tau (t,d)) (betaPlus N epsilon) (betaMinus N epsilon)

theorem rho_at_product (t : ℕ × ℕ) {s d : ℕ} (hs : s ∈ small N epsilon) (hd : d ∈ roughCarrier N epsilon) :
    let c := coefficient R bank b m N epsilon tau (t,d)
    rho R bank b m N epsilon tau t (s*d) = c * (if 0 ≤ c then betaMinus N epsilon s else betaPlus N epsilon s) :=
  smallRoughRho_mul (fun _ h => actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ h)
    (fun _ h => universe_rough _ _ _ _ h) (fun r => coefficient R bank b m N epsilon tau (t,r))
    (betaPlus N epsilon) (betaMinus N epsilon) hs hd

theorem rho_abs_le_one (t : ℕ × ℕ) (k : ℕ) : |rho R bank b m N epsilon tau t k| ≤ 1 := by
  by_cases hk : k ∈ roundedSupport N epsilon
  · obtain ⟨⟨s,d⟩, hsd, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hs, hd⟩ := Finset.mem_product.mp hsd
    exact abs_smallRoughRho_mul_le_one
      (fun _ h => actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ h)
      (fun _ h => universe_rough _ _ _ _ h)
      (fun r => coefficient R bank b m N epsilon tau (t,r)) (betaPlus N epsilon) (betaMinus N epsilon)
      (fun r _ => coefficient_abs_le_one R bank b m N epsilon tau (t,r))
      (fun r _ => actualSmallRosserPlus_abs_le_one _ _ _ _ r)
      (fun r _ => actualSmallRosserMinus_abs_le_one _ _ _ _ r) hs hd
  · unfold rho
    rw [smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hk]
    norm_num

theorem rough_minorant {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (n : ℤ) :
    supportedDivisorSum (roughCarrier N epsilon) (fun d => coefficient R bank b m N epsilon tau (t,d))
        n.natAbs ≤ actualIntervalRoughIndicator N (smallCutoff N epsilon) (cutoff N) n := by
  have h := supportedDivisorSum_le_of_coefficient_le (roughCarrier N epsilon)
    (fun d => coefficient R bank b m N epsilon tau (t,d))
    (raw (policy R bank b m N t) N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N))
    (fun d _ => coefficient_le_raw R bank b m N epsilon tau ht d) n.natAbs
  rw [P2LowerFiniteCellBetaCompiler.raw_divisorSum_on_universe] at h
  exact h.trans (fixedEvenRoughDivisorSum_le_roughIndicator (policy R bank b m N t) N _ _ _ (Nat.le_ceil _) n)

/-- On each original pair the actual signed attachment minorizes the
physical roughness indicator, for every integer including zero. -/
theorem rho_minorant {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (tau : ℝ) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (n : ℤ) :
    physicalDivisorSum (roundedSupport N epsilon) (rho R bank b m N epsilon tau t) n.natAbs ≤
      actualSmallRoughIndicator N (cutoff N) n := by
  obtain ⟨hL, hwL, hwz⟩ := attachment_gates hN he he8
  have hs := actualSmallRosser_sandwich N (Nat.ceil (cutoff N)) (smallCutoff N epsilon)
    (smallLevel N epsilon) hL hwL (hwz.trans (Nat.le_ceil _)) n
  have h := physicalDivisorSum_smallRoughRho_lower
    (fun _ h => actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ h)
    (fun _ h => universe_rough _ _ _ _ h)
    (fun d => coefficient R bank b m N epsilon tau (t,d)) (betaMinus N epsilon) (betaPlus N epsilon) n.natAbs
    (actualSmallRoughIndicator_nonneg N (smallCutoff N epsilon) n)
    (rough_minorant R bank b m N epsilon tau ht n) hs.1 hs.2
  change _ ≤ actualSmallRoughIndicator N (smallCutoff N epsilon) n *
    actualIntervalRoughIndicator N (smallCutoff N epsilon) (cutoff N) n at h
  rwa [actualSmallRoughIndicator_mul_interval _ _ _ hwz n] at h

/-- Exact full-modulus density. A positive joint rough coefficient uses
the actual lower small density; a negative coefficient uses the upper. -/
theorem full_density_eq {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (tau : ℝ) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    (∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k /
      (Nat.totient (fullModulus t k) : ℝ)) =
      signSensitiveReciprocalTotientDensity (roughCarrier N epsilon)
        (fun d => coefficient R bank b m N epsilon tau (t,d))
        (reciprocalTotientDensity (small N epsilon) (betaPlus N epsilon))
        (reciprocalTotientDensity (small N epsilon) (betaMinus N epsilon)) /
          (Nat.totient (t.1 * t.2) : ℝ) := by
  rw [fullModulus_density_eq hN he he8 ht]
  exact congrArg (fun z : ℝ => z / (Nat.totient (t.1 * t.2) : ℝ))
    (physicalDensitySum_smallRoughRho_eq_signSensitive
      (fun _ h => actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ h)
      (fun _ h => universe_rough _ _ _ _ h) (fun d => coefficient R bank b m N epsilon tau (t,d))
      (betaPlus N epsilon) (betaMinus N epsilon))

/-- The finite AP estimator uses the identical joint rho as the physical
density, with both marks present in the modulus and centre subtraction. -/
theorem joint_count_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (tau : ℝ) :
    (∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k *
      (chenPrimeAPCount N N (fullModulus t k) - chenCentrePrimeAPCount N N (fullModulus t k))) ≤
        currentChenUpsilon5 N := by
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  apply Finset.sum_le_sum
  intro t ht
  change (∑ d ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t d *
    (chenPrimeAPCount N N (markedProduct t * d) - chenCentrePrimeAPCount N N (markedProduct t * d))) ≤ _
  rw [← P5CausalRhoQuotientBridge.quotient_sum_physicalDivisorSum]
  calc
    _ ≤ ∑ q ∈ chenQuotientPrimeSource N (markedProduct t),
        if ChenPrimeRough (cutoff N) q then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      have h := rho_minorant R bank b m hN he he8 tau ht (q : ℤ)
      have hind : actualSmallRoughIndicator N (cutoff N) (q : ℤ) =
          if Nat.Coprime q (sieveProduct N (Nat.ceil (cutoff N))) then (1 : ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [← actualSmallPrimeProduct_coprime_natAbs_iff N (Nat.ceil (cutoff N)) (cutoff N) (Nat.le_ceil _) (q : ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N (Nat.ceil (cutoff N)) (cutoff N) (Nat.le_ceil _),
          Nat.coprime_comm]
      have hr := chenPrimeRough_iff_coprime_sieveProduct (cutoff N) (chenQuotientPrimeSource_data hq).2.2
      simpa only [Int.natAbs_natCast, hind, ← hr] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedQuotientPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

end
end ImbalancedChen.P3OriginalU5JointBetaAttachment
