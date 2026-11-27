import ImbalancedChen.P3OriginalU5JointBetaAttachment
import ImbalancedChen.P3OriginalU5JointPrimeWallPayment
import ImbalancedChen.P3OriginalU5PhysicalRawRank

/-! Fixed physical support of the marked joint coefficient. A retained
witness may change both marked primes as well as the rough divisor. -/

namespace ImbalancedChen.P3OriginalU5JointModulusCap

noncomputable section
open scoped Classical List
open P2LowerCapPlanIntegerRetention (coordinate coordinate_power physicalWord)
open P2LowerFiniteCellRounding (primeLabel)
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P2RoundedCausalFibreLossAndLevel (same_floor_word_sum_le universe_word_power)
open P3OriginalU5JointCellCoefficient (Point carrier coefficient same_fine_word same_rough_length
  retained_witness_of_ne_zero)
open P3OriginalU5JointPrimeWallPayment (word)
open P3OriginalU5JointBetaAttachment (rho betaMinus betaPlus rho_at_product)
open P3OriginalU5PhysicalRawRank (physical_raw_level_and_rank)
open P3OriginalU5RoundedCountInsertion (roundedSupport)
open P3OriginalU5RoundedModulusCap (rawRank)
open P5OriginalU5CausalFinite (attachmentNu cutoff smallCutoff smallLevel pairSupport)
open P5OriginalU5PlateauPrimeBV (fullModulus markedProduct)

private theorem marked_power {N : ℕ} (hN : 1 < (N : ℝ)) {epsilon : ℝ} {x : Point}
    (hx : x ∈ carrier N epsilon) :
    (N : ℝ) ^ ((word x).map (coordinate N)).sum = (fullModulus x.1 x.2 : ℝ) := by
  obtain ⟨ht, hd⟩ := Finset.mem_product.mp hx
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
  have hpow := universe_word_power hN (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) hd
  have hpos := zero_lt_one.trans hN
  simp only [word, List.map_cons, List.sum_cons]
  rw [Real.rpow_add hpos, Real.rpow_add hpos,
    coordinate_power hN (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos,
    coordinate_power hN (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos]
  change (x.1.2 : ℝ) * ((x.1.1 : ℝ) * ((N : ℝ) ^ (physicalWord N x.2.primeFactorsList).sum)) = _
  rw [hpow]
  simp only [fullModulus, markedProduct, Nat.cast_mul]
  ring

/-- The full logarithmic word has two marked slots in addition to the
rough rank. Directed joint rounding compares all of them with the same
genuinely retained original witness. -/
theorem marked_rough_level (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : 0 ≤ b) (m : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {epsilon tau : ℝ} (he : 0 < epsilon) (htau : 0 < tau) {x : Point}
    (hc : coefficient R bank b m N epsilon tau x ≠ 0) :
    (fullModulus x.1 x.2 : ℝ) ≤ (N : ℝ) ^ (topCap + ((rawRank epsilon : ℝ) + 2) * tau) := by
  obtain ⟨hx, y, hycell, hyraw⟩ := retained_witness_of_ne_zero R bank b m N epsilon tau hc
  obtain ⟨hy, hlabel⟩ := Finset.mem_filter.mp hycell
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hgood := physical_raw_level_and_rank R bank b hb m epsilon he hN
    (Finset.mem_product.mp hy).1 (Nat.ceil (cutoff N)) hyraw
  have hyn : ((word y).map (coordinate N)).sum ≤ topCap :=
    (Real.rpow_le_rpow_left_iff hNr).mp ((marked_power hNr hy).le.trans hgood.1)
  have hlen := same_rough_length R m N tau hlabel.symm
  have hlenN : ((word x).map (coordinate N)).length ≤ rawRank epsilon + 2 := by
    have hrank := hgood.2
    simp only [word, List.length_map, List.length_cons, List.length_reverse]
    omega
  have hlenR : (((word x).map (coordinate N)).length : ℝ) ≤ (rawRank epsilon : ℝ) + 2 := by
    exact_mod_cast hlenN
  have hf := same_fine_word R m N tau hlabel.symm
  have hfun : primeLabel N tau = fun p : ℕ => (⌊coordinate N p / tau⌋ : ℤ) := rfl
  rw [hfun] at hf
  have hsum := same_floor_word_sum_le htau ((word x).map (coordinate N)) ((word y).map (coordinate N))
    (by simpa only [word, List.map_map, Function.comp_def] using hf)
  rw [← marked_power hNr hx]
  exact Real.rpow_le_rpow_of_exponent_le hNr.le
    (hsum.trans (add_le_add hyn (mul_le_mul_of_nonneg_right hlenR htau.le)))

/-- The exponent includes the actual active small Rosser factor and the
two exterior labels of the joint cell. -/
theorem complete_level (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : 0 ≤ b) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon tau : ℝ}
    (he : 0 < epsilon) (htau : 0 < tau) {t : ℕ × ℕ} {k : ℕ}
    (hk : rho R bank b m N epsilon tau t k ≠ 0) :
    (fullModulus t k : ℝ) <
      (N : ℝ) ^ (topCap + ((rawRank epsilon : ℝ) + 2) * tau + attachmentNu * epsilon) := by
  have hmem : k ∈ roundedSupport N epsilon := by
    by_contra hnot
    exact hk (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot)
  obtain ⟨⟨s, d⟩, hsd, rfl⟩ := Finset.mem_image.mp hmem
  obtain ⟨hs, hd⟩ := Finset.mem_product.mp hsd
  rw [rho_at_product R bank b m N epsilon tau t hs hd] at hk
  let c := coefficient R bank b m N epsilon tau (t,d)
  change c * (if 0 ≤ c then betaMinus N epsilon s else betaPlus N epsilon s) ≠ 0 at hk
  obtain ⟨hc, hbeta⟩ := mul_ne_zero_iff.mp hk
  have hsmall : (s : ℝ) < smallLevel N epsilon := by
    by_cases hsign : 0 ≤ c
    · rw [if_pos hsign] at hbeta
      exact (actualSmallRosserMinus_active hbeta).2.1
    · rw [if_neg hsign] at hbeta
      exact (actualSmallRosserPlus_active hbeta).2.1
  have hrough := marked_rough_level R bank b hb m hN he htau (x := (t,d)) hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    (fullModulus t (s*d) : ℝ) = (s : ℝ) * (fullModulus t d : ℝ) := by
      simp only [fullModulus, markedProduct, Nat.cast_mul]
      ring
    _ ≤ (s : ℝ) * (N : ℝ) ^ (topCap + ((rawRank epsilon : ℝ) + 2) * tau) :=
      mul_le_mul_of_nonneg_left hrough (Nat.cast_nonneg _)
    _ < (N : ℝ) ^ (attachmentNu * epsilon) * (N : ℝ) ^ (topCap + ((rawRank epsilon : ℝ) + 2) * tau) :=
      mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hNpos _)
    _ = _ := by rw [← Real.rpow_add hNpos, add_comm]

/-- The sole physical budget is numerical and is independent of the
candidate bank, auxiliary mesh, target, marked row and modulus. -/
theorem complete_level_lt_599 (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : 0 ≤ b) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon tau : ℝ}
    (he : 0 < epsilon) (htau : 0 < tau)
    (hbudget : topCap + ((rawRank epsilon : ℝ) + 2) * tau + attachmentNu * epsilon ≤ 599/1000)
    {t : ℕ × ℕ} {k : ℕ} (hk : rho R bank b m N epsilon tau t k ≠ 0) :
    (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact (complete_level R bank b hb m hN he htau hk).trans_le
    (Real.rpow_le_rpow_of_exponent_le hNr hbudget)

/-- A support width chosen before every physical receiver and bank can
be refined together with the density width. -/
theorem exists_uniform_joint_cap {epsilon : ℝ} (he : 0 < epsilon)
    (hreserve : topCap + attachmentNu * epsilon < 599/1000) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
      ∀ (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ), 0 ≤ b →
      ∀ m N : ℕ, 2 ≤ N → ∀ t : ℕ × ℕ, ∀ k : ℕ, rho R bank b m N epsilon tau t k ≠ 0 →
        (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ) := by
  let D : ℝ := (rawRank epsilon : ℝ) + 2
  have hD : 0 < D := by dsimp only [D]; positivity
  let gap : ℝ := 599/1000 - (topCap + attachmentNu * epsilon)
  have hg : 0 < gap := sub_pos.mpr hreserve
  refine ⟨gap / D, div_pos hg hD, ?_⟩
  intro tau htau hsmall R mesh bank b hb m N hN t k hk
  have hpaid := (le_div_iff₀ hD).mp hsmall
  apply complete_level_lt_599 R bank b hb m hN he htau ?_ hk
  change topCap + D * tau + attachmentNu * epsilon ≤ 599/1000
  rw [mul_comm D tau]
  dsimp only [gap] at hpaid
  linarith only [hpaid]

end
end ImbalancedChen.P3OriginalU5JointModulusCap
