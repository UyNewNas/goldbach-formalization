import ImbalancedChen.Part3AllKFamilyProperPowerSaving
import ImbalancedChen.P4BActualUpperTrimPayment

/-! Finite estimates for the literal proper-power reserve, including its
pre-HB rough projector. A coordinate is an ordered occurrence. The two
row bounds below address different complete products. -/
namespace ImbalancedChen.P3OriginalProperPowerChartPayment

noncomputable section
open Classical
open scoped BigOperators
open P5Z.ActualLabelledPrimeSmoothCharts P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.LicensedOriginalIntegerProfile
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.IndependentPrimeSourceWordDictionary
open P5Z.ProperPowerSignedMeanHBTransport (signedRow markedWords)
open P5Z.ProperPowerSignedModulusPayment (collisionWords collisionWords_card_le_divisor_power)
open Part3.OriginalProperPowerActualChart Part3.OriginalProperPowerChartCount
open Part3.AllKLambdaChartCorrection Part3.AllKFamilyLambdaCorrectionBound
open Part3.AllKFamilyProperPowerSaving (chart_log_bound)

private abbrev chi := P5Z.ActualEtaPsiOccurrenceBudget.chi
private abbrev eta := P5Z.ActualEtaPsiOccurrenceBudget.eta

/-- The padded rectangle is used only when its own marked chart is occupied.
This estimate uses a single licensed original profile and its integer
support, so no absent rank is added to the source family. -/
theorem marked_card {k N cap : ℕ} {W : (Fin k → ℕ) → ℝ}
    (L : Licence k W) (t : ℝ) {js : List ℕ} (hjs : js ∈ chartBank cap k)
    (bad : Fin k) {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U)
    (hsupp : ∀ ps ∈ integerWords cap k, listExtension L ps ≠ 0 →
      (∀ n ∈ ps, A ≤ (n : ℝ)) ∧ (ps.prod : ℝ) ≤ U * N) :
    ((markedWords L chi eta (N : ℝ) t cap js bad).card : ℝ) ≤
      2 * ((5 : ℝ)^k * U) * N * ((cutoffIndex cap + 2 : ℕ) : ℝ) / Real.sqrt A := by
  let S := markedWords L chi eta (N : ℝ) t cap js bad
  let V := chartUpper k js
  by_cases hs : S.Nonempty
  · obtain ⟨ps, hps⟩ := hs
    have hsdata := badChartWords_spec hps
    have hword := (Finset.mem_filter.mp hps).1
    have hwc : (listExtension L ps : ℂ) ≠ 0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hsdata.2.2.1).2).2
    have hgeo := hsupp ps hword (fun hz => hwc (by simp [hz]))
    have hbox := padded_chart_product_le_five_pow_word chi eta
      (fun u => (listExtension L u : ℂ)) (fun _ h => actual_chi_one h)
      (fun _ h => actual_chi_zero h) cap k (N : ℝ) t bad hjs hps
    have hwhole : (∏ i : Fin k, ((V i + 1 : ℕ) : ℝ)) ≤ ((5 : ℝ)^k * U) * N :=
      (hbox.trans (mul_le_mul_of_nonneg_left hgeo.2 (by positivity))).trans_eq
        (mul_assoc _ _ _).symm
    have maps (us : List ℕ) (hus : us ∈ S) :
        wordVector k us ∈ oneBadSlotBox V bad :=
      active_bad_word_in_chart_box chi eta _ (fun _ h => actual_chi_one h)
        (fun _ h => actual_chi_zero h) cap k (N : ℝ) t bad hjs hus
    have hcard : S.card ≤ (oneBadSlotBox V bad).card :=
      Finset.card_le_card_of_injOn _ maps
        (fun _ hu _ hv h => wordVector_injOn_length k (badChartWords_spec hu).1
          (badChartWords_spec hv).1 h)
    have hslot := Finset.mem_piFinset.mp (maps ps hps) bad
    have hp : wordVector k ps bad ∈ properPowers (V bad) := by
      simpa only [oneBadSlotBox, if_pos rfl] using hslot
    have hj : bad.val < ps.length := by rw [hsdata.1]; exact bad.isLt
    have hmem : wordVector k ps bad ∈ ps := by
      rw [wordVector, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hcap := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hlower : A ≤ (V bad : ℝ) := (hgeo.1 _ hmem).trans (Nat.cast_le.mpr hcap)
    have hb := oneBadSlotBox_absolute_mass_scale V bad
      (fun i => by dsimp [V, chartUpper]; positivity)
      (fun _ => (1 : ℂ)) 1 ((5 : ℝ)^k * U) (N : ℝ) A
      ((cutoffIndex cap + 2 : ℕ) : ℝ) zero_le_one (by positivity)
      (Nat.cast_nonneg N) hA (by positivity) (fun _ _ => by simp)
      hwhole hlower (by exact_mod_cast chart_log_bound hjs bad)
    change (S.card : ℝ) ≤ _
    exact (Nat.cast_le.mpr hcard).trans (by simpa using hb)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (S.card : ℝ) ≤ _
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Count actual signed rows after the complete modulus sum. The possible
diagonal is paid with the true divisor multiplicity at N. The volume
saving is used only at nonzero difference. -/
theorem actual_reserve_le {k N cap : ℕ} (hN : N ≠ 0) {W : (Fin k → ℕ) → ℝ}
    (L : Licence k W) (K : ℕ) (t : ℝ) {js : List ℕ} (hjs : js ∈ chartBank cap k)
    (Q : Finset ℕ) (rho : ℕ → ℂ) {A U M H : ℝ} (hA : 0 < A)
    (hU : 0 ≤ U) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hsupp : ∀ ps ∈ integerWords cap k, listExtension L ps ≠ 0 →
      (∀ n ∈ ps, A ≤ (n : ℝ)) ∧ (ps.prod : ℝ) ≤ U * N)
    (hweight : ∀ ps : List ℕ, ‖(listExtension L ps : ℂ)‖ ≤ M)
    (hoff : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ U * N → n ≠ N → ‖signedRow Q rho N n‖ ≤ H) :
    ‖properPowerReserve L K cap N t Q rho js‖ ≤
      (k : ℝ) * ((2 * ((5 : ℝ)^k * U) * N * ((cutoffIndex cap + 2 : ℕ) : ℝ) /
        Real.sqrt A) * (M * H) +
        ((N.divisors.card ^ k : ℕ) : ℝ) * (M * ‖signedRow Q rho N N‖)) := by
  let S (bad : Fin k) := markedWords L chi eta (N : ℝ) t cap js bad
  let g (ps : List ℕ) := ‖lambdaWord ps * originalChart L N t js ps *
    (roughWord (beforeHBCutoff K js) ps * wordKernel Q rho N ps)‖
  have hchi (x : ℝ) : 0 ≤ chi x ∧ chi x ≤ 1 := by
    have hh := P5Z.ActualEtaPsiOccurrenceBudget.eta_bounds x
    dsimp [chi, P5Z.ActualEtaPsiOccurrenceBudget.chi]
    constructor <;> linarith only [hh.1, hh.2]
  have hchart (ps : List ℕ) : ‖originalChart L N t js ps‖ ≤ M := by
    have hη (x : ℝ) : ‖(eta x : ℂ)‖ ≤ 1 := by
      have hh := P5Z.ActualEtaPsiOccurrenceBudget.eta_bounds x
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
    unfold originalChart chartTerm trimmedWeight
    rw [norm_mul, norm_mul]
    calc
      _ ≤ 1 * (1 * M) := mul_le_mul (tupleProfile_norm_le_one chi hchi js ps)
        (mul_le_mul (hη _) (hweight ps) (norm_nonneg _) zero_le_one)
        (by positivity) zero_le_one
      _ = _ := by ring
  have hpoint (ps : List ℕ) : g ps ≤ M * ‖signedRow Q rho N ps.prod‖ := by
    dsimp only [g]
    rw [P4BActualUpperTrimPayment.wordKernel_eq_signedRow]
    simp only [norm_mul]
    calc
      _ ≤ (1 * M) * (1 * ‖signedRow Q rho N ps.prod‖) :=
        mul_le_mul (mul_le_mul (lambdaWord_norm_le_one ps) (hchart ps) (norm_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_right (roughWord_norm_le_one _ _) (norm_nonneg _))
          (by positivity) (by positivity)
      _ = _ := by ring
  have hcover : (∑ ps ∈ properChartWords cap k, g ps) ≤ ∑ bad : Fin k, ∑ ps ∈ S bad, g ps := by
    apply covered_nonnegative_sum_le _ Finset.univ _ g (fun _ => norm_nonneg _)
    intro ps hps hg
    have ha : originalChart L N t js ps ≠ 0 := fun hz => hg (by simp [g, hz])
    obtain ⟨bad, hm⟩ := active_proper_chart_in_bad_words chi eta
      (fun us => (listExtension L us : ℂ)) (N : ℝ) t js hps ha
    exact ⟨bad, Finset.mem_univ _, hm⟩
  have hone (bad : Fin k) :
      (∑ ps ∈ S bad, g ps) ≤
        (2 * ((5 : ℝ)^k * U) * N * ((cutoffIndex cap + 2 : ℕ) : ℝ) / Real.sqrt A) * (M*H) +
        ((N.divisors.card ^ k : ℕ) : ℝ) * (M * ‖signedRow Q rho N N‖) := by
    have per (ps : List ℕ) (hps : ps ∈ S bad) :
        g ps ≤ M*H + (if ps.prod = N then M * ‖signedRow Q rho N N‖ else 0) := by
      by_cases he : ps.prod = N
      · rw [if_pos he]
        exact ((hpoint ps).trans_eq (by rw [he])).trans
          (le_add_of_nonneg_left (mul_nonneg hM hH))
      · rw [if_neg he, add_zero]
        have hs := badChartWords_spec hps
        have hwc : (listExtension L ps : ℂ) ≠ 0 :=
          (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.2.2.1).2).2
        have hgeo := hsupp ps (Finset.mem_filter.mp hps).1 (fun hz => hwc (by simp [hz]))
        have hp : 0 < ps.prod := List.prod_pos (fun n hn => (hs.2.1 n hn).1)
        exact (hpoint ps).trans (mul_le_mul_of_nonneg_left (hoff _ hp hgeo.2 he) hM)
    have hc := marked_card L t hjs bad hA hU hsupp
    have hd := collisionWords_card_le_divisor_power L chi eta (N : ℝ) t cap js bad N hN
    change ((S bad).filter (fun ps => ps.prod = N)).card ≤ _ at hd
    calc
      _ ≤ ∑ ps ∈ S bad, (M*H + (if ps.prod = N then M*‖signedRow Q rho N N‖ else 0)) :=
        Finset.sum_le_sum per
      _ = ((S bad).card : ℝ) * (M*H) +
          (((S bad).filter (fun ps => ps.prod = N)).card : ℝ) * (M * ‖signedRow Q rho N N‖) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (mul_nonneg hM hH))
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) (mul_nonneg hM (norm_nonneg _)))
  calc
    _ ≤ ∑ ps ∈ properChartWords cap k, g ps := norm_sum_le _ _
    _ ≤ _ := hcover
    _ ≤ ∑ _bad : Fin k,
        ((2 * ((5 : ℝ)^k * U) * N * ((cutoffIndex cap + 2 : ℕ) : ℝ) / Real.sqrt A) * (M * H) +
          ((N.divisors.card ^ k : ℕ) : ℝ) * (M * ‖signedRow Q rho N N‖)) :=
      Finset.sum_le_sum (fun bad _ => hone bad)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end ImbalancedChen.P3OriginalProperPowerChartPayment
