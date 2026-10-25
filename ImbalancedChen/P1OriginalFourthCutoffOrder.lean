import ImbalancedChen.P1OriginalCoarseFourthCellLimit
import ImbalancedChen.P1HistoricalFourthIntegralSign

/-!
Source-only, uncompiled, not root accepted.

Order and exact cutoff increments of the literal original fourth correction.
The original firstStop/raw-Q3 region is retained.  In particular the
generic historical-prefix `fullIntegral` is never substituted here.
These statements do not assert that a fixed positive cutoff removes the
arithmetic remainder, or supply the remaining zero-cutoff passage.
-/

namespace ImbalancedChen.P1OriginalFourthCutoffOrder

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseContinuation P1OriginalFourthIntegral
open P1FourthFullCellIntegral

/-- Lowering a positive truncation only enlarges the same original cell. -/
theorem truncatedCell_antitone (e : ℚ) (m : ℕ) (omega : ℝ)
    {a b : ℝ} (hab : a ≤ b) (j : FourthCell m) :
    truncatedCell e m omega b j ⊆ truncatedCell e m omega a j := by
  intro t ht
  refine ⟨?_, ht.2⟩
  apply mem_logPrimeBox.mpr
  intro i
  exact ⟨hab.trans (mem_logPrimeBox.mp ht.1 i).1,
    (mem_logPrimeBox.mp ht.1 i).2⟩

/-- Sign of the actual original-cell integrand, from the checked old/new
levels and the genuine continuous upper-factor order. -/
theorem original_integrand_nonneg
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m))
    (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    {t : Fin 4 → ℝ} (ht : t ∈ truncatedCell e m omega a j) :
    0 ≤ (extendedProfile (oldExponent e m j) t -
      extendedProfile (cap4 j : ℝ) t) * reciprocalWeight t := by
  have hpos : ∀ i, 0 < t i := fun i =>
    ha.trans_le (mem_logPrimeBox.mp ht.1 i).1
  apply mul_nonneg
  · exact sub_nonneg.mpr
      (P1FourthIntegralSign.extendedProfile_antitone_level t (hpos _)
        (selected_cap_ge_old e chi m omega J4 cap4 hcheck j hj))
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hpos i).le)

theorem original_cellIntegral_nonneg
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m))
    (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    0 ≤ cellIntegral e m omega a cap4 j := by
  exact setIntegral_nonneg (truncatedCell_measurable e m omega a j)
    (fun _ ht => original_integrand_nonneg e chi m omega ha J4 cap4 hcheck j hj ht)

theorem original_selectedIntegral_nonneg
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (J4 : Finset (FourthCell m))
    (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    0 ≤ selectedIntegral e chi m omega a J4 cap4 := by
  exact Finset.sum_nonneg (fun j hj =>
    original_cellIntegral_nonneg e chi m omega ha J4 cap4 hcheck j hj)

theorem original_cellIntegral_antitone_cutoff
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    cellIntegral e m omega b cap4 j ≤ cellIntegral e m omega a cap4 j := by
  apply setIntegral_mono_set (integrableOn_cellIntegrand e m omega ha cap4 j)
  · filter_upwards [ae_restrict_mem (truncatedCell_measurable e m omega a j)] with t ht
    exact original_integrand_nonneg e chi m omega ha J4 cap4 hcheck j hj ht
  · exact Filter.Eventually.of_forall (truncatedCell_antitone e m omega hab j)

theorem original_selectedIntegral_antitone_cutoff
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    selectedIntegral e chi m omega b J4 cap4 ≤
      selectedIntegral e chi m omega a J4 cap4 := by
  exact Finset.sum_le_sum (fun j hj =>
    original_cellIntegral_antitone_cutoff e chi m omega ha hab J4 cap4 hcheck j hj)

/-- The change between two arithmetic remainders has the exact corresponding
original integral increment.  The common original source cancels at finite
N; no separate convergence of that untruncated source is assumed. -/
theorem tendsto_original_remainder_cutoff_increment
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a b : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (hb : 0 < b) (hbRho : b < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N) -
      P1OriginalFourthLimit.smallRemainder e chi m omega b J4 cap4 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedIntegral e chi m omega b J4 cap4 -
        selectedIntegral e chi m omega a J4 cap4)) := by
  have h :=
    (P1OriginalFourthLimit.tendsto_actualSaving_sub_smallRemainder
      e chi m omega b hb hbRho J4 cap4 hcheck cap hcap).sub
    (P1OriginalFourthLimit.tendsto_actualSaving_sub_smallRemainder
      e chi m omega a ha haRho J4 cap4 hcheck cap hcap)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N => by ring)

end
end ImbalancedChen.P1OriginalFourthCutoffOrder
