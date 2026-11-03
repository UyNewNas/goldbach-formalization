import ImbalancedChen.P5OriginalU789SmoothLogSources
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches
import ImbalancedChen.P5IndependentTestPrimeChartUniformCutoff

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual pre-HB rough insertion for the six new positive original U7/U8/U9
smoothings. This applies the existing original chart-cutoff theorem, not
a replacement cutoff. One threshold precedes every legal smoothing width,
source/branch label, original chart and prime word. No rho support, density,
arithmetic-mode bound or new smooth-family licence is assumed.
-/

namespace ImbalancedChen.P5OriginalU789SmoothChartRoughOne

noncomputable section
open Classical Filter
open scoped BigOperators
open P5OriginalU789SmoothLogSources
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.IndependentTestPrimeChartUniformCutoff
open P5Z.OriginalPrimeAtlasReserveBranches
open Part3.AllKLambdaChartCorrection Part3.OriginalProperPowerActualChart

/-- Exactly the actual two U7 sources, one U8 source and three U9 labels. -/
inductive Source
  | u7Prime
  | u7Semiprime
  | u8
  | u9 (branch : Fin 3)

def rank : Source → ℕ
  | .u7Prime => 3
  | .u7Semiprime => 4
  | .u8 => 3
  | .u9 _ => 3

def sourceWeight (s : Source) (N : ℕ) (width : ℝ) :
    (Fin (rank s) → Fin (N + 1)) → ℝ :=
  match s with
  | .u7Prime => fun u => physicalOuter7Three N width (logPoint u)
  | .u7Semiprime => fun u => physicalOuter7Four N width (logPoint u)
  | .u8 => fun u => physicalOuter8 N width (logPoint u)
  | .u9 j => fun u => physicalOuter9 j N width (logPoint u)

def primeWord {k N : ℕ} (u : Fin k → Fin (N + 1)) : List ℕ :=
  List.ofFn (fun i => (u i).val)

theorem source_prime_floor {N : ℕ} (hN : 2 ≤ N) {width : ℝ}
    (hw : 0 < width) (hwidth : width ≤ maximumWidth)
    (s : Source) {u : Fin (rank s) → Fin (N + 1)}
    (hu : u ∈ Part3.labelledPrimeTuples (rank s) N) (hs : sourceWeight s N width u ≠ 0) :
    ∀ p ∈ primeWord u, (N : ℝ) ^ commonPrimeFloor ≤ (p : ℝ) ∧ (p : ℝ) ≤ N := by
  have hfloor : ∀ i, (N : ℝ) ^ commonPrimeFloor < ((u i).val : ℝ) := by
    have h := actual_smoothing_prime_support hN hw hwidth
    cases s with
    | u7Prime => exact (h.1 u hu hs).1
    | u7Semiprime => exact (h.2.1 u hu hs).1
    | u8 => exact (h.2.2.1 u hu hs).1
    | u9 j => exact (h.2.2.2 j u hu hs).1
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
  subst p
  exact ⟨(hfloor i).le, by exact_mod_cast Nat.le_of_lt_succ (u i).isLt⟩

/-- The full original chart window is supplied by the actual psi profile.
The only fixed rank choice is K>=4, made before N and all source labels. -/
theorem exists_actual_chart_rough_one (K : ℕ) (hK : 4 ≤ K) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ width : ℝ,
      0 < width → width ≤ maximumWidth → ∀ s : Source,
      ∀ js ∈ chartBank N (rank s), ∀ u ∈ Part3.labelledPrimeTuples (rank s) N,
      sourceWeight s N width u ≠ 0 →
      tupleProfile P5Z.ActualEtaPsiOccurrenceBudget.chi js (primeWord u) ≠ 0 →
      roughWord (beforeHBCutoff K js) (primeWord u) = 1 := by
  obtain ⟨N0, hcut⟩ := independent_test_chart_cutoff_eventual K commonPrimeFloor
    (by norm_num [commonPrimeFloor])
  refine ⟨max 2 N0, ?_⟩
  intro N hN width hw hwidth s js hjs u hu hs hprofile
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN0 : N0 ≤ N := (le_max_right _ _).trans hN
  have hsource := source_prime_floor hN2 hw hwidth s hu hs
  have hlen : js.length = rank s := (words_spec _ _ _ hjs).1
  have hwindow := profile_nonzero_support P5Z.ActualEtaPsiOccurrenceBudget.chi
    (fun t ht => actual_chi_one ht) (fun t ht => actual_chi_zero ht) js (primeWord u) hprofile
  have hrank1 : 1 ≤ rank s := by cases s <;> norm_num [rank]
  have hrankK : rank s ≤ K := by cases s <;> simp only [rank] <;> omega
  have hrough := hcut N hN0 (rank s) hrank1 hrankK P5Z.ActualEtaPsiOccurrenceBudget.chi
    js (primeWord u) hlen hwindow hsource
  have hprime : primeOnly (primeWord u) := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    subst p
    exact (Finset.mem_filter.mp hu).2 i
  exact roughWord_one_on_prime_word _ hprime
    (fun p hp => hrough.trans_le (hsource p hp).1)

/-- The actual whole finite chart/label correction is zero even with any
additional smooth trim and the complete signed modulus kernel. F is kept
arbitrary because each summand is annihilated, not estimated separately.
This is an exact correction payment, not a retained-mode PP estimate. -/
theorem eventually_actual_full_chart_correction_zero (K : ℕ) (hK : 4 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, 0 < width → width ≤ maximumWidth →
      ∀ s : Source, ∀ F : List ℕ → (Fin (rank s) → Fin (N + 1)) → ℂ,
      (∑ js ∈ chartBank N (rank s), ∑ u ∈ Part3.labelledPrimeTuples (rank s) N,
        (sourceWeight s N width u : ℂ) *
          tupleProfile P5Z.ActualEtaPsiOccurrenceBudget.chi js (primeWord u) *
          (1 - roughWord (beforeHBCutoff K js) (primeWord u)) * F js u) = 0 := by
  obtain ⟨N0, hzero⟩ := exists_actual_chart_rough_one K hK
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro width hw hwidth s F
  apply Finset.sum_eq_zero
  intro js hjs
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hs : sourceWeight s N width u = 0
  · simp only [hs, Complex.ofReal_zero, zero_mul]
  by_cases ht : tupleProfile P5Z.ActualEtaPsiOccurrenceBudget.chi js (primeWord u) = 0
  · simp only [ht, mul_zero, zero_mul]
  rw [hzero N hN width hw hwidth s js hjs u hu hs ht]
  simp only [sub_self, mul_zero, zero_mul]

end
end ImbalancedChen.P5OriginalU789SmoothChartRoughOne
