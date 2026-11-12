import ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeSignedSum
import ImbalancedChen.P4BOriginalFiniteProperArithmetic
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches

/-! Bounds for the actual labelled integer family prior to its HB expansion.
Each original position has weight at most one. The bank retains multiplicity. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalPowerProfile
noncomputable section
open Finset Real
open P5Z.AdmissibleAllRankIntegerGeometricFamily (Family licence)
open P5Z.ActualEtaPsiOccurrenceBudget (chi eta eta_bounds)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open Part3.OriginalProperPowerActualChart (wordVector)
open Part3.AllKFamilyLambdaCorrectionBound (bankWeight bankWeight_eq_ambient bankWeight_support)
open Part5OriginalH430ClassicalSmoothOuterWeight (outer_bounds)
open Part5OriginalH430ClassicalSmoothRealProfile (raw)
open Part5OriginalH430ClassicalSmoothAllOccurrences (Occurrence order lane ambient on_rank off_rank at_least_four)
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open scoped Classical BigOperators

def markBound : ℝ := Fintype.card Occurrence
theorem markBound_nonneg : 0≤markBound := Nat.cast_nonneg _

theorem ambient_bounds (μ δ h c : ℝ) (N : ℕ) (k : Fin 201) (x : Fin k.val → ℝ) :
    0≤ambient μ δ h c N k x ∧ ambient μ δ h c N k x≤markBound := by
  by_cases hn : 2≤N
  · simp only [ambient,if_pos hn]
    have H (o : Occurrence) : 0≤lane N μ δ h c o k x ∧ lane N μ δ h c o k x≤1 := by
      by_cases eq : k=order o
      · subst k
        rw [on_rank]
        exact outer_bounds _ _ _ _ _ _ _ _
      · simp [off_rank eq]
    exact ⟨sum_nonneg (fun o _ => (H o).1),
      (sum_le_sum (s:=univ) (fun o _ => (H o).2)).trans_eq (by simp [markBound])⟩
  · simp only [ambient,if_neg hn]
    exact ⟨le_rfl,markBound_nonneg⟩

variable (μ : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
local notation "F₀" => family μ hd hh hh' hc hc'

theorem word_amplitude (N : ℕ) (k : Fin 201) (ps : List ℕ) (hl : ps.length=k.val) :
    ‖bankWeight F₀ N k ps‖≤markBound := by
  rw [bankWeight_eq_ambient _ _ _ hl,Complex.norm_real,Real.norm_eq_abs]
  have H := ambient_bounds μ δ h c N k (fun i => (wordVector k.val ps i:ℝ))
  exact (abs_of_nonneg H.1).le.trans H.2

theorem too_short {N : ℕ} {k : Fin 201} (hk : k.val<4) {ps : List ℕ} (hl : ps.length=k.val) :
    bankWeight F₀ N k ps=0 := by
  rw [bankWeight_eq_ambient _ _ _ hl]
  change (ambient μ δ h c N k _ : ℂ)=0
  by_cases hn : 2≤N
  · rw [ambient,if_pos hn]
    have H (o : Occurrence) : k≠order o := by
      intro he
      have := at_least_four o
      rw [←he] at this
      omega
    apply Complex.ofReal_eq_zero.mpr
    exact sum_eq_zero (fun o _ => by rw [off_rank (H o)] <;> rfl)
  · simp [ambient,hn]

theorem chi_bounds (x : ℝ) : 0≤chi x ∧ chi x≤1 := by
  have H := eta_bounds x
  unfold chi
  constructor <;> linarith only [H.1,H.2]
theorem abs_eta (x : ℝ) : |eta x|≤1 := (abs_of_nonneg (eta_bounds x).1).le.trans (eta_bounds x).2

theorem chart_live {N : ℕ} {k : Fin 201} {κ₀ : ℝ} {js ps : List ℕ}
    (ha : originalChart (licence F₀ N k) N κ₀ js ps≠0) : bankWeight F₀ N k ps≠0 := by
  intro hw
  apply ha
  change tupleProfile chi js ps * ( _ * bankWeight F₀ N k ps)=0
  simp only [hw,mul_zero]

end
end ImbalancedChen.Part5OriginalH430ClassicalPowerProfile

