import ImbalancedChen.P2HistoricalScheduledPointReads
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel

/-! The four old W1 tuples with S-S/s < 2 still admit a genuine source
comparison at the clamped target. Retain its actual delta-dependent cost. -/
namespace ImbalancedChen.P2HistoricalW1NativeClipping

noncomputable section
open MeasureTheory Wu2008DoubleSieve P2TableActionSourceOnly P2Historical248Authentication
open P2HistoricalScheduledPointReads P2HistoricalLowerBankAncestry
open scoped Interval

def clipped (s S : ℝ) : ℝ := max s (S/(S-2))

private theorem ratio_test {s S : ℝ} (hs : 0<s) (hS : 2<S) :
    S/(S-2) ≤ s ↔ 2 ≤ S-S/s := by
  calc
    S/(S-2) ≤ s ↔ S ≤ s*(S-2) := div_le_iff₀ (by linarith)
    _ ↔ S ≤ (S-2)*s := by rw [mul_comm s]
    _ ↔ S/s ≤ S-2 := (div_le_iff₀ hs).symm
    _ ↔ 2 ≤ S-S/s := by constructor <;> intro h <;> linarith

theorem clipped_start {s S : ℝ} (hs : 0<s) (hS : 2<S) :
    (1-1/clipped s S)*S = max 2 (S-S/s) := by
  have hSn : S≠0 := by linarith
  have hSm : S-2≠0 := by linarith
  unfold clipped
  by_cases h : 2≤S-S/s
  · rw [max_eq_left ((ratio_test hs hS).mpr h),max_eq_right h]
    field_simp [hs.ne'] <;> ring
  · have hc : s ≤ S/(S-2) := le_of_not_ge (fun q => h ((ratio_test hs hS).mp q))
    rw [max_eq_right hc,max_eq_left (le_of_not_ge h)]
    field_simp [hSn,hSm,div_ne_zero hSn hSm] <;> ring

theorem native_clipped_W1 {δ s S : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (hs : 2≤s) (hs' : s≤3) (hS : 3≤S) (hS' : S≤5) :
    firstFunctionalGainPsi δ (clipped s S) S + H δ S +
      (1/2)*(∫ u in (max 2 (S-S/s))..(S-1), h δ u * firstFeedbackWeightedKernel S u) ≤ H δ s := by
  have hmax : s≤clipped s S := le_max_left _ _
  have hmax' : clipped s S≤3 := max_le hs' ((div_le_iff₀ (by linarith : 0<S-2)).2 (by linarith))
  have hratio := (ratio_test (show 0<clipped s S by linarith) (by linarith : 2<S)).mp
    (le_max_right s (S/(S-2)))
  have hc := wuImprovementLimit_firstFunctionalGain hd hd' (hs.trans hmax) hmax' hS hS' hratio
  rw [firstFeedbackWeighted_substitution (g := wuImprovementLimit false δ) (by linarith : S≠0),
    clipped_start (by linarith : 0<s) (by linarith : 2<S),
    show (1-1/S)*S=S-1 by field_simp [show S≠0 by linarith] <;> ring] at hc
  exact hc.trans (wuImprovementLimit_upper_antitone hd hd' ⟨by linarith,by linarith⟩
    ⟨by linarith,by linarith⟩ hmax)

def basic (a : SourceW1) : Bool := decide (2≤a.s ∧ a.s≤3 ∧ 3≤a.s0 ∧ a.s0≤5)
private theorem original_domain : w1Original.all basic=true ∧ w1Retained.all basic=true := by decide

/-- This records only the four exceptional original parameter pairs. -/
theorem exceptional_raw_pairs :
    ((w1Original.filter (fun a => decide (a.s0-a.s0/a.s < 2))).map (fun a => (a.s,a.s0))) =
    [(12/5,16/5),(12/5,17/5),(5/2,16/5),(13/5,16/5)] := by decide

theorem all_W1_functions (g : ℕ) {a : SourceW1} (ha : a∈sourceW1Schedule g)
    {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10) :
    firstFunctionalGainPsi δ (clipped a.s a.s0) a.s0 + H δ a.s0 +
      (1/2)*(∫ u in (max 2 ((a.s0:ℝ)-(a.s0:ℝ)/(a.s:ℝ)))..((a.s0:ℝ)-1),
        h δ u*firstFeedbackWeightedKernel a.s0 u) ≤ H δ a.s := by
  have hm : (sourceW1Schedule g).all basic=true := by
    unfold sourceW1Schedule
    split <;> first | exact original_domain.1 | exact original_domain.2
  obtain ⟨hs,hs',hS,hS'⟩ := of_decide_eq_true (List.all_eq_true.mp hm a ha)
  exact native_clipped_W1 hd hd' (by exact_mod_cast hs) (by exact_mod_cast hs')
    (by exact_mod_cast hS) (by exact_mod_cast hS')

/-- The historical lower channel has literally zero on all cells strictly
below the admitted lower-side left end. -/
theorem original_lower_before_two (g : ℕ) (i : Fin 200) (hi : i.val<50) : outputAt g false i=0 := by
  cases g with
  | zero => rfl
  | succ n =>
    rw [show outputAt (n+1) false i = _ from iterate_lower_last_suffix designatedW1 designatedW2 n i]
    simp [show ¬50≤i.val by omega]

end
end ImbalancedChen.P2HistoricalW1NativeClipping
