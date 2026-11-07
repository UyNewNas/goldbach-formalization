import ImbalancedChen.P2EnhancedNegativeChildPhysicalSupport
import ImbalancedChen.P5OriginalFeedbackDomains

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Logarithmic coordinates of the independently defined original negative
prime windows. The lower endpoint is CLOSED in the arithmetic source.
Actual child level, query and alpha are computed from the same Q,d,p;
alpha is transported, never set to two. -/

namespace ImbalancedChen.P2EnhancedNegativeChildLogGeometry

noncomputable section
open scoped Classical
open Wu2008DoubleSieve P2EnhancedTwentyOneSameQWeighted
open P2EnhancedNegativeChildRosser (childLevel childCoefficient)
open P2OriginalNegativeSingleSameQSupport (negativeWindow negativeParameter lowerCutoff)

def relativeCoordinate (Q : ℝ) (d p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (Q / (d : ℝ))
def parentAlpha (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ := Real.log ((N : ℝ) / d) / Real.log (Q / d)
def childAlpha (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  Real.log ((N : ℝ) / ((d * p : ℕ) : ℝ)) / Real.log (childLevel Q d p)
def childQuery (Q : ℝ) (d p : ℕ) : ℝ :=
  Real.log (childLevel Q d p) / Real.log (cutoff Q d (227 / 50))

theorem actual_child_level_log {Q : ℝ} {d p : ℕ}
    (hR : 1 < Q / (d : ℝ)) (hp : p.Prime) :
    Real.log (childLevel Q d p) = Real.log (Q / (d : ℝ)) - Real.log (p : ℝ) := by
  unfold childLevel
  rw [Nat.cast_mul, ← div_div, Real.log_div (zero_lt_one.trans hR).ne'
    (Nat.cast_pos.mpr hp.pos).ne']

/-- The true arithmetic source maps to a CLOSED lower endpoint. Its
boundary cannot be silently declared an open feedback-domain point. -/
theorem actual_coordinate_bounds {N d p : ℕ} {Q : ℝ}
    (hR : 1 < Q / (d : ℝ)) (j : Fin 3) (hp : p ∈ negativeWindow N Q d j) :
    (50 / 227 : ℝ) ≤ relativeCoordinate Q d p ∧
      relativeCoordinate Q d p < 1 / negativeParameter j ∧
      0 < relativeCoordinate Q d p ∧ relativeCoordinate Q d p < 1 / 2 := by
  have hpData := mem_primeWindow.mp hp
  have hR0 := zero_lt_one.trans hR
  have hlog : 0 < Real.log (Q / (d : ℝ)) := Real.log_pos hR
  have ha0 : 0 < lowerCutoff Q d := Real.rpow_pos_of_pos hR0 _
  have hu0 : 0 < cutoff Q d (negativeParameter j) := Real.rpow_pos_of_pos hR0 _
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpData.1.pos
  have hlo := Real.log_le_log ha0 hpData.2.2.1
  have hhi := (Real.log_lt_log_iff hp0 hu0).mpr hpData.2.2.2
  rw [lowerCutoff, cutoff, Real.log_rpow hR0] at hlo
  rw [cutoff, Real.log_rpow hR0] at hhi
  have hlower : (50 / 227 : ℝ) ≤ relativeCoordinate Q d p := by
    apply (le_div_iff₀ hlog).mpr
    norm_num at hlo ⊢
    exact hlo
  have hupper : relativeCoordinate Q d p < 1 / negativeParameter j :=
    (div_lt_iff₀ hlog).mpr hhi
  have hcap : 1 / negativeParameter j < (1 / 2 : ℝ) := by
    fin_cases j <;> norm_num [negativeParameter]
  exact ⟨hlower, hupper, lt_of_lt_of_le (by norm_num) hlower, hupper.trans hcap⟩

/-- The original ordinary lower-child query is the actual log ratio,
with the original 227/50 profile rather than a reset argument. -/
theorem actual_child_query {N d p : ℕ} {Q : ℝ}
    (hR : 1 < Q / (d : ℝ)) (j : Fin 3) (hp : p ∈ negativeWindow N Q d j) :
    childQuery Q d p = (227 / 50 : ℝ) * (1 - relativeCoordinate Q d p) ∧
      2 < childQuery Q d p := by
  have hpData := mem_primeWindow.mp hp
  have hR0 := zero_lt_one.trans hR
  have hlog : Real.log (Q / (d : ℝ)) ≠ 0 := (Real.log_pos hR).ne'
  have heq : childQuery Q d p = (227 / 50 : ℝ) * (1 - relativeCoordinate Q d p) := by
    unfold childQuery relativeCoordinate
    rw [actual_child_level_log hR hpData.1, cutoff, Real.log_rpow hR0]
    field_simp [hlog] <;> ring
  have hcoord := actual_coordinate_bounds hR j hp
  have hmax : relativeCoordinate Q d p < (5 / 11 : ℝ) := by
    have hc : 1 / negativeParameter j ≤ (5 / 11 : ℝ) := by
      fin_cases j <;> norm_num [negativeParameter]
    exact hcoord.2.1.trans_le hc
  exact ⟨heq, by rw [heq]; linarith⟩

theorem parent_alpha_ge_one {N d : ℕ} {Q : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) (hQN : Q ≤ (N : ℝ)) :
    1 ≤ parentAlpha N Q d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hRN : Q / (d : ℝ) ≤ (N : ℝ) / d := div_le_div_of_nonneg_right hQN hdR.le
  have hl := Real.log_le_log (zero_lt_one.trans hR) hRN
  apply (le_div_iff₀ (Real.log_pos hR)).mpr
  simpa [parentAlpha] using hl

/-- Alpha>=2 is derived from the actual prefix physical half-source gate,
not supplied as a guessed child alpha. This gate is not asserted for an
arbitrary d from the finite mother count theorem. -/
theorem parent_alpha_ge_two_of_physical_gate {N d : ℕ} {Q : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) (hgate : Q ^ 2 ≤ (N : ℝ) * d) :
    2 ≤ parentAlpha N Q d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpow : (Q / (d : ℝ)) ^ 2 ≤ (N : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    calc
      (Q / (d : ℝ)) ^ 2 * d = Q ^ 2 / d := by field_simp [hdR.ne'] <;> ring
      _ ≤ N := (div_le_iff₀ hdR).mpr hgate
  have hlog := Real.log_le_log (sq_pos_of_pos (zero_lt_one.trans hR)) hpow
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ (Real.log_pos hR)).mpr
  simpa only [Nat.cast_ofNat, parentAlpha] using hlog

theorem actual_alpha_transport {N d p : ℕ} {Q : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) (hQN : Q ≤ (N : ℝ))
    (j : Fin 3) (hp : p ∈ negativeWindow N Q d j) :
    childAlpha N Q d p = 1 + (parentAlpha N Q d - 1) / (1 - relativeCoordinate Q d p) ∧
      parentAlpha N Q d ≤ childAlpha N Q d p := by
  have hpData := mem_primeWindow.mp hp
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hR0 := zero_lt_one.trans hR
  have hNdiv : 0 < (N : ℝ) / d := hR0.trans_le (div_le_div_of_nonneg_right hQN hdR.le)
  have hcoord := actual_coordinate_bounds hR j hp
  have hrest : 0 < 1 - relativeCoordinate Q d p := by linarith [hcoord.2.2.2]
  have hlog : Real.log (Q / (d : ℝ)) ≠ 0 := (Real.log_pos hR).ne'
  have hdiff : Real.log (Q / (d : ℝ)) - Real.log (p : ℝ) ≠ 0 := by
    have hu : Real.log (p : ℝ) < Real.log (Q / (d : ℝ)) := by
      have hh : relativeCoordinate Q d p < 1 := by linarith [hcoord.2.2.2]
      exact (div_lt_one (Real.log_pos hR)).mp hh
    exact (sub_pos.mpr hu).ne'
  have heq : childAlpha N Q d p =
      1 + (parentAlpha N Q d - 1) / (1 - relativeCoordinate Q d p) := by
    unfold childAlpha parentAlpha relativeCoordinate
    rw [actual_child_level_log hR hpData.1, Nat.cast_mul, ← div_div,
      Real.log_div hNdiv.ne' (Nat.cast_pos.mpr hpData.1.pos).ne']
    field_simp [hlog, hdiff] <;> ring
  refine ⟨heq, ?_⟩
  rw [heq]
  exact P5OriginalFeedbackDomains.alpha_transport_mono (parent_alpha_ge_one hd hR hQN)
    hrest (by linarith [hcoord.2.2.1])

/-- A physical old prefix admitting alpha>=2 gives that same property at
every actual negative child. No alpha reset is used. -/
theorem actual_child_alpha_ge_two {N d p : ℕ} {Q : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) (hQN : Q ≤ (N : ℝ))
    (hgate : Q ^ 2 ≤ (N : ℝ) * d) (j : Fin 3)
    (hp : p ∈ negativeWindow N Q d j) : 2 ≤ childAlpha N Q d p :=
  (parent_alpha_ge_two_of_physical_gate hd hR hgate).trans
    (actual_alpha_transport hd hR hQN j hp).2

end
end ImbalancedChen.P2EnhancedNegativeChildLogGeometry
