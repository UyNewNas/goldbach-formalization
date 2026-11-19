import ImbalancedChen.P4AOriginalElevenOwnCaps

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Quantization loss is paid on the actual initial rational profile, before
the reciprocal-prime prefix mass. Both residual denominators are bounded
below by the original sixth-coordinate cutoff. The actual fifth cap may
be smaller than the raw comparison; this increases the limiting saving.
-/
namespace ImbalancedChen.P4AOriginalElevenProfileQuantization
noncomputable section
open VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthMomentRow (Point cutoff)
open P1GuardFrozenFiniteCapAlgebra (rounded rounded_error)
open P4AOriginalFull87HistoryCore (width width_pos)
open Certificates.P2OriginalSixthElevenLogSemantics (S6 S6_eq_sum PhysicalCell oldCap newCap)

theorem profile_eq_reciprocals {P M : ℝ} {t : Point}
    (hP : P-S6 t≠0) (hM : M-S6 t≠0) :
    primeBoxInitialSavingProfile P M t=4/(P-S6 t)-4/(M-S6 t) := by
  simp only [primeBoxInitialSavingProfile,← S6_eq_sum]
  field_simp [hP,hM]
  <;> ring

/-- Pure cap algebra with an explicit error, not an assumed saving bound.
It retains the varying old cap P, comparison R and rounded new cap M. -/
theorem profile_quantization_lower (P R M V c w : ℝ) (t : Point)
    (hc : 0<c) (hP : 0<P-S6 t) (hPR : P≤R) (hcM : c≤M-S6 t)
    (hMV : M≤V) (hround : V-M≤2*w) :
    primeBoxInitialSavingProfile R V t-8*w/c^2≤primeBoxInitialSavingProfile P M t := by
  have hR : 0<R-S6 t := hP.trans_le (sub_le_sub_right hPR _)
  have hM : 0<M-S6 t := hc.trans_le hcM
  have hcV : c≤V-S6 t := hcM.trans (sub_le_sub_right hMV _)
  have hV : 0<V-S6 t := hc.trans_le hcV
  have hprod : c^2≤(M-S6 t)*(V-S6 t) := by
    simpa only [pow_two] using mul_le_mul hcM hcV hc.le hM.le
  have hcost : 4*(V-M)/((M-S6 t)*(V-S6 t))≤8*w/c^2 := by
    calc
      _ ≤ 4*(V-M)/c^2 := div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hMV)) (sq_pos_of_pos hc) hprod
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (sq_nonneg c)
  have hdiff : 4/(M-S6 t)-4/(V-S6 t)=4*(V-M)/((M-S6 t)*(V-S6 t)) := by
    field_simp [hM.ne',hV.ne']
    <;> ring
  have hparent : 4/(R-S6 t)≤4/(P-S6 t) :=
    div_le_div_of_nonneg_left (by norm_num) hP (sub_le_sub_right hPR _)
  rw [profile_eq_reciprocals hR.ne' hV.ne',profile_eq_reciprocals hP.ne' hM.ne']
  linarith

theorem original_profile_rounded_lower (n : ℕ)
    {c : Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point}
    (hc : PhysicalCell c t) {P M : ℝ}
    (hP : t 5<P-S6 t) (hPR : P≤oldCap c t) (hPM : P≤M)
    (heq : M=(rounded n (newCap c t):ℝ)) :
    primeBoxInitialSavingProfile (oldCap c t) (newCap c t) t-
      8*width n/cutoff^2≤primeBoxInitialSavingProfile P M t := by
  have hcut : 0<cutoff := by norm_num [cutoff]
  have hlow := P4AOriginalSixthActionBank.geometric_lower_license (.eleven c) t hc none
  change (1/2:ℝ)<newCap c t at hlow
  have hcap : newCap c t≤cap :=
    (P4AOriginalSixthActionBank.geometric_upper_license (.eleven c) t hc).trans (v_le_cap _)
  have hr := rounded_error n (newCap c t) (by linarith) hcap
  rw [← heq] at hr
  exact profile_quantization_lower P (oldCap c t) M (newCap c t) cutoff (width n) t
    hcut (hc.rpos.trans hP) hPR
    (hc.compactCutoff.le.trans (hP.le.trans (sub_le_sub_right hPM _)))
    hr.2.2 (by linarith [hr.1])

end
end ImbalancedChen.P4AOriginalElevenProfileQuantization
