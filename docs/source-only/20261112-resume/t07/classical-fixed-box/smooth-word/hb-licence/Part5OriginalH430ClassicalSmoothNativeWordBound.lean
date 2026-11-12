import ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerConjugacy

/-! Each actual original occurrence has a bound in the native Euler word
notation before the target, including points outside the positive orthant. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeWordBound
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5Z.AdmissibleAllRankIntegerGeometricFamily (eulerWord)
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothOuterWeight
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalSmoothEulerBounds (E BoundedDerivatives ScalarBound)
open Part5OriginalH430ClassicalSmoothEulerProfile
open Part5OriginalH430ClassicalSmoothRealProfile (raw raw_smooth raw_support)
open Part5OriginalH430ClassicalSmoothEulerConjugacy (flow norm_bound_at_zero)
open scoped Classical Topology BigOperators ContDiff

def rawChart {s r : ℕ} (C : Fin s → ℕ) (ν δ h c : ℝ) (a : Param (rank s r)) (u : E (rank s r)) :=
  outerWeight C ν δ h c (logCoords a u) (ratios a u) (radial a u)

private theorem radial_derivatives {k : ℕ} {f : ℝ → ℝ} (hf : ScalarBound (fun x => f (exp x))) :
    BoundedDerivatives (fun (a : Param k) u => f (radial a u)) := by
  let L : E k →L[ℝ] ℝ := ∑ i : Fin k,coord i
  have H := Part5OriginalH430ClassicalSmoothEulerBounds.affine hf
    (fun a : Param k => (∑ i,a.2 i)-log (a.1.val:ℝ)) (fun _ => (1:ℝ)) L
    zero_le_one (fun _ => by norm_num)
  have he (a : Param k) (u : E k) :
      exp (((∑ i,a.2 i)-log (a.1.val:ℝ))+1*L u)=radial a u := by
    apply congrArg exp
    simp [L,coord,ContinuousLinearMap.sum_apply,sum_add_distrib] <;> ring
  simpa only [he] using H

theorem raw_chart_budget {s r : ℕ} (C : Fin s → ℕ) (ν : ℝ) {δ h c : ℝ}
    (hd : 0<δ) (hh : 0<h) (hc : 0<c) :
    BoundedDerivatives (fun (a : Param (rank s r)) u => rawChart C ν δ h c a u) :=
  Part5OriginalH430ClassicalSmoothEulerBounds.mul (floor_budget (s:=s) (r:=r))
    (Part5OriginalH430ClassicalSmoothEulerBounds.add
      (radial_derivatives (Part5OriginalH430ClassicalSmoothEulerBounds.log_thin_bound hc))
      (Part5OriginalH430ClassicalSmoothEulerBounds.mul
        (Part5OriginalH430ClassicalSmoothEulerBounds.sub Part5OriginalH430ClassicalSmoothEulerBounds.one
          (radial_derivatives (Part5OriginalH430ClassicalSmoothEulerBounds.log_thin_bound hc)))
        (Part5OriginalH430ClassicalSmoothEulerBounds.mul
          (radial_derivatives (Part5OriginalH430ClassicalSmoothEulerBounds.log_radial_bound hh))
          (gate_budget C ν hd))))

theorem physical_flow {s r N : ℕ} (hN : 2≤N) (C : Fin s → ℕ) (ν δ h c : ℝ)
    (v : E (rank s r)) (hp : ∀i,0<v i) (u : E (rank s r)) :
    raw N C ν δ h c (flow v u)=rawChart C ν δ h c (⟨N,hN⟩,fun i => log (v i)) u := by
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hs (i) : flow v u i=exp (log (v i)+u i) := by rw [exp_add,exp_log (hp i)] <;> rfl
  have hlog (i) : log (flow v u i)=log (v i)+u i := by rw [hs i,log_exp]
  have hrat (i) : flow v u i/(N:ℝ)^(1/90:ℝ)=exp (log (v i)+u i-(1/90)*log (N:ℝ)) := by
    rw [hs i,exp_sub,rpow_def_of_pos h0,mul_comm (1/90:ℝ) (log (N:ℝ))]
  have hprod : (∏i,flow v u i)/(N:ℝ)=radial (⟨N,hN⟩,fun i => log (v i)) u := by
    rw [radial,exp_sub,exp_log h0,Real.exp_sum]
    simp only [hs]
  unfold raw rawChart
  simp only [hlog,hrat,hprod,logCoords,ratios]

theorem native_word_bound {s r : ℕ} (C : Fin s → ℕ) (ν : ℝ) {δ h c : ℝ}
    (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8) (m : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ N : ℕ,2≤N → ∀ w : List (Fin (rank s r)),w.length≤m →
      ∀ v : E (rank s r),|eulerWord w (raw N C ν δ h c) v|≤B := by
  choose A hA hbound using (raw_chart_budget (r:=r) C ν hd hh hc).2
  refine ⟨∑ n∈range (m+1),A n,sum_nonneg (fun n _ => hA n),?_⟩
  intro N hN w hlen v
  have H := norm_bound_at_zero (raw_smooth hN C ν δ h c) w v
  apply H.trans
  by_cases hpos : ∀i,0<v i
  · have he := funext (physical_flow hN C ν δ h c v hpos)
    rw [he]
    exact (hbound w.length (⟨N,hN⟩,fun i => log (v i)) 0).trans
      (single_le_sum (fun d _ => hA d) (mem_range.mpr (Nat.lt_succ_of_le hlen)))
  · push_neg at hpos
    obtain ⟨i,hi⟩ := hpos
    have hzero : (fun u => raw N C ν δ h c (flow v u))=fun _ => (0:ℝ) := by
      funext u
      by_contra hn
      have hfl := (raw_support hN hh hh' hc hc' hn).1 i
      have hApos := half_pos (rpow_pos_of_pos (Nat.cast_pos.mpr (show 0<N by omega)) (1/90:ℝ))
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hi (exp_pos (u i)).le)) (hApos.trans hfl)
    rw [hzero,iteratedFDeriv_fun_zero]
    simpa only [Pi.zero_apply,norm_zero] using sum_nonneg (s:=range (m+1)) (fun n _ => hA n)

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeWordBound

