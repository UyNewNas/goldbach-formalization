import ImbalancedChen.Part5OriginalH430ClassicalSmoothRealProfile

/-! Actual coordinate Euler operators of the original all-rank licence,
in the order of its List.foldr and including repeated coordinates. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerConjugacy
noncomputable section
open Finset Real
open P5Z.AdmissibleAllRankIntegerGeometricFamily (eulerOne eulerWord)
open Part5OriginalH430ClassicalSmoothEulerBounds (E)
open Part5OriginalH430ClassicalSmoothEulerProfile (coord)
open scoped Classical BigOperators Topology ContDiff

def unit {k : ℕ} (i : Fin k) : E k := fun j => if j=i then 1 else 0
def flow {k : ℕ} (v u : E k) (i : Fin k) := v i*exp (u i)
def jac {k : ℕ} (v u : E k) : E k →L[ℝ] E k :=
  ContinuousLinearMap.pi (fun i => flow v u i • coord i)

theorem unit_norm {k : ℕ} (i : Fin k) : ‖unit i‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases hj : j=i <;> simp [unit,hj]

theorem single_eq {k : ℕ} (z : E k) (i : Fin k) : Pi.single i (z i)=z i • unit i := by
  funext j
  by_cases hj : j=i
  · subst j; simp [unit]
  · simp [Pi.single_eq_of_ne hj,unit,hj]

theorem flow_smooth {k : ℕ} (v : E k) : ContDiff ℝ ∞ (flow v) :=
  contDiff_pi.mpr (fun i => contDiff_const.mul (contDiff_apply ℝ ℝ i).exp)

theorem flow_deriv {k : ℕ} (v u : E k) : HasFDerivAt (flow v) (jac v u) u := by
  apply hasFDerivAt_pi.mpr
  intro i
  simpa only [flow,jac,coord,smul_smul] using
    ((hasFDerivAt_apply (𝕜:=ℝ) i u).exp.const_mul (v i))

theorem jac_unit {k : ℕ} (v u : E k) (i : Fin k) :
    jac v u (unit i)=Pi.single i (flow v u i) := by
  rw [single_eq]
  funext j
  by_cases hj : j=i
  · subst j; simp [jac,coord,unit]
  · simp [jac,coord,unit,hj]

theorem word_smooth {k : ℕ} {F : E k → ℝ} (hF : ContDiff ℝ ∞ F) (w : List (Fin k)) :
    ContDiff ℝ ∞ (eulerWord w F) := by
  induction w with
  | nil => exact hF
  | cons i w ih =>
    change ContDiff ℝ ∞ (fun u => fderiv ℝ (eulerWord w F) u (Pi.single i (u i)))
    have hEq : (fun u : E k => Pi.single i (u i))=(fun u : E k => u i • unit i) :=
      funext (fun u => single_eq u i)
    have hv : ContDiff ℝ ∞ (fun u : E k => Pi.single i (u i)) := by
      rw [hEq]
      exact (contDiff_apply ℝ ℝ i).smul contDiff_const
    exact (ih.fderiv_right (by simp)).clm_apply hv

def directions {k : ℕ} : (w : List (Fin k)) → Fin w.length → E k
  | [], j => Fin.elim0 j
  | i::w, j => Fin.cons (unit i) (directions w) j

theorem direction_norm {k : ℕ} (w : List (Fin k)) (i : Fin w.length) :
    ‖directions w i‖≤1 := by
  induction w with
  | nil => exact Fin.elim0 i
  | cons j w ih =>
    refine Fin.cases (unit_norm j) (fun i => ih i) i

/-- Pull each physical Euler operator back to the actual multiplicative
flow. This identity also holds when a base coordinate is zero or negative. -/
theorem word_chart {k : ℕ} {F : E k → ℝ} (hF : ContDiff ℝ ∞ F)
    (w : List (Fin k)) (v u : E k) :
    eulerWord w F (flow v u)=iteratedFDeriv ℝ w.length (fun z => F (flow v z)) u (directions w) := by
  have hg := hF.comp (flow_smooth v)
  induction w generalizing u with
  | nil => simp [eulerWord]
  | cons i w ih =>
    let H := eulerWord w F
    have hH : ContDiff ℝ ∞ H := word_smooth hF w
    have hchain := (hH.differentiable (by simp) (flow v u)).hasFDerivAt.comp u (flow_deriv v u)
    have he : (fun z => H (flow v z)) =
        (fun z => iteratedFDeriv ℝ w.length (fun y => F (flow v y)) z (directions w)) :=
      funext (fun z => ih z)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length (fun z => F (flow v z))) u :=
      hg.contDiffAt.differentiableAt_iteratedFDeriv (by simp)
    have head : eulerOne i H (flow v u) =
        fderiv ℝ (fun z => H (flow v z)) u (unit i) := by
      rw [hchain.fderiv,ContinuousLinearMap.comp_apply,jac_unit] <;> rfl
    change eulerOne i H (flow v u)=_
    rw [head,he]
    symm
    simpa only [List.length_cons,directions,Fin.cons_zero,Fin.tail_cons] using
      (hd.iteratedFDeriv_succ_apply_left' (m:=Fin.cons (unit i) (directions w)))

theorem norm_bound_at_zero {k : ℕ} {F : E k → ℝ} (hF : ContDiff ℝ ∞ F)
    (w : List (Fin k)) (v : E k) :
    |eulerWord w F v|≤‖iteratedFDeriv ℝ w.length (fun z => F (flow v z)) 0‖ := by
  have hv : flow v 0=v := by funext i; simp [flow]
  have he := word_chart hF w v 0
  rw [hv] at he
  rw [he]
  let D := iteratedFDeriv ℝ w.length (fun z => F (flow v z)) 0
  have h := D.le_opNorm (directions w)
  have hm : (∏ i,‖directions w i‖)≤1 :=
    prod_le_one (fun i _ => norm_nonneg _) (fun i _ => direction_norm w i)
  exact (by simpa only [Real.norm_eq_abs] using h :
    |D (directions w)|≤‖D‖*∏ i,‖directions w i‖).trans
      ((mul_le_mul_of_nonneg_left hm (norm_nonneg D)).trans_eq (mul_one _))

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerConjugacy

