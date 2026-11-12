import ImbalancedChen.Part3ActualMarkedHorocycleSupport
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Laplace continuation and the physical angular Fourier boundary for
the logarithmic horocycle average of a compact quotient packet. -/
namespace ImbalancedChen.Part3.LogHorocycleLaplaceBoundary20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
open AngularFourierUnitary20261026b HeightMellinUnitary20261026b
open ActualCriticalCuspEvaluation20261110

def kernel (s : ℂ) (u : ℝ) := Complex.exp ((s-1/2)*(u : ℂ))
def laplace (H : ℝ → ℂ) (s : ℂ) := ∫ u, kernel s u*star (H u)

private theorem kernel_norm (s : ℂ) (u : ℝ) :
    ‖kernel s u‖ = Real.exp ((s.re-1/2)*u) := by
  simp [kernel,Complex.norm_exp,Complex.re_mul_ofReal]

theorem weight_l1 {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) {a : ℝ} (ha : 0 < a) :
    Integrable (fun u => Real.exp (a*u)*‖H u‖) := by
  let W := (Iic A).indicator (fun u : ℝ => Real.exp (a*u))
  have wm : AEStronglyMeasurable W volume := (by fun_prop : Continuous (fun u : ℝ => Real.exp (a*u))).aestronglyMeasurable.indicator measurableSet_Iic
  have hW : MemLp W 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm wm).mpr
    apply ((integrableOn_exp_mul_Iic (show 0 < 2*a by positivity) A).integrable_indicator measurableSet_Iic).congr
    exact ae_of_all _ (fun u => by
      by_cases h : u ≤ A
      · simp only [W,indicator_of_mem (show u ∈ Iic A from h),Real.norm_of_nonneg (Real.exp_pos _).le,
          pow_two,← Real.exp_add]
        congr 1 <;> ring
      · simp [W,h])
  exact (hW.integrable_mul hH.norm).congr (ae_of_all _ (fun u => by
    by_cases hu : u ≤ A
    · simp [W,hu]
    · simp [W,hu,hA u (lt_of_not_ge hu)]))

theorem laplace_integrable {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) {s : ℂ} (hs : 1/2 < s.re) :
    Integrable (fun u => kernel s u*star (H u)) := by
  apply (weight_l1 hH hA (sub_pos.mpr hs)).mono'
    ((by fun_prop [kernel] : Continuous (kernel s)).aestronglyMeasurable.mul hH.1.star)
  exact ae_of_all _ (fun u => by rw [norm_mul,norm_star,kernel_norm])

private theorem derivative_weight {a b d x : ℝ} (hd : 0 < d) (h₁ : a ≤ x) (h₂ : x ≤ b) (u : ℝ) :
    |u|*Real.exp (x*u) ≤ d⁻¹*(Real.exp ((a-d)*u)+Real.exp ((b+d)*u)) := by
  rw [← div_eq_inv_mul,le_div_iff₀ hd]
  rcases le_total 0 u with h|h
  · rw [abs_of_nonneg h]
    have hW : d*u ≤ Real.exp (d*u) := by linarith [Real.add_one_le_exp (d*u)]
    have hM := mul_le_mul hW (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h₂ h))
      (Real.exp_pos (x*u)).le (Real.exp_pos _).le
    rw [← Real.exp_add,show d*u+b*u = (b+d)*u by ring] at hM
    nlinarith only [hM,(Real.exp_pos ((a-d)*u)).le]
  · rw [abs_of_nonpos h]
    have hW : d*(-u) ≤ Real.exp ((-d)*u) := by linarith [Real.add_one_le_exp ((-d)*u)]
    have hM := mul_le_mul hW (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right h₁ h))
      (Real.exp_pos (x*u)).le (Real.exp_pos _).le
    rw [← Real.exp_add,show (-d)*u+a*u = (a-d)*u by ring] at hM
    nlinarith only [hM,(Real.exp_pos ((b+d)*u)).le]

theorem laplace_differentiable {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) {s : ℂ} (hs : 1/2 < s.re) :
    DifferentiableAt ℂ (laplace H) s := by
  let d := (s.re-1/2)/4
  have hd : 0 < d := by dsimp [d]; linarith
  let U := {w : ℂ | 2*d < w.re-1/2 ∧ w.re-1/2 < 6*d}
  have hU : U ∈ 𝓝 s := ((isOpen_lt continuous_const (Complex.continuous_re.sub continuous_const)).inter
    (isOpen_lt (Complex.continuous_re.sub continuous_const) continuous_const)).mem_nhds
      (show s ∈ U by change 2*d < s.re-1/2 ∧ s.re-1/2 < 6*d; dsimp [d]; constructor <;> linarith)
  let F := fun w u => kernel w u*star (H u)
  let D := fun w u => (u : ℂ)*F w u
  have M (w : ℂ) : AEStronglyMeasurable (F w) volume :=
    (by fun_prop [kernel] : Continuous (kernel w)).aestronglyMeasurable.mul hH.1.star
  have Hder (w : ℂ) (u : ℝ) : HasDerivAt (fun v => F v u) (D w u) w := by
    have T := ((((hasDerivAt_id w).sub_const (1/2 : ℂ)).mul_const (u : ℂ)).cexp).mul_const (star (H u))
    convert T using 1 <;> simp [F,D,kernel] <;> ring
  let B := fun u => d⁻¹*(Real.exp (d*u)*‖H u‖+Real.exp ((7*d)*u)*‖H u‖)
  have hB : Integrable B := ((weight_l1 hH hA hd).add
    (weight_l1 hH hA (show 0 < 7*d by positivity))).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D) hU
    (Eventually.of_forall M) (laplace_integrable hH hA hs)
    (Complex.continuous_ofReal.aestronglyMeasurable.mul (M s)) _ hB
    (ae_of_all _ (fun u w _ => Hder w u))).2.differentiableAt
  exact ae_of_all _ (fun u w hw => by
    obtain ⟨l,r⟩ := hw
    have J := mul_le_mul_of_nonneg_right (derivative_weight hd l.le r.le u) (norm_nonneg (H u))
    rw [show 2*d-d=d by ring,show 6*d+d=7*d by ring] at J
    simpa only [D,F,B,norm_mul,kernel_norm,Complex.norm_real,Real.norm_eq_abs,norm_star,
      mul_add,add_mul,mul_assoc] using J)

def step (n : ℕ) : ℝ := 1/((n : ℝ)+1)
theorem step_pos (n : ℕ) : 0 < step n := by unfold step; positivity
theorem step_le (n : ℕ) : step n ≤ 1 := by
  rw [step,div_le_one (by positivity)]
  linarith only [Nat.cast_nonneg (R := ℝ) n]
theorem step_zero : Tendsto step atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

private def damp (H : ℝ → ℂ) (n : ℕ) (u : ℝ) := (Real.exp (step n*u) : ℂ)*H u

private theorem damp_bound {H : ℝ → ℂ} {A : ℝ} (hA : ∀ u, A < u → H u=0) (n : ℕ) (u : ℝ) :
    ‖damp H n u‖ ≤ Real.exp (max A 0)*‖H u‖ := by
  by_cases hu : u ≤ A
  · rw [damp,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (hu.trans (le_max_left _ _)) (step_pos n).le).trans
      (mul_le_of_le_one_left (le_max_right A 0) (step_le n))
  · simp [damp,hA u (lt_of_not_ge hu)]

private theorem damp_mem {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) (n : ℕ) : MemLp (damp H n) 2 volume :=
  hH.of_le_mul ((by fun_prop : Continuous (fun u : ℝ => (Real.exp (step n*u) : ℂ))).aestronglyMeasurable.mul hH.1)
    (ae_of_all _ (damp_bound hA n))

private theorem damp_l1 {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) (n : ℕ) : Integrable (damp H n) := by
  apply (weight_l1 hH hA (step_pos n)).mono' (damp_mem hH hA n).1
  exact ae_of_all _ (fun u => by simp [damp,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le])

private theorem damp_strong {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) :
    Tendsto (fun n => (damp_mem hH hA n).toLp _) atTop (𝓝 (hH.toLp H)) := by
  let G := fun n u => ‖damp H n u-H u‖^2
  let B := (Real.exp (max A 0)+1)^2
  have H₀ (u : ℝ) : Tendsto (fun n => damp H n u) atTop (𝓝 (H u)) := by
    simpa [damp] using ((Complex.continuous_ofReal.tendsto _).comp
      (Real.continuous_exp.tendsto _ |>.comp (step_zero.mul_const u))).mul_const (H u)
  have hb (n : ℕ) (u : ℝ) : ‖G n u‖ ≤ B*‖H u‖^2 := by
    have T := (norm_sub_le _ _).trans (add_le_add_right (damp_bound hA n u) ‖H u‖)
    have T' : ‖damp H n u-H u‖ ≤ (Real.exp (max A 0)+1)*‖H u‖ := by linarith
    simpa only [G,B,Real.norm_of_nonneg (sq_nonneg _),mul_pow] using pow_le_pow_left₀ (norm_nonneg _) T' 2
  have D := tendsto_integral_of_dominated_convergence (fun u => B*‖H u‖^2)
    (fun n => ((damp_mem hH hA n).1.sub hH.1).norm.pow 2)
    (((memLp_two_iff_integrable_sq_norm hH.1).mp hH).const_mul B)
    (fun n => ae_of_all _ (hb n))
    (f := fun _ : ℝ => (0 : ℝ)) (ae_of_all _ (fun u => by
      simpa [G] using ((H₀ u).sub_const (H u)).norm.pow 2))
  have T : Tendsto (fun n => ∫ u,G n u) atTop (𝓝 0) := by simpa [G] using D
  rw [tendsto_iff_dist_tendsto_zero]
  have E (n : ℕ) : dist ((damp_mem hH hA n).toLp _) (hH.toLp H) =
      (∫ u,G n u)^((2:ℝ)⁻¹) := by
    rw [dist_eq_norm,← MemLp.toLp_sub,Lp.norm_toLp,toReal_eLpNorm ((damp_mem hH hA n).sub hH).1,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) ((damp_mem hH hA n).sub hH).1]
    norm_num [G]
  simp_rw [E]
  simpa using (Real.continuousAt_rpow_const 0 ((2 : ℝ)⁻¹) (.inr (by norm_num))).tendsto.comp T

private theorem angular_damp (H : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    angularTransform (damp H n) t = star (laplace H (criticalPoint t + (step n : ℂ))) := by
  rw [laplace,Complex.star_def,← integral_conj,angularTransform]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by
    simp only [damp,kernel,criticalPoint,map_mul,← Complex.exp_conj,Complex.star_def,Complex.conj_conj,
      map_sub,map_add,map_mul,map_div₀,map_ofNat,map_one,Complex.conj_ofReal,Complex.conj_I,
      Complex.ofReal_mul,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
    congr 2 <;> ring)

/-- A single increasing subsequence identifies the literal Laplace values
with the Fourier transform of the physical log-height representative. -/
theorem laplace_fourier_boundary {H : ℝ → ℂ} (hH : MemLp H 2 volume) {A : ℝ}
    (hA : ∀ u, A < u → H u=0) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ t ∂angularMeasure,
      Tendsto (fun n => star (laplace H (criticalPoint t + (step (k n) : ℂ)))) atTop
        (𝓝 (angularFourierUnitary (hH.toLp H) t)) := by
  have T := angularFourierUnitary.continuous.continuousAt.tendsto.comp (damp_strong hH hA)
  obtain ⟨k,hk,Hk⟩ := (tendstoInMeasure_of_tendsto_Lp T).exists_seq_tendsto_ae
  have W : ∀ᵐ t ∂angularMeasure, ∀ n, angularFourierUnitary ((damp_mem hH hA n).toLp _) t =
      star (laplace H (criticalPoint t + (step n : ℂ))) :=
    ae_all_iff.mpr (fun n => (angularFourierUnitary_toLp_ae (damp_l1 hH hA n) (damp_mem hH hA n)).trans
      (ae_of_all _ (fun t => angular_damp H n t)))
  refine ⟨k,hk,?_⟩
  filter_upwards [W,Hk] with t ht hj
  simpa only [ht,Function.comp_apply] using hj

end
end ImbalancedChen.Part3.LogHorocycleLaplaceBoundary20261112
