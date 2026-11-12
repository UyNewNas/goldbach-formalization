import ImbalancedChen.Part5OriginalH430ClassicalSmoothDyadicFamily
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Fixed real scalar factors used by the classical word. In an Euler chart
each logarithmic factor is affine. Each physical radial or floor factor
is a scalar smooth plateau of an affine logarithm. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds
noncomputable section
open Finset Set Filter Real Wu2008DoubleSieve
open P4B
open Part5OriginalH430ClassicalSmoothOuterWeight (floorGate thinGate radialGate)
open scoped Classical Topology BigOperators ContDiff

abbrev E (d : ℕ) := Fin d → ℝ

/-- Bounds at every mixed order, uniform in the chart parameters. -/
def BoundedDerivatives {ι : Type*} {d : ℕ} (F : ι → E d → ℝ) : Prop :=
  (∀ i,ContDiff ℝ ∞ (F i)) ∧
    ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ i x,‖iteratedFDeriv ℝ n (F i) x‖≤C

def ScalarBound (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ x,|iteratedDeriv n f x|≤C

theorem step_bound {w : ℝ} (hw : 0<w) : ScalarBound (smoothGateUpperStep w) := by
  refine ⟨contDiff_smoothGateUpperStep _,?_⟩
  intro n
  obtain ⟨A,hA,H⟩ := exists_smoothGateUpperStep_derivative_budget n
  exact ⟨A/w^n,div_nonneg (zero_le_one.trans hA) (pow_nonneg hw.le n),H w hw⟩

private theorem plateau_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ∀x,|f x|≤1)
    {l u v w : ℝ} (hl : ∀x,x≤l → f x=v) (hu : ∀x,u≤x → f x=w) : ScalarBound f := by
  refine ⟨hf,?_⟩
  intro n
  cases n with
  | zero => exact ⟨1,zero_le_one,by simpa only [iteratedDeriv_zero] using hb⟩
  | succ m =>
    have hcont := ContDiff.continuous_iteratedDeriv' (m+1) (hf.of_le (by simp))
    obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max 0 B,le_max_left _ _,?_⟩
    intro x
    by_cases hx : x<l
    · have hlocal : f=ᶠ[𝓝 x](fun _ => v) := (Iio_mem_nhds hx).mono (fun p hp => hl p hp.le)
      rw [hlocal.iteratedDeriv_eq (m+1),iteratedDeriv_const,if_neg (by omega),abs_zero]
      exact le_max_left _ _
    by_cases hx' : u<x
    · have hlocal : f=ᶠ[𝓝 x](fun _ => w) := (Ioi_mem_nhds hx').mono (fun p hp => hu p hp.le)
      rw [hlocal.iteratedDeriv_eq (m+1),iteratedDeriv_const,if_neg (by omega),abs_zero]
      exact le_max_left _ _
    exact (show |iteratedDeriv (m+1) f x|≤B by
      simpa only [Real.norm_eq_abs] using hB x ⟨le_of_not_gt hx,le_of_not_gt hx'⟩).trans (le_max_right _ _)

theorem log_floor_bound : ScalarBound (fun u => floorGate (exp u)) := by
  apply plateau_bound (l:=log (1/2:ℝ)) (u:=0) (v:=0) (w:=1)
  · exact (contDiff_smoothGateUpperStep _).comp (contDiff_exp.sub contDiff_const)
  · intro x
    rw [abs_of_nonneg (smoothGateUpperStep_nonneg _ _)]
    exact smoothGateUpperStep_le_one _ _
  · intro x hx
    apply smoothGateUpperStep_eq_zero (by norm_num)
    have h := exp_le_exp.mpr hx
    rw [exp_log (by norm_num : (0:ℝ)<1/2)] at h
    linarith only [h]
  · intro x hx
    apply smoothGateUpperStep_eq_one (by norm_num)
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)

private theorem log_upper_bound {w b : ℝ} (hw : 0<w) (hb : 0<b) :
    ScalarBound (fun u => smoothGateUpperStep w (b-exp u)) := by
  apply plateau_bound (l:=log b) (u:=log (b+w)) (v:=1) (w:=0)
  · exact (contDiff_smoothGateUpperStep _).comp (contDiff_const.sub contDiff_exp)
  · intro x
    rw [abs_of_nonneg (smoothGateUpperStep_nonneg _ _)]
    exact smoothGateUpperStep_le_one _ _
  · intro x hx
    apply smoothGateUpperStep_eq_one hw
    have h := exp_le_exp.mpr hx
    rw [exp_log hb] at h
    exact sub_nonneg.mpr h
  · intro x hx
    apply smoothGateUpperStep_eq_zero hw
    have h := exp_le_exp.mpr hx
    rw [exp_log (add_pos hb hw)] at h
    linarith only [h]

theorem log_thin_bound {c : ℝ} (hc : 0<c) : ScalarBound (fun u => thinGate c (exp u)) :=
  log_upper_bound (half_pos hc) (half_pos hc)

theorem log_radial_bound {h : ℝ} (hh : 0<h) : ScalarBound (fun u => radialGate h (exp u)) :=
  log_upper_bound hh zero_lt_one

theorem affine {ι : Type*} {d : ℕ} {f : ℝ → ℝ} (hf : ScalarBound f) (a λ : ι → ℝ)
    (L : E d →L[ℝ] ℝ) {R : ℝ} (hR : 0≤R) (hλ : ∀i,|λ i|≤R) :
    BoundedDerivatives (fun i x => f (a i+λ i*L x)) := by
  refine ⟨fun i => hf.1.comp (contDiff_const.add (contDiff_const.mul L.contDiff)),?_⟩
  intro n
  obtain ⟨A,hA,hfA⟩ := hf.2 n
  refine ⟨A*(R*‖L‖)^n,mul_nonneg hA (pow_nonneg (mul_nonneg hR (norm_nonneg _)) _),?_⟩
  intro i x
  let g := fun t : ℝ => f (a i+t)
  let M := (λ i) • L
  have hg : ContDiff ℝ ∞ g := hf.1.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ n (g ∘ M) x‖≤_
  rw [M.iteratedFDeriv_comp_right hg x (by simp)]
  have hnorm := (iteratedFDeriv ℝ n g (M x)).norm_compContinuousLinearMap_le (fun _ : Fin n => M)
  have heq := congrFun (iteratedDeriv_comp_const_add n f (a i)) (M x)
  have he : ‖iteratedFDeriv ℝ n g (M x)‖≤A := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,show iteratedDeriv n g (M x)=_ from heq]
    exact hfA _
  have hM : ‖M‖≤R*‖L‖ := by
    rw [show ‖M‖=|λ i|*‖L‖ by simp [M,Real.norm_eq_abs]]
    exact mul_le_mul_of_nonneg_right (hλ i) (norm_nonneg _)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (M x)‖*‖M‖^n := by
      simpa only [prod_const,card_univ,Fintype.card_fin] using hnorm
    _ ≤ _ := mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) hM n) (pow_nonneg (norm_nonneg _) n) hA

theorem one {ι : Type*} {d : ℕ} : BoundedDerivatives (fun _ : ι => fun _ : E d => (1:ℝ)) := by
  refine ⟨fun _ => contDiff_const,fun n => ⟨1,zero_le_one,?_⟩⟩
  intro _ x
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

theorem add {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}
    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :
    BoundedDerivatives (fun i x => F i x+G i x) := by
  refine ⟨fun i => (hF.1 i).add (hG.1 i),?_⟩
  intro n
  obtain ⟨B,hB,hf⟩ := hF.2 n
  obtain ⟨C,hC,hg⟩ := hG.2 n
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro i x
  change ‖iteratedFDeriv ℝ n (F i+G i) x‖≤_
  rw [iteratedFDeriv_add_apply ((hF.1 i).of_le (by simp)).contDiffAt ((hG.1 i).of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf i x) (hg i x))

theorem sub {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}
    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :
    BoundedDerivatives (fun i x => F i x-G i x) := by
  refine ⟨fun i => (hF.1 i).sub (hG.1 i),?_⟩
  intro n
  obtain ⟨B,hB,hf⟩ := hF.2 n
  obtain ⟨C,hC,hg⟩ := hG.2 n
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro i x
  change ‖iteratedFDeriv ℝ n (F i-G i) x‖≤_
  rw [iteratedFDeriv_sub_apply ((hF.1 i).of_le (by simp)).contDiffAt ((hG.1 i).of_le (by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hf i x) (hg i x))

theorem mul {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}
    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :
    BoundedDerivatives (fun i x => F i x*G i x) := by
  refine ⟨fun i => (hF.1 i).mul (hG.1 i),?_⟩
  choose B hB hf using hF.2
  choose C hC hg using hG.2
  intro n
  refine ⟨∑ j∈range (n+1),(n.choose j:ℝ)*B j*C (n-j),
    sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hC _)),?_⟩
  intro i x
  have hle : ‖iteratedFDeriv ℝ n (fun y => F i y*G i y) x‖≤
      ∑ j∈range (n+1),(n.choose j:ℝ)*‖iteratedFDeriv ℝ j (F i) x‖*‖iteratedFDeriv ℝ (n-j) (G i) x‖ :=
    norm_iteratedFDeriv_mul_le (hF.1 i) (hG.1 i) x (by simp)
  apply hle.trans
  exact sum_le_sum (fun j _ => mul_le_mul (mul_le_mul_of_nonneg_left (hf j i x) (Nat.cast_nonneg _))
    (hg (n-j) i x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB j)))

theorem prod {ι σ : Type*} [DecidableEq σ] {d : ℕ} (S : Finset σ) (F : σ → ι → E d → ℝ)
    (hF : ∀ j,BoundedDerivatives (F j)) :
    BoundedDerivatives (fun i x => ∏ j∈S,F j i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using (one (ι:=ι) (d:=d))
  | @insert j S hj ih => simpa only [prod_insert hj] using mul (hF j) ih

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds

