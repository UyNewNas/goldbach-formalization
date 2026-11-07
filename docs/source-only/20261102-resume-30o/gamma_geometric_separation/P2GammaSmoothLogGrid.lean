import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A concrete smooth logarithmic partition, with a proved fixed variation
budget.  There is no Fourier-separation premise.  The grid is chosen
before any arithmetic modulus, residue or character.  Its rows can be
used without Fourier integration: a finite counting measure is enough.
-/

namespace ImbalancedChen.P2GammaSmoothLogGrid
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

def hat (u : ℝ) : ℝ := Real.smoothTransition (u+1)-Real.smoothTransition u

theorem hat_nonneg (u : ℝ) : 0≤hat u :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem hat_le_one (u : ℝ) : hat u≤1 := by
  have h₁ := Real.smoothTransition.le_one (u+1)
  have h₀ := Real.smoothTransition.nonneg u
  dsimp [hat]
  linarith

theorem hat_eq_zero_of_le {u : ℝ} (hu : u≤-1) : hat u=0 := by
  rw [hat,Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]

theorem hat_eq_zero_of_one_le {u : ℝ} (hu : 1≤u) : hat u=0 := by
  rw [hat,Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le hu,sub_self]

theorem hat_nonzero_support {u : ℝ} (hu : hat u≠0) : -1<u ∧ u<1 := by
  constructor
  · by_contra h
    exact hu (hat_eq_zero_of_le (le_of_not_gt h))
  · by_contra h
    exact hu (hat_eq_zero_of_one_le (le_of_not_gt h))

theorem hat_contDiff : ContDiff ℝ ∞ hat :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem sum_hat (K : ℕ) (u : ℝ) :
    (∑ j∈Finset.range K,hat (u-(j : ℝ))) =
      Real.smoothTransition (u+1)-Real.smoothTransition (u+1-(K : ℝ)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ,ih,hat]
    have h₁ : u-(K : ℝ)+1=u+1-(K : ℝ) := by ring
    have h₂ : u+1-((K+1 : ℕ) : ℝ)=u-(K : ℝ) := by push_cast; ring
    rw [h₁,h₂]
    ring

theorem sum_hat_le_one (K : ℕ) (u : ℝ) :
    (∑ j∈Finset.range K,hat (u-(j : ℝ)))≤1 := by
  rw [sum_hat]
  have h₁ := Real.smoothTransition.le_one (u+1)
  have h₀ := Real.smoothTransition.nonneg (u+1-(K : ℝ))
  linarith

theorem sum_hat_eq_one {K : ℕ} {u : ℝ} (hu : 0≤u) (hK : u+1≤K) :
    (∑ j∈Finset.range K,hat (u-(j : ℝ)))=1 := by
  rw [sum_hat,Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

def lower (δ : ℝ) (j : ℕ) : ℝ := Real.exp (δ*((j : ℝ)-1))
def upper (δ : ℝ) (j : ℕ) : ℝ := Real.exp (δ*((j : ℝ)+1))
def weight (δ : ℝ) (j : ℕ) (p : ℝ) : ℝ := hat (Real.log p/δ-(j : ℝ))
def complexWeight (δ : ℝ) (j : ℕ) (p : ℝ) : ℂ := (weight δ j p : ℂ)

theorem lower_pos (δ : ℝ) (j : ℕ) : 0<lower δ j := Real.exp_pos _
theorem upper_pos (δ : ℝ) (j : ℕ) : 0<upper δ j := Real.exp_pos _
theorem weight_nonneg (δ : ℝ) (j : ℕ) (p : ℝ) : 0≤weight δ j p := hat_nonneg _
theorem weight_le_one (δ : ℝ) (j : ℕ) (p : ℝ) : weight δ j p≤1 := hat_le_one _

theorem complexWeight_norm_le_one (δ : ℝ) (j : ℕ) (p : ℝ) :
    ‖complexWeight δ j p‖≤1 := by
  rw [complexWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg _ _ _)]
  exact weight_le_one _ _ _

theorem weight_nonzero_support {δ p : ℝ} (hδ : 0<δ) (hp : 0<p)
    (j : ℕ) (hw : weight δ j p≠0) : lower δ j<p ∧ p<upper δ j := by
  obtain ⟨hl,hu⟩ := hat_nonzero_support hw
  have hl' : (j : ℝ)-1<Real.log p/δ := by linarith
  have hu' : Real.log p/δ<(j : ℝ)+1 := by linarith
  have hlogl := (lt_div_iff₀ hδ).mp hl'
  have hlogu := (div_lt_iff₀ hδ).mp hu'
  constructor
  · exact (Real.exp_lt_exp.mpr (by nlinarith : δ*((j : ℝ)-1)<Real.log p)).trans_eq
      (Real.exp_log hp)
  · rw [← Real.exp_log hp]
    exact Real.exp_lt_exp.mpr (by nlinarith)

theorem upper_eq_lower_mul (δ : ℝ) (j : ℕ) :
    upper δ j=lower δ j*Real.exp (2*δ) := by
  rw [upper,lower,← Real.exp_add]
  congr 1
  ring

theorem upper_le_two_lower {δ : ℝ} (hδ : 2*δ≤Real.log 2) (j : ℕ) :
    upper δ j≤2*lower δ j := by
  have h := Real.exp_le_exp.mpr hδ
  rw [Real.exp_log (by norm_num : (0 : ℝ)<2)] at h
  rw [upper_eq_lower_mul]
  nlinarith [lower_pos δ j]

theorem weight_sum_eq_one {δ p : ℝ} (hδ : 0<δ) (hp : 1≤p)
    {K : ℕ} (hK : Real.log p/δ+1≤K) :
    (∑ j∈Finset.range K,weight δ j p)=1 :=
  sum_hat_eq_one (div_nonneg (Real.log_nonneg hp) hδ.le) hK

theorem weight_sum_le_one (δ p : ℝ) (K : ℕ) :
    (∑ j∈Finset.range K,weight δ j p)≤1 := sum_hat_le_one _ _

private theorem transition_differentiable : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)

theorem hat_hasDerivAt (u : ℝ) :
    HasDerivAt hat
      (deriv Real.smoothTransition (u+1)-deriv Real.smoothTransition u) u := by
  simpa only [hat,one_mul,mul_one] using
    (((transition_differentiable (u+1)).hasDerivAt.comp u
      ((hasDerivAt_id u).add_const 1)).sub
        (transition_differentiable u).hasDerivAt

theorem exists_hat_derivative_bound :
    ∃ D : ℝ,1≤D ∧ ∀ u : ℝ,|deriv hat u|≤2*D := by
  obtain ⟨D,hD,hbase⟩ := P4B.exists_smoothTransition_global_derivative_bound 1
  refine ⟨D,hD,?_⟩
  intro u
  have h₁ : |deriv Real.smoothTransition (u+1)|≤D := by
    simpa only [iteratedDeriv_one] using hbase (u+1)
  have h₀ : |deriv Real.smoothTransition u|≤D := by
    simpa only [iteratedDeriv_one] using hbase u
  rw [(hat_hasDerivAt u).deriv]
  exact (abs_sub _ _).trans (by linarith)

theorem complexWeight_contDiffOn (δ : ℝ) (j : ℕ) :
    ContDiffOn ℝ 1 (complexWeight δ j) (Ioi (0 : ℝ)) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hl : ContDiffAt ℝ 1 Real.log p := Real.contDiffAt_log.mpr hp.ne'
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
    ((hat_contDiff.of_le (by norm_num)).contDiffAt.comp p
      ((hl.div_const δ).sub_const (j : ℝ)))

theorem complexWeight_hasDerivAt (δ : ℝ) (j : ℕ) {p : ℝ} (hp : 0<p) :
    HasDerivAt (complexWeight δ j)
      ((deriv hat (Real.log p/δ-(j : ℝ))/(δ*p) : ℝ) : ℂ) p := by
  have h := ((hat_hasDerivAt (Real.log p/δ-(j : ℝ))).comp p
    (((Real.hasDerivAt_log hp.ne').div_const δ).sub_const (j : ℝ))).ofReal_comp
  convert h using 1
  · rfl
  · congr 1
    ring

/-- Fixed derivative constant, then every physical interval and grid
parameter.  The norm is exactly the complex Abel norm used by the
small-conductor peer. -/
theorem exists_complexWeight_Abel_budget :
    ∃ D : ℝ,1≤D ∧ ∀ δ : ℝ,0<δ → ∀ j : ℕ,∀ P u v : ℝ,
      0<P → P≤u → u≤v → v≤2*P →
      ‖complexWeight δ j v‖+
        (∫ p in Ioc u v,‖deriv (complexWeight δ j) p‖)≤1+2*D/δ := by
  obtain ⟨D,hD,hbound⟩ := exists_hat_derivative_bound
  refine ⟨D,hD,?_⟩
  intro δ hδ j P u v hP hlo huv hhi
  have hsubset : Icc u v⊆Ioi (0 : ℝ) := fun p hp => hP.trans_le (hlo.trans hp.1)
  have hcont : ContinuousOn (deriv (complexWeight δ j)) (Icc u v) :=
    ((complexWeight_contDiffOn δ j).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)).mono hsubset
  have hint : IntegrableOn (fun p => ‖deriv (complexWeight δ j) p‖) (Ioc u v) :=
    hcont.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hconst : IntegrableOn (fun _ : ℝ => 2*D/(δ*P)) (Ioc u v) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpoint (p : ℝ) (hp : p∈Ioc u v) :
      ‖deriv (complexWeight δ j) p‖≤2*D/(δ*P) := by
    have hp0 : 0<p := hP.trans_le (hlo.trans hp.1.le)
    rw [(complexWeight_hasDerivAt δ j hp0).deriv,Complex.norm_real,
      Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hδ hp0)]
    exact (div_le_div_of_nonneg_right (hbound _) (mul_pos hδ hp0).le).trans
      (div_le_div_of_nonneg_left (by linarith) (mul_pos hδ hP)
        (mul_le_mul_of_nonneg_left (hlo.trans hp.1.le) hδ.le))
  have hvar : (∫ p in Ioc u v,‖deriv (complexWeight δ j) p‖)≤2*D/δ := by
    calc
      _ ≤ ∫ _p in Ioc u v,2*D/(δ*P) :=
        setIntegral_mono_on hint hconst measurableSet_Ioc hpoint
      _ = (v-u)*(2*D/(δ*P)) := by
        rw [← intervalIntegral.integral_of_le huv,intervalIntegral.integral_const,smul_eq_mul]
      _ ≤ P*(2*D/(δ*P)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2*D/δ := by field_simp [hδ.ne',hP.ne']
  linarith [complexWeight_norm_le_one δ j v]

end
end ImbalancedChen.P2GammaSmoothLogGrid
