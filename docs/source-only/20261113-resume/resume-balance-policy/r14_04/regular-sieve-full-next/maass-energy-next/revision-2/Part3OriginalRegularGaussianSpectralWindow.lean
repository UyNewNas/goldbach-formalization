import ImbalancedChen.Part3OriginalRegularCutoffOrder

/-! The compact and limiting Gaussian square on a finite real spectral
window, with the actual native mass from all incoming parameters. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularGaussianSpectralWindow20261113
open Real Set Filter MeasureTheory
open scoped Topology
open OriginalRegularCutoffOrder20261113
open OriginalRegularPreKuznetsovGaussian20261113 (weight weight_nonnegative)
open OriginalRegularPreKuznetsovAverage20261113 (weight_integrable)
open OriginalRegularCompactCoordinates20261113 (native native_nonnegative)
open OriginalCumulativeContinuousRemoval20261110 (marked_density_cont)
open OriginalRegularPreKuznetsovProbe20261113 (probe)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def window (K : ℝ) := {t : ℝ | 2≤|t| ∧ K/2≤|t| ∧ |t|≤K}
def windowMeasure (K : ℝ) : Measure ℝ := volume.restrict (window K)

theorem window_measurable (K : ℝ) : MeasurableSet (window K) := by
  exact (measurableSet_le measurable_const continuous_abs.measurable).inter
    ((measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const))

private theorem contained (K : ℝ) : window K⊆Icc (-K) K := fun _ h => abs_le.mp h.2.2

theorem native_continuous (q : ℕ+) (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (f : ℕ→ℤ) :
    Continuous (native q one S a f) := by
  let C := fun t : ℝ => cosh (π*t)
  have h : Continuous (fun t => native q one S a f t/C t) := marked_density_cont q.val S a f one
  have T : Continuous C := by dsimp only [C];fun_prop
  convert h.mul T using 1
  ext t
  exact (div_mul_cancel₀ _ (cosh_pos (π*t)).ne').symm

def lineDensity (K : ℝ) (j : Option ℕ) (L : ℝ→ℝ) (z : ℝ×ℝ) :=
  weight K z.1*‖value j z.1 z.2‖^2*L z.2

private theorem bound {L : ℝ→ℝ} (L0 : ∀ t,0≤L t) (K : ℝ) (j : Option ℕ) (z : ℝ×ℝ) :
    ‖lineDensity K j L z‖≤(weight K z.1*cap^2)*L z.2 := by
  dsimp only [lineDensity]
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (weight_nonnegative _ _) (sq_nonneg _)) (L0 _))]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (value_bound j z.1 z.2) 2) (weight_nonnegative _ _)) (L0 _)

theorem integral_window {K : ℝ} (hK : 0<K) {L : ℝ→ℝ} (cont : Continuous L) (L0 : ∀ t,0≤L t) :
    (∀ j,Integrable (lineDensity K j L) (volume.prod (windowMeasure K))) ∧
    Tendsto (fun j : ℕ => ∫ z,lineDensity K (some j) L z ∂volume.prod (windowMeasure K))
      atTop (𝓝 (∫ z,lineDensity K none L z ∂volume.prod (windowMeasure K))) := by
  have hi : Integrable L (windowMeasure K) :=
    (cont.continuousOn.integrableOn_compact (isCompact_Icc (a:=-K) (b:=K))).mono_set (contained K)
  have dom := ((weight_integrable hK).mul_const (cap^2)).mul_prod hi
  have me (j : Option ℕ) : Measurable (lineDensity K j L) := by
    have w : Measurable (fun z : ℝ×ℝ => weight K z.1) := by dsimp only [weight];fun_prop
    exact (w.mul ((value_measurable j).norm.pow_const 2)).mul (cont.measurable.comp measurable_snd)
  have integ (j : Option ℕ) : Integrable (lineDensity K j L) (volume.prod (windowMeasure K)) :=
    dom.mono' (me j).aestronglyMeasurable (ae_of_all _ (bound L0 K j))
  refine ⟨integ,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun z : ℝ×ℝ => (weight K z.1*cap^2)*L z.2)
    (fun j => (integ (some j)).aestronglyMeasurable) dom (fun j => ae_of_all _ (bound L0 K (some j)))
  exact ae_of_all _ (fun z => (((coordinate_limit z.1 z.2).norm.pow 2).const_mul (weight K z.1)).mul_const (L z.2))

def discreteDensity (K : ℝ) (j : Option ℕ) (t : ℝ) (r : ℝ) :=
  weight K r*‖value j r t‖^2

theorem discrete_integral {K : ℝ} (hK : 0<K) (t : ℝ) :
    (∀ j,Integrable (discreteDensity K j t)) ∧
    Tendsto (fun j : ℕ => ∫ r : ℝ,discreteDensity K (some j) t r) atTop
      (𝓝 (∫ r : ℝ,discreteDensity K none t r)) := by
  have m (j : Option ℕ) : Measurable (discreteDensity K j t) := by
    have v := (value_measurable j).comp (show Measurable (fun x : ℝ => (x,t)) by fun_prop)
    exact (show Measurable (weight K) by unfold weight;fun_prop).mul (v.norm.pow_const 2)
  have dom := (weight_integrable hK).mul_const (cap^2)
  have b (j : Option ℕ) (r : ℝ) : ‖discreteDensity K j t r‖≤weight K r*cap^2 := by
    simpa only [lineDensity,discreteDensity,mul_one] using bound (L:=fun _ => (1:ℝ)) (fun _ => zero_le_one) K j (r,t)
  have I (j : Option ℕ) := dom.mono' (m j).aestronglyMeasurable (ae_of_all _ (b j))
  refine ⟨I,?_⟩
  exact tendsto_integral_of_dominated_convergence (fun r => weight K r*cap^2)
    (fun k => (I (some k)).aestronglyMeasurable) dom (fun k => ae_of_all _ (b (some k)))
    (ae_of_all _ (fun r => ((coordinate_limit r t).norm.pow 2).const_mul (weight K r)))

theorem shell_floor : ∃ C : ℝ,0<C ∧ ∀ {K t : ℝ},2≤K → t∈window K →
    K/cosh (π*t)≤C*∫ r : ℝ,discreteDensity K none t r := by
  obtain ⟨C,Cp,major⟩ := OriginalRegularPreKuznetsovGaussian20261113.dyadic_gaussian_majorant
  refine ⟨C,Cp,?_⟩
  intro K t hk ht
  have kp : 0<K := by linarith only [hk]
  have I := (discrete_integral kp t).1 none
  have b (r : ℝ) : OriginalRegularPreKuznetsovGaussian20261113.mass K t r≤discreteDensity K none t r := by
    simp only [OriginalRegularPreKuznetsovGaussian20261113.mass,discreteDensity,value,floorLimit,
      norm_mul,Complex.norm_two,mul_pow]
    nlinarith only [mul_nonneg (weight_nonnegative K r) (sq_nonneg ‖probe r ((t:ℂ)*Complex.I)‖)]
  have nonneg (r : ℝ) : 0≤discreteDensity K none t r := mul_nonneg (weight_nonnegative _ _) (sq_nonneg _)
  have w := (integral_mono_ae (OriginalRegularPreKuznetsovGaussian20261113.mass_integrable kp t)
    I.integrableOn (ae_of_all _ b)).trans (setIntegral_le_integral I (ae_of_all _ nonneg))
  calc
    K/cosh (π*t)≤C*∫ r in Ioi (0:ℝ),OriginalRegularPreKuznetsovGaussian20261113.mass K t r := by
      simpa only [div_eq_mul_inv] using major ht.1 ht.2.1 ht.2.2
    _≤_ := mul_le_mul_of_nonneg_left w Cp.le

end ImbalancedChen.Part3.OriginalRegularGaussianSpectralWindow20261113
end

