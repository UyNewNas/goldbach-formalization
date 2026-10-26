import ImbalancedChen.P2SeedOmegaLastUnitIntegrals
import ImbalancedChen.FinitePiIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original M20/M21 nonunit integrals PLUS separate unit integrals
are bounded by literal switchedMass11/12. Only measurable omega with its
elementary [0,1] bound on arguments>=1 is input. No target mass, log cap,
count estimate, numerical pass or enhanced-count licence is assumed.
-/

namespace ImbalancedChen.P2SeedOmegaLastFullMassBounds
noncomputable section
open Set MeasureTheory Filter Classical
open scoped BigOperators Interval
open P2SeedOmegaLastSwitchGeometry
open P2SeedOmegaLastUnitIntegrals
open P2SeedOmegaLiteralFibre (a2 a3 b phi2 phi3)
open Wu2008DoubleSieve (continuousDensity)
open Wu2008DoubleSieve.SecondFunctionalGeometricMass.OrderedPure

theorem measurableSet_D20 : MeasurableSet D20 :=
  (measurableSet_Icc.preimage (measurable_pi_apply 0)).inter
    ((orderedDomain_measurable 4 a3 b).preimage (by fun_prop))
theorem measurableSet_D21 : MeasurableSet D21 := orderedDomain_measurable 6 a3 b

theorem integrableOn_reciprocal_D20 : IntegrableOn reciprocal D20 := by
  have h := pure_rectangle_integrable 5 (b:=b) (by norm_num [a2] : 0<a2)
  have heq : (reciprocal (n:=5))=continuousDensity := funext reciprocal_eq_density
  rw [heq]
  exact h.mono_set (fun x hx i _ => D20_coordinate_bounds hx i)

/-- Genuine Fubini for the independent low band times FOUR ordered
high coordinates, followed by the pinned proved ordered log integral. -/
theorem integral_reciprocal_D20 :
    (∫ x in D20,reciprocal x)=Real.log (a3/a2)*Real.log (b/a3)^4/24 := by
  let F := D20.indicator reciprocal
  have hi : Integrable F := integrableOn_reciprocal_D20.integrable_indicator measurableSet_D20
  have hpoint (u : ℝ) (y : Fin 4 → ℝ) : F (Fin.cons u y)=
      (Icc a2 a3).indicator (fun u => (1/u)*(orderedBand 4 a3 b).indicator reciprocal y) u := by
    by_cases hu : u ∈ Icc a2 a3 <;> by_cases hy : y ∈ orderedBand 4 a3 b
    all_goals simp [F,D20,hu,hy,reciprocal,Fin.prod_univ_succ,one_div,mul_inv_rev,mul_comm]
  have hslice (u : ℝ) : (∫ y : Fin 4 → ℝ,F (Fin.cons u y))=
      (Icc a2 a3).indicator (fun u => (1/u)*(∫ y in orderedBand 4 a3 b,reciprocal y)) u := by
    simp_rw [hpoint]
    by_cases hu : u ∈ Icc a2 a3
    · simp_rw [indicator_of_mem hu]
      rw [integral_const_mul,integral_indicator (orderedDomain_measurable 4 a3 b)]
    · simp_rw [indicator_of_notMem hu]
      simp only [integral_zero]
  have hlow : (∫ u in Icc a2 a3,(1:ℝ)/u)=Real.log (a3/a2) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num [a2,a3])]
    exact integral_one_div_of_pos (by norm_num [a2]) (by norm_num [a3])
  calc
    _ = ∫ x,F x := (integral_indicator measurableSet_D20).symm
    _ = ∫ u : ℝ,∫ y : Fin 4 → ℝ,F (Fin.cons u y) := integral_fin_succ F hi
    _ = ∫ u in Icc a2 a3,(1/u)*(∫ y in orderedBand 4 a3 b,reciprocal y) := by
      simp_rw [hslice]
      exact integral_indicator measurableSet_Icc
    _ = _ := by
      rw [integral_mul_const,hlow,integral_reciprocal_band 4
        (by norm_num [a3]) (by norm_num [a3,b])]
      norm_num [Nat.factorial]
      ring

def nonunit20Density (ω : ℝ → ℝ) (alpha : ℝ) : (Fin 5 → ℝ) → ℝ :=
  D20.indicator (fun x => nonunitKernel ω alpha (w20 x) x)
def nonunit21Density (ω : ℝ → ℝ) (alpha : ℝ) : (Fin 6 → ℝ) → ℝ :=
  D21.indicator (fun x => nonunitKernel ω alpha (w21 x) x)
def nonunit20Mass (ω : ℝ → ℝ) (alpha : ℝ) : ℝ :=
  ∫ x in D20,nonunitKernel ω alpha (w20 x) x
def nonunit21Mass (ω : ℝ → ℝ) (alpha : ℝ) : ℝ :=
  ∫ x in D21,nonunitKernel ω alpha (w21 x) x
def full20Mass (ω : ℝ → ℝ) (alpha : ℝ) : ℝ := nonunit20Mass ω alpha+unit20Mass alpha
def full21Mass (ω : ℝ → ℝ) (alpha : ℝ) : ℝ := nonunit21Mass ω alpha+unit21Mass alpha

theorem nonunit20Density_bounds (ω : ℝ → ℝ)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) (x : Fin 5 → ℝ) :
    0≤nonunit20Density ω alpha x ∧ nonunit20Density ω alpha x≤phi3*D20.indicator reciprocal x := by
  by_cases hx : x ∈ D20
  · rw [nonunit20Density,indicator_of_mem hx,indicator_of_mem hx]
    exact nonunit20_bounds ω hω alpha hx
  · rw [nonunit20Density,indicator_of_notMem hx,indicator_of_notMem hx]
    simp

theorem nonunit21Density_bounds (ω : ℝ → ℝ)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) (x : Fin 6 → ℝ) :
    0≤nonunit21Density ω alpha x ∧ nonunit21Density ω alpha x≤phi3*D21.indicator reciprocal x := by
  by_cases hx : x ∈ D21
  · rw [nonunit21Density,indicator_of_mem hx,indicator_of_mem hx]
    exact nonunit21_bounds ω hω alpha hx
  · rw [nonunit21Density,indicator_of_notMem hx,indicator_of_notMem hx]
    simp

theorem integrable_nonunit20Density (ω : ℝ → ℝ) (hmω : Measurable ω)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) :
    Integrable (nonunit20Density ω alpha) := by
  have hmaj := (integrableOn_reciprocal_D20.integrable_indicator measurableSet_D20).const_mul phi3
  have hm : Measurable (fun x : Fin 5 → ℝ => nonunitKernel ω alpha (w20 x) x) := by
    unfold nonunitKernel w20 total
    fun_prop
  apply hmaj.mono' (hm.indicator measurableSet_D20).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (nonunit20Density_bounds ω hω alpha x).1]
  exact (nonunit20Density_bounds ω hω alpha x).2

theorem integrable_nonunit21Density (ω : ℝ → ℝ) (hmω : Measurable ω)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) :
    Integrable (nonunit21Density ω alpha) := by
  have hmaj := ((integrableOn_reciprocal_band 6 (hi:=b) (by norm_num [a3])).integrable_indicator measurableSet_D21).const_mul phi3
  have hm : Measurable (fun x : Fin 6 → ℝ => nonunitKernel ω alpha (w21 x) x) := by
    unfold nonunitKernel w21 total
    fun_prop
  apply hmaj.mono' (hm.indicator measurableSet_D21).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (nonunit21Density_bounds ω hω alpha x).1]
  exact (nonunit21Density_bounds ω hω alpha x).2

theorem nonunit20Mass_log_cap (ω : ℝ → ℝ) (hmω : Measurable ω)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) :
    0≤nonunit20Mass ω alpha ∧
      nonunit20Mass ω alpha≤phi3*Real.log (a3/a2)*Real.log (b/a3)^4/24 := by
  have heq : nonunit20Mass ω alpha=∫ x,nonunit20Density ω alpha x :=
    (integral_indicator measurableSet_D20).symm
  rw [heq]
  refine ⟨integral_nonneg (fun x => (nonunit20Density_bounds ω hω alpha x).1),?_⟩
  calc
    _ ≤ ∫ x,phi3*D20.indicator reciprocal x := integral_mono
      (integrable_nonunit20Density ω hmω hω alpha)
      ((integrableOn_reciprocal_D20.integrable_indicator measurableSet_D20).const_mul phi3)
      (fun x => (nonunit20Density_bounds ω hω alpha x).2)
    _ = _ := by rw [integral_const_mul,integral_indicator measurableSet_D20,integral_reciprocal_D20]; ring

theorem nonunit21Mass_log_cap (ω : ℝ → ℝ) (hmω : Measurable ω)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) :
    0≤nonunit21Mass ω alpha ∧ nonunit21Mass ω alpha≤phi3*Real.log (b/a3)^6/720 := by
  have heq : nonunit21Mass ω alpha=∫ x,nonunit21Density ω alpha x :=
    (integral_indicator measurableSet_D21).symm
  rw [heq]
  refine ⟨integral_nonneg (fun x => (nonunit21Density_bounds ω hω alpha x).1),?_⟩
  calc
    _ ≤ ∫ x,phi3*D21.indicator reciprocal x := integral_mono
      (integrable_nonunit21Density ω hmω hω alpha)
      (((integrableOn_reciprocal_band 6 (hi:=b) (by norm_num [a3])).integrable_indicator measurableSet_D21).const_mul phi3)
      (fun x => (nonunit21Density_bounds ω hω alpha x).2)
    _ = _ := by
      rw [integral_const_mul,integral_indicator measurableSet_D21,
        integral_reciprocal_band 6 (by norm_num [a3]) (by norm_num [a3,b])]
      norm_num [Nat.factorial]
      ring

/-- Literal original indices11,12, including both separate unit terms.
This is stronger than alpha>=2 uniformity, with no count supplier hidden. -/
theorem full_masses_le_original (ω : ℝ → ℝ) (hmω : Measurable ω)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ) :
    full20Mass ω alpha≤P2SeedOmegaLiteralFunctional.switchedMass (11 : Fin 13) ∧
    full21Mass ω alpha≤P2SeedOmegaLiteralFunctional.switchedMass (12 : Fin 13) := by
  have h23 : Real.log (a3/a2)=P2SeedOmegaLiteralFunctional.l23 := by
    norm_num [P2SeedOmegaLiteralFunctional.l23,a3,a2,phi2,phi3]
  have h3b : Real.log (b/a3)=P2SeedOmegaLiteralFunctional.l3b := by
    norm_num [P2SeedOmegaLiteralFunctional.l3b,b,a3,phi3,P2SeedOmegaLiteralFibre.s]
  constructor
  · have h := add_le_add (nonunit20Mass_log_cap ω hmω hω alpha).2 (unit20Mass_log_cap alpha).2
    simpa only [full20Mass,h23,h3b,P2SeedOmegaLiteralFunctional.switchedMass,
      Matrix.cons_val_succ,Matrix.cons_val_zero] using h
  · have h := add_le_add (nonunit21Mass_log_cap ω hmω hω alpha).2 (unit21Mass_log_cap alpha).2
    simpa only [full21Mass,h3b,P2SeedOmegaLiteralFunctional.switchedMass,
      Matrix.cons_val_succ,Matrix.cons_val_zero] using h

end
end ImbalancedChen.P2SeedOmegaLastFullMassBounds
