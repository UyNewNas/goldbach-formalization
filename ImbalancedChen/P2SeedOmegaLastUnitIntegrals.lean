import ImbalancedChen.P2SeedOmegaLastSwitchGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The TWO actual quotient-one integrals, in their own dimensions4 and5.
Their integrability and uniform logarithmic caps are proved, not assumed.
The original manuscript eliminates the low prime for20 and last prime
for21; those exact coordinates are retained. No ambient nullity argument
can erase either positive-dimensional unit mass.
-/

namespace ImbalancedChen.P2SeedOmegaLastUnitIntegrals
noncomputable section
open Set MeasureTheory Filter Classical
open scoped BigOperators
open P2SeedOmegaLastSwitchGeometry
open P2SeedOmegaLiteralFibre (a2 a3 b phi2 phi3)
open Wu2008DoubleSieve (continuousDensity)
open Wu2008DoubleSieve.SecondFunctionalGeometricMass (pureOrderedMass)
open Wu2008DoubleSieve.SecondFunctionalGeometricMass.OrderedPure

theorem reciprocal_eq_density {n : ℕ} (x : Fin n → ℝ) :
    reciprocal x=continuousDensity x := by
  simp [reciprocal,continuousDensity,one_div,Finset.prod_inv_distrib]

theorem integrableOn_reciprocal_band (n : ℕ) {lo hi : ℝ} (hlo : 0<lo) :
    IntegrableOn (reciprocal (n:=n)) (orderedBand n lo hi) := by
  have heq : (reciprocal (n:=n))=continuousDensity := funext reciprocal_eq_density
  rw [heq]
  exact pureOrderedMass_integrable n hlo

theorem integral_reciprocal_band (n : ℕ) {lo hi : ℝ} (hlo : 0<lo) (hlh : lo≤hi) :
    (∫ x in orderedBand n lo hi,reciprocal x)=Real.log (hi/lo)^n/(n.factorial : ℝ) := by
  have heq : (reciprocal (n:=n))=continuousDensity := funext reciprocal_eq_density
  rw [heq]
  exact pureOrderedMass_eq_log n hlo hlh

theorem measurable_eliminated (n : ℕ) (alpha : ℝ) :
    Measurable (eliminated (n:=n) alpha) := by
  unfold eliminated total
  fun_prop

theorem measurable_unitKernel (n : ℕ) (alpha : ℝ) :
    Measurable (unitKernel (n:=n) alpha) := by
  unfold unitKernel eliminated total
  fun_prop

theorem measurableSet_unit20Domain (alpha : ℝ) : MeasurableSet (unit20Domain alpha) :=
  (orderedDomain_measurable 4 a3 b).inter
    (measurableSet_Icc.preimage (measurable_eliminated 4 alpha))

theorem measurableSet_unit21Domain (alpha : ℝ) : MeasurableSet (unit21Domain alpha) :=
  (orderedDomain_measurable 5 a3 b).inter
    ((measurableSet_Icc.preimage (measurable_eliminated 5 alpha)).inter
      (MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i)
        (measurable_eliminated 5 alpha)))

def unit20Density (alpha : ℝ) : (Fin 4 → ℝ) → ℝ :=
  (unit20Domain alpha).indicator (unitKernel alpha)
def unit21Density (alpha : ℝ) : (Fin 5 → ℝ) → ℝ :=
  (unit21Domain alpha).indicator (unitKernel alpha)
def unit20Mass (alpha : ℝ) : ℝ := ∫ y in unit20Domain alpha,unitKernel alpha y
def unit21Mass (alpha : ℝ) : ℝ := ∫ y in unit21Domain alpha,unitKernel alpha y

theorem unit20Density_bounds (alpha : ℝ) (y : Fin 4 → ℝ) :
    0≤unit20Density alpha y ∧ unit20Density alpha y≤
      phi2*(orderedBand 4 a3 b).indicator reciprocal y := by
  by_cases hy : y ∈ unit20Domain alpha
  · rw [unit20Density,indicator_of_mem hy,indicator_of_mem hy.1]
    exact unit20_bounds hy
  · rw [unit20Density,indicator_of_notMem hy]
    refine ⟨le_rfl,mul_nonneg (by norm_num [phi2]) ?_⟩
    by_cases hb : y ∈ orderedBand 4 a3 b
    · rw [indicator_of_mem hb]
      exact (reciprocal_pos (fun i => lt_of_lt_of_le (by norm_num [a3]) (hb.1 i).1)).le
    · rw [indicator_of_notMem hb]

theorem unit21Density_bounds (alpha : ℝ) (y : Fin 5 → ℝ) :
    0≤unit21Density alpha y ∧ unit21Density alpha y≤
      phi3*(orderedBand 5 a3 b).indicator reciprocal y := by
  by_cases hy : y ∈ unit21Domain alpha
  · rw [unit21Density,indicator_of_mem hy,indicator_of_mem hy.1]
    exact unit21_bounds hy
  · rw [unit21Density,indicator_of_notMem hy]
    refine ⟨le_rfl,mul_nonneg (by norm_num [phi3]) ?_⟩
    by_cases hb : y ∈ orderedBand 5 a3 b
    · rw [indicator_of_mem hb]
      exact (reciprocal_pos (fun i => lt_of_lt_of_le (by norm_num [a3]) (hb.1 i).1)).le
    · rw [indicator_of_notMem hb]

theorem integrable_unit20Density (alpha : ℝ) : Integrable (unit20Density alpha) := by
  have hm := orderedDomain_measurable 4 a3 b
  have hi := ((integrableOn_reciprocal_band 4 (hi:=b) (by norm_num [a3])).integrable_indicator hm).const_mul phi2
  apply hi.mono' ((measurable_unitKernel 4 alpha).indicator
    (measurableSet_unit20Domain alpha)).aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs,abs_of_nonneg (unit20Density_bounds alpha y).1]
  exact (unit20Density_bounds alpha y).2

theorem integrable_unit21Density (alpha : ℝ) : Integrable (unit21Density alpha) := by
  have hm := orderedDomain_measurable 5 a3 b
  have hi := ((integrableOn_reciprocal_band 5 (hi:=b) (by norm_num [a3])).integrable_indicator hm).const_mul phi3
  apply hi.mono' ((measurable_unitKernel 5 alpha).indicator
    (measurableSet_unit21Domain alpha)).aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs,abs_of_nonneg (unit21Density_bounds alpha y).1]
  exact (unit21Density_bounds alpha y).2

/-- Uniform in every real alpha, hence in particular every actual alpha>=2.
This is the separate SECOND summand of the manuscript's M20. -/
theorem unit20Mass_log_cap (alpha : ℝ) :
    0≤unit20Mass alpha ∧ unit20Mass alpha≤phi2*Real.log (b/a3)^4/24 := by
  have hm := orderedDomain_measurable 4 a3 b
  have hmaj := ((integrableOn_reciprocal_band 4 (hi:=b) (by norm_num [a3])).integrable_indicator hm).const_mul phi2
  have heq : unit20Mass alpha=∫ y,unit20Density alpha y :=
    (integral_indicator (measurableSet_unit20Domain alpha)).symm
  rw [heq]
  refine ⟨integral_nonneg (fun y => (unit20Density_bounds alpha y).1),?_⟩
  calc
    _ ≤ ∫ y,phi2*(orderedBand 4 a3 b).indicator reciprocal y :=
      integral_mono (integrable_unit20Density alpha) hmaj (fun y => (unit20Density_bounds alpha y).2)
    _ = _ := by
      rw [integral_const_mul,integral_indicator hm,
        integral_reciprocal_band 4 (by norm_num [a3]) (by norm_num [a3,b])]
      norm_num [Nat.factorial]
      ring

/-- Uniform separate SECOND summand of M21. The elimination ordering
gate remains inside the actual integral until the positive majorization. -/
theorem unit21Mass_log_cap (alpha : ℝ) :
    0≤unit21Mass alpha ∧ unit21Mass alpha≤phi3*Real.log (b/a3)^5/120 := by
  have hm := orderedDomain_measurable 5 a3 b
  have hmaj := ((integrableOn_reciprocal_band 5 (hi:=b) (by norm_num [a3])).integrable_indicator hm).const_mul phi3
  have heq : unit21Mass alpha=∫ y,unit21Density alpha y :=
    (integral_indicator (measurableSet_unit21Domain alpha)).symm
  rw [heq]
  refine ⟨integral_nonneg (fun y => (unit21Density_bounds alpha y).1),?_⟩
  calc
    _ ≤ ∫ y,phi3*(orderedBand 5 a3 b).indicator reciprocal y :=
      integral_mono (integrable_unit21Density alpha) hmaj (fun y => (unit21Density_bounds alpha y).2)
    _ = _ := by
      rw [integral_const_mul,integral_indicator hm,
        integral_reciprocal_band 5 (by norm_num [a3]) (by norm_num [a3,b])]
      norm_num [Nat.factorial]
      ring

end
end ImbalancedChen.P2SeedOmegaLastUnitIntegrals
