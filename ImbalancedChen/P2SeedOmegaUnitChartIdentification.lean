import ImbalancedChen.P2SeedOmegaLastUnitIntegrals
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitChamberIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The manuscript eliminates the FIRST coordinate for unit20, whereas the
pinned finite-prime count theorem uses the LAST-coordinate graph chart.
The actual cyclic affine chart preserves free Lebesgue measure. This
proves equality of the two real masses, not merely equality of their caps.
Unit21 uses the same last-coordinate chart in both sources.
-/

namespace ImbalancedChen.P2SeedOmegaUnitChartIdentification
noncomputable section
open Set MeasureTheory Classical
open P2SeedOmegaLastSwitchGeometry
open P2SeedOmegaLastUnitIntegrals
open P2SeedOmegaLiteralFibre (a2 a3 b)
open Wu2008DoubleSieve.SecondFunctionalGeometricMass.OrderedPure

theorem D20_pinned_dictionary (x : Fin 5 → ℝ) :
    x ∈ D20 ↔ Wu2008DoubleSieve.HighUnit.D20 a2 a3 b x := by
  rw [Wu2008DoubleSieve.HighUnit.D20_box_monotone]
  constructor
  · intro hx
    refine ⟨?_,hx.2.2⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hx.1
    · simpa using hx.2.1 j
  · intro hx
    refine ⟨by simpa using hx.1 0,⟨?_,hx.2⟩⟩
    intro j
    simpa using hx.1 j.succ

theorem D21_pinned_dictionary (x : Fin 6 → ℝ) :
    x ∈ D21 ↔ Wu2008DoubleSieve.HighUnit.D21 a3 b x :=
  (Wu2008DoubleSieve.HighUnit.D21_box_monotone a3 b x).symm

def unit20Rotation : Equiv.Perm (Fin 5) where
  toFun := ![4,0,1,2,3]
  invFun := ![1,2,3,4,0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem unit20_chart (alpha : ℝ) (y : Fin 4 → ℝ) :
    Wu2008DoubleSieve.HighUnit.append alpha
      (Wu2008DoubleSieve.HighUnit.graphPerm alpha unit20Rotation y)=unit20Point alpha y := by
  rw [Wu2008DoubleSieve.HighUnit.append_graphPerm]
  ext i
  fin_cases i <;> simp [unit20Rotation,Wu2008DoubleSieve.HighUnit.append,
    unit20Point,eliminated,total]

theorem unit20_point_domain (alpha : ℝ) (y : Fin 4 → ℝ) :
    unit20Point alpha y ∈ D20 ↔ y ∈ unit20Domain alpha := by
  simp [unit20Point,D20,unit20Domain,and_comm]

theorem unit21_point_domain (alpha : ℝ) (y : Fin 5 → ℝ) :
    unit21Point alpha y ∈ D21 ↔ y ∈ unit21Domain alpha := by
  constructor
  · intro hx
    obtain ⟨hq,hy⟩ := (mem_orderedDomain_snoc a3 b (eliminated alpha y) y).mp hx
    exact ⟨⟨fun i => ⟨(hy.1 i).1,(hy.1 i).2.trans hq.2⟩,hy.2⟩,
      hq,fun i => (hy.1 i).2⟩
  · exact unit21_reconstruct

theorem section20_as_indicator (alpha : ℝ) (t : Fin 4 → ℝ) :
    Wu2008DoubleSieve.HighUnit.section20 a2 a3 b alpha t=
      D20.indicator reciprocal (Wu2008DoubleSieve.HighUnit.append alpha t) := by
  by_cases ht : Wu2008DoubleSieve.HighUnit.D20 a2 a3 b
      (Wu2008DoubleSieve.HighUnit.append alpha t)
  · rw [Wu2008DoubleSieve.HighUnit.section20,if_pos ht,
      indicator_of_mem ((D20_pinned_dictionary _).mpr ht)]
    simp [reciprocal,Wu2008DoubleSieve.HighUnit.append,Fin.prod_univ_castSucc]
  · rw [Wu2008DoubleSieve.HighUnit.section20,if_neg ht,
      indicator_of_notMem (fun h => ht ((D20_pinned_dictionary _).mp h))]

theorem section21_as_indicator (alpha : ℝ) (t : Fin 5 → ℝ) :
    Wu2008DoubleSieve.HighUnit.section21 a3 b alpha t=
      D21.indicator reciprocal (Wu2008DoubleSieve.HighUnit.append alpha t) := by
  by_cases ht : Wu2008DoubleSieve.HighUnit.D21 a3 b
      (Wu2008DoubleSieve.HighUnit.append alpha t)
  · rw [Wu2008DoubleSieve.HighUnit.section21,if_pos ht,
      indicator_of_mem ((D21_pinned_dictionary _).mpr ht)]
    simp [reciprocal,Wu2008DoubleSieve.HighUnit.append,Fin.prod_univ_castSucc]
  · rw [Wu2008DoubleSieve.HighUnit.section21,if_neg ht,
      indicator_of_notMem (fun h => ht ((D21_pinned_dictionary _).mp h))]

theorem unit20_density_chart (alpha : ℝ) (y : Fin 4 → ℝ) :
    unit20Density alpha y=Wu2008DoubleSieve.HighUnit.section20 a2 a3 b alpha
      (Wu2008DoubleSieve.HighUnit.graphPerm alpha unit20Rotation y) := by
  rw [section20_as_indicator,unit20_chart]
  by_cases hy : y ∈ unit20Domain alpha
  · rw [unit20Density,indicator_of_mem hy,
      indicator_of_mem ((unit20_point_domain alpha y).mpr hy),unit20_density_identity]
  · rw [unit20Density,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy ((unit20_point_domain alpha y).mp h))]

theorem unit21_density_chart (alpha : ℝ) (y : Fin 5 → ℝ) :
    unit21Density alpha y=Wu2008DoubleSieve.HighUnit.section21 a3 b alpha y := by
  rw [section21_as_indicator]
  change unit21Density alpha y=D21.indicator reciprocal (unit21Point alpha y)
  by_cases hy : y ∈ unit21Domain alpha
  · rw [unit21Density,indicator_of_mem hy,
      indicator_of_mem ((unit21_point_domain alpha y).mpr hy),unit21_density_identity]
  · rw [unit21Density,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy ((unit21_point_domain alpha y).mp h))]

/-- Actual first-coordinate surface mass equals the existing finite-count
receiver's J20 at the SAME real alpha, by an actual affine change of chart. -/
theorem unit20Mass_eq_pinned_J20 (alpha : ℝ) :
    unit20Mass alpha=Wu2008DoubleSieve.HighUnit.J20 a2 a3 b alpha := by
  calc
    _ = ∫ y,unit20Density alpha y :=
      (integral_indicator (measurableSet_unit20Domain alpha)).symm
    _ = ∫ y,Wu2008DoubleSieve.HighUnit.section20 a2 a3 b alpha
        (Wu2008DoubleSieve.HighUnit.graphPerm alpha unit20Rotation y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (unit20_density_chart alpha)
    _ = _ := Wu2008DoubleSieve.HighUnit.integral_graphPerm alpha unit20Rotation _

theorem unit21Mass_eq_pinned_J21 (alpha : ℝ) :
    unit21Mass alpha=Wu2008DoubleSieve.HighUnit.J21 a3 b alpha := by
  calc
    _ = ∫ y,unit21Density alpha y :=
      (integral_indicator (measurableSet_unit21Domain alpha)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (unit21_density_chart alpha)

end
end ImbalancedChen.P2SeedOmegaUnitChartIdentification
