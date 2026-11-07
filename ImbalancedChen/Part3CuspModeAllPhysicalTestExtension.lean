import ImbalancedChen.Part3CuspModePhysicalDifferential

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Every usual smooth physical profile compact in positive height belongs to
the actual mode operator domain, and its operator value is the literal
physical second derivative expression in dy/y^2. The earlier radial-image
extension is applied to the explicitly constructed radialTestOfPhysical.
Equality on the open positive-height set is differentiated twice; no
derivative identity or physical graph membership is assumed.
-/

namespace ImbalancedChen.Part3.CuspModeAllPhysicalTestExtension20261026b
noncomputable section
open Set Filter MeasureTheory
open CuspCylinderMeasure20261024z
open CuspCylinderBesselMode20261024z
open CuspModePhysicalCoreForm20261026a
open CuspModeNativeClosedForm20261026a
open CuspModePhysicalDifferential20261026b

theorem physical_test_lift_eqOn (a : ℝ) (ha : 0 < a) (T : PhysicalHeightTest) :
    EqOn (physicalLift a (radialTestOfPhysical a ha T).function) T.function (Ioi 0) := by
  intro y hy
  exact physical_test_is_lift a ha T ⟨y, hy⟩

theorem physical_test_lift_second_deriv_eqOn (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    EqOn (deriv (deriv (physicalLift a (radialTestOfPhysical a ha T).function)))
      (deriv (deriv T.function)) (Ioi 0) :=
  ((physical_test_lift_eqOn a ha T).deriv isOpen_Ioi).deriv isOpen_Ioi

theorem physical_test_differential_lift_eq (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) (y : PositiveHeight) :
    physicalDifferential a (physicalLift a (radialTestOfPhysical a ha T).function) y =
      physicalDifferential a T.function y := by
  unfold physicalDifferential
  rw [physical_test_lift_second_deriv_eqOn a ha T y.property,
    physical_test_is_lift a ha T y]

theorem physicalHeightTest_memLp (T : PhysicalHeightTest) :
    MemLp (fun y : PositiveHeight => T.function y) 2 heightMeasure :=
  (physicalLift_memLp (a := 1) (by norm_num)
      (radialTestOfPhysical 1 (by norm_num) T)).congr
    (Eventually.of_forall (physical_test_is_lift 1 (by norm_num) T))

def physicalHeightTestL2 (T : PhysicalHeightTest) : PhysicalHeightL2 :=
  (physicalHeightTest_memLp T).toLp (fun y : PositiveHeight => T.function y)

theorem physicalHeightTestL2_eq_radial_core (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    physicalHeightTestL2 T = physicalCoreL2 a ha (radialTestOfPhysical a ha T) := by
  apply Lp.ext
  exact (physicalHeightTest_memLp T).coeFn_toLp.trans
    ((Eventually.of_forall (physical_test_is_lift a ha T)).symm.trans
      (physicalLift_memLp ha (radialTestOfPhysical a ha T)).coeFn_toLp.symm)

theorem physicalHeightTestDifferential_memLp (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    MemLp (fun y : PositiveHeight => physicalDifferential a T.function y) 2 heightMeasure :=
  (physicalDifferential_core_memLp a ha (radialTestOfPhysical a ha T)).congr
    (Eventually.of_forall (physical_test_differential_lift_eq a ha T))

def physicalHeightTestDifferentialL2 (a : ℝ) (ha : 0 < a) (T : PhysicalHeightTest) :
    PhysicalHeightL2 :=
  (physicalHeightTestDifferential_memLp a ha T).toLp
    (fun y : PositiveHeight => physicalDifferential a T.function y)

theorem physicalHeightTestDifferentialL2_eq_radial_core (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    physicalHeightTestDifferentialL2 a ha T =
      physicalDifferentialCoreL2 a ha (radialTestOfPhysical a ha T) := by
  apply Lp.ext
  exact (physicalHeightTestDifferential_memLp a ha T).coeFn_toLp.trans
    ((Eventually.of_forall (physical_test_differential_lift_eq a ha T)).symm.trans
      (physicalDifferential_core_memLp a ha (radialTestOfPhysical a ha T)).coeFn_toLp.symm)

/-- All usual smooth compact physical tests occur in the native graph;
the output is represented by the literal physical differential expression. -/
theorem actualModeFriedrichs_extends_all_physical_tests (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    (physicalHeightTestL2 T, physicalHeightTestDifferentialL2 a ha T) ∈
      (actualModeFriedrichs a ha).graph := by
  rw [physicalHeightTestL2_eq_radial_core a ha T,
    physicalHeightTestDifferentialL2_eq_radial_core a ha T]
  exact actualModeFriedrichs_extends_physicalDifferential a ha
    (radialTestOfPhysical a ha T)

theorem physicalHeightTest_in_actualMode_domain (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    physicalHeightTestL2 T ∈ (actualModeFriedrichs a ha).domain :=
  LinearPMap.mem_domain_iff.mpr
    ⟨physicalHeightTestDifferentialL2 a ha T,
      actualModeFriedrichs_extends_all_physical_tests a ha T⟩

/-- Native partial-map evaluation at every genuine smooth compact profile. -/
theorem actualModeFriedrichs_apply_physical_test (a : ℝ) (ha : 0 < a)
    (T : PhysicalHeightTest) :
    actualModeFriedrichs a ha
      ⟨physicalHeightTestL2 T, physicalHeightTest_in_actualMode_domain a ha T⟩ =
      physicalHeightTestDifferentialL2 a ha T :=
  LinearPMap.mem_graph_snd_inj (actualModeFriedrichs a ha)
    (LinearPMap.mem_graph _ _)
    (actualModeFriedrichs_extends_all_physical_tests a ha T) rfl

/-- The signed original mode n has exactly its original horizontal
eigenvalue (2*pi*n)^2; the absolute value in the positive scale disappears. -/
theorem physicalDifferential_frequency_literal (n : ℤ) (f : ℝ → ℂ) (y : ℝ) :
    physicalDifferential (frequencyScale n) f y =
      -(y : ℂ) ^ 2 * deriv (deriv f) y +
        ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y := by
  have hfreq : (frequencyScale n : ℂ) ^ 2 =
      ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast frequencyScale_sq n
  unfold physicalDifferential
  rw [Complex.ofReal_mul, mul_pow, hfreq]

theorem actualNonzeroModeFriedrichs_extends_all_physical_tests
    (n : ℤ) (hn : n ≠ 0) (T : PhysicalHeightTest) :
    (physicalHeightTestL2 T,
      physicalHeightTestDifferentialL2 (frequencyScale n) (frequencyScale_pos hn) T) ∈
      (actualNonzeroModeFriedrichs n hn).graph :=
  actualModeFriedrichs_extends_all_physical_tests
    (frequencyScale n) (frequencyScale_pos hn) T

end
end ImbalancedChen.Part3.CuspModeAllPhysicalTestExtension20261026b
