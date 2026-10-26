import ImbalancedChen.P2SeedOmegaFirstThreeKernel
import ImbalancedChen.P2SeedOmegaLiteralFunctional

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original switched omega masses9,10,11 are bounded by the FIRST
THREE literal switchedMass entries. Real integrals and exact primitives
are reused from the pinned GeoMass modules. No integral value, numerical
PASS, final saving, or count licence is an assumption. All alpha>=2 are
covered, and the separate arithmetic count-to-integral supplier is OPEN.
-/

namespace ImbalancedChen.P2SeedOmegaFirstThreeLiteralMass
noncomputable section

open Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SecondFunctionalGeometricMass
open Wu2008DoubleSieve.SecondFunctionalJointTail
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b phi1 phi2 phi3 s omegaCap)
open P2SeedOmegaFirstThreeKernel

theorem geometric_zero_reduction : geometric 0=FullReduction.logMoment 1 1 a1 a3 := by
  change selectedOrderedMass (1 : Fin 3) a1 a3=FullReduction.logMoment 1 1 a1 a3
  rw [FullReduction.selectedOrderedMass_eq_log (1 : Fin 3)
    (by norm_num [a1]) (by norm_num [a1,a3])]
  norm_num

theorem geometric_one_reduction : geometric 1=
    FullReduction.logMoment 1 0 a1 a2*Real.log (b/a2) := by
  change geometricMass (1 : Fin 3) (LowerTripleContinuous.D a0 a1 a2 a3 b 0)=_
  have hb : 0<a1 := by norm_num [a1]
  have hc : 0<a2 := by norm_num [a2]
  have h := OriginalBlocks.mass_blocks_left (1 : Fin 2) hb hc _
    (OriginalBlocks.lower_zero_domain a0 a1 a2 a3 b)
  have hblocks : geometricMass (1 : Fin 3) (LowerTripleContinuous.D a0 a1 a2 a3 b 0)=
      selectedOrderedMass (1 : Fin 2) a1 a2*Real.log (b/a2) := by
    simpa only [OriginalBlocks.pure_one hc (by norm_num [a2,b] : a2≤b)] using h
  rw [hblocks,FullReduction.selectedOrderedMass_eq_log (1 : Fin 2) hb
    (by norm_num [a1,a2])]
  norm_num

theorem geometric_two_reduction : geometric 2=
    Real.log (a2/a1)*FullReduction.logMoment 0 1 a2 a3 := by
  change geometricMass (1 : Fin 3) (LowerTripleContinuous.D a0 a1 a2 a3 b 1)=_
  have hb : 0<a1 := by norm_num [a1]
  have hc : 0<a2 := by norm_num [a2]
  have h := OriginalBlocks.mass_blocks_right (0 : Fin 2) hb hc _
    (OriginalBlocks.lower_one_domain a0 a1 a2 a3 b)
  have hblocks : geometricMass (1 : Fin 3) (LowerTripleContinuous.D a0 a1 a2 a3 b 1)=
      Real.log (a2/a1)*selectedOrderedMass (0 : Fin 2) a2 a3 := by
    simpa only [OriginalBlocks.pure_one hb (by norm_num [a1,a2] : a1≤a2)] using h
  rw [hblocks,FullReduction.selectedOrderedMass_eq_log (0 : Fin 2) hc
    (by norm_num [a2,a3])]
  norm_num

/-- The selected reciprocal is still the MIDDLE coordinate of all
three-dimensional original domains; it has not been replaced by a cap. -/
theorem geometric_zero_log : geometric 0=
    (1/a1+1/a3)*Real.log (a3/a1)-2*(1/a1-1/a3) := by
  rw [geometric_zero_reduction,Elementary.logMoment_one_eq 1
    (by norm_num [a1]) (by norm_num [a1,a3])]
  norm_num [Elementary.elementaryMomentOne,Elementary.elementaryMomentZero,
    Elementary.momentPolynomial] <;> ring

theorem geometric_one_log : geometric 1=
    (1/a1-(Real.log (a2/a1)+1)/a2)*Real.log (b/a2) := by
  rw [geometric_one_reduction,Elementary.logMoment_zero_eq 1
    (by norm_num [a1]) (by norm_num [a1,a2])]
  norm_num [Elementary.elementaryMomentZero,Elementary.momentPolynomial]

theorem geometric_two_log : geometric 2=
    Real.log (a2/a1)*((Real.log (a3/a2)-1)/a2+1/a3) := by
  rw [geometric_two_reduction,Elementary.logMoment_one_eq 0
    (by norm_num [a2]) (by norm_num [a2,a3])]
  norm_num [Elementary.elementaryMomentOne,Elementary.elementaryMomentZero,
    Elementary.momentPolynomial] <;> ring

theorem first_literal_entry : omegaCap*geometric 0=
    P2SeedOmegaLiteralFunctional.switchedMass 0 := by
  rw [geometric_zero_log]
  change omegaCap*((1/a1+1/a3)*Real.log (a3/a1)-2*(1/a1-1/a3))=
    omegaCap*((phi1+phi3)*Real.log (phi1/phi3)-2*(phi1-phi3))
  norm_num [a1,a3,phi1,phi3] <;> ring

theorem second_literal_entry : omegaCap*geometric 1=
    P2SeedOmegaLiteralFunctional.switchedMass 1 := by
  rw [geometric_one_log]
  change omegaCap*((1/a1-(Real.log (a2/a1)+1)/a2)*Real.log (b/a2))=
    omegaCap*(phi1-phi2*(1+P2SeedOmegaLiteralFunctional.l12))*Real.log (phi2/s)
  norm_num [a1,a2,b,phi1,phi2,s,P2SeedOmegaLiteralFunctional.l12] <;> ring

theorem third_literal_entry : omegaCap*geometric 2=
    P2SeedOmegaLiteralFunctional.switchedMass 2 := by
  rw [geometric_two_log]
  change omegaCap*(Real.log (a2/a1)*((Real.log (a3/a2)-1)/a2+1/a3))=
    omegaCap*P2SeedOmegaLiteralFunctional.l12*
      (phi2*(P2SeedOmegaLiteralFunctional.l23-1)+phi3)
  norm_num [a1,a2,a3,phi1,phi2,phi3,
    P2SeedOmegaLiteralFunctional.l12,P2SeedOmegaLiteralFunctional.l23] <;> ring

/-- The actual omega-weighted switched integrals, uniformly on the
whole original half-line alpha>=2, now feed the literal seed functional. -/
theorem original_first_three_mass_bounds {alpha : ℝ} (ha : 2≤alpha) :
    actualMass alpha 0≤P2SeedOmegaLiteralFunctional.switchedMass 0 ∧
    actualMass alpha 1≤P2SeedOmegaLiteralFunctional.switchedMass 1 ∧
    actualMass alpha 2≤P2SeedOmegaLiteralFunctional.switchedMass 2 := by
  exact ⟨(actualMass_le_geometric 0 ha).trans_eq first_literal_entry,
    (actualMass_le_geometric 1 ha).trans_eq second_literal_entry,
    (actualMass_le_geometric 2 ha).trans_eq third_literal_entry⟩

end
end ImbalancedChen.P2SeedOmegaFirstThreeLiteralMass
