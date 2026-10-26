import ImbalancedChen.P2SeedOmegaSwitchedKernelFour
import ImbalancedChen.P2SeedOmegaLiteralFunctional
import MathlibNt.Wu2008DoubleSieve.GeoMassElementaryPrimitives

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The genuine original M12..M15 Buchstab masses are bounded by the four
literal entries 3..6 in switchedMass, uniformly for alpha >= 2. The native
geometric integral producers (including their Fubini and elementary
primitives) are reused verbatim. Their original-parameter specializations
are identified with the literal certifier expressions, without evaluating
any numerical witness. The true omega envelope is supplied internally.
This does not assert the asymptotic arithmetic switched-count licence.
-/

namespace ImbalancedChen.P2SeedOmegaSwitchedMassFour

noncomputable section

open Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SecondFunctionalJointTail
open Wu2008DoubleSieve.SecondFunctionalGeometricMass
open P2SeedOmegaLiteralFibre (s s0 phi1 phi2 phi3 a0 a1 a2 a3 b omegaCap)
open P2SeedOmegaLiteralFunctional (l01 l12 l23 l3b switchedMass)
open P2SeedOmegaSwitchedKernelFour

private theorem native_two_geometric : lowerMass nativeParameters 2=
    selectedOrderedMass (1 : Fin 2) a0 a1*Real.log (b/a3) := by
  have h := OriginalBlocks.lowerMass_two_blocks nativeParameters native_mother
    (by norm_num [nativeParameters,s] : 2≤nativeParameters.s)
  convert h using 1 <;>
    norm_num [nativeParameters,s,s0,phi1,phi2,phi3,a0,a1,a2,a3,b]

private theorem native_four_geometric : lowerMass nativeParameters 4=
    Real.log (a1/a0)*selectedOrderedMass (0 : Fin 2) a2 b := by
  have h := OriginalBlocks.lowerMass_four_blocks nativeParameters native_mother
    (by norm_num [nativeParameters,s] : 2≤nativeParameters.s)
  convert h using 1 <;>
    norm_num [nativeParameters,s,s0,phi1,phi2,phi3,a0,a1,a2,a3,b]

/-- The M12 domain is ordered [a0,a1]^2 followed by [a3,b]. The exact
native integral has selected coordinate one, not the terminal prime. -/
theorem native_mass12_exact : lowerMass nativeParameters 2=
    (s0-phi1*(1+l01))*l3b := by
  have ha : 0<a0 := by norm_num [a0]
  have hab : a0≤a1 := by norm_num [a0,a1]
  have heval : selectedOrderedMass (1 : Fin 2) a0 a1=
      Elementary.elementaryMomentZero 1 a0 a1 := by
    rw [FullReduction.selectedOrderedMass_eq_log (1 : Fin 2) ha hab]
    simpa using Elementary.logMoment_zero_eq 1 ha hab
  rw [native_two_geometric,heval]
  norm_num [Elementary.elementaryMomentZero,Elementary.momentPolynomial,
    a0,a1,a3,b,s0,phi1,phi3,s,l01,l3b] <;> ring

/-- The M13 domain is the original three distinct colour windows. -/
theorem native_mass13_exact : lowerMass nativeParameters 3=
    l01*(phi1-phi2)*Real.log (phi2/s) := by
  rw [OriginalBlocks.lowerMass_three_blocks nativeParameters native_mother
    (by norm_num [nativeParameters,s] : 2≤nativeParameters.s)]
  norm_num [lowerThreeLog,nativeParameters,l01,s0,phi1,phi2,phi3,s] <;> ring

/-- The M14 selected prime is the FIRST of its last ordered pair.
The pinned logMoment(0,1) primitive supplies its exact geometric mass. -/
theorem native_mass14_exact : lowerMass nativeParameters 4=
    l01*(phi2*(Real.log (phi2/s)-1)+s) := by
  have ha : 0<a2 := by norm_num [a2]
  have hab : a2≤b := by norm_num [a2,b]
  have heval : selectedOrderedMass (0 : Fin 2) a2 b=
      Elementary.elementaryMomentOne 0 a2 b := by
    rw [FullReduction.selectedOrderedMass_eq_log (0 : Fin 2) ha hab]
    simpa using Elementary.logMoment_one_eq 0 ha hab
  rw [native_four_geometric,heval]
  norm_num [Elementary.elementaryMomentOne,Elementary.elementaryMomentZero,
    Elementary.momentPolynomial,a0,a1,a2,b,s0,phi1,phi2,s,l01] <;> ring

/-- The M15 domain is [a1,a2][a2,a3][a3,b], with middle-prime cutoff. -/
theorem native_mass15_exact : lowerMass nativeParameters 5=
    l12*(phi2-phi3)*l3b := by
  rw [OriginalBlocks.lowerMass_five_blocks nativeParameters native_mother
    (by norm_num [nativeParameters,s] : 2≤nativeParameters.s)]
  norm_num [lowerFiveLog,nativeParameters,l12,l3b,phi1,phi2,phi3,s] <;> ring

/-- Exact semantics of the four entries used by the literal ordinary
seed functional: actual geometric integrals multiplied by c_omega. -/
theorem literal_switchedMass_eq_native_integral (j : Fin 4) :
    switchedMass (functionalIndex j)=omegaCap*lowerMass nativeParameters (nativeIndex j) := by
  fin_cases j
  all_goals simp only [functionalIndex,nativeIndex,switchedMass,Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  · rw [native_mass12_exact]
    ring
  · rw [native_mass13_exact]
    ring
  · rw [native_mass14_exact]
    ring
  · rw [native_mass15_exact]
    ring

/-- Every admitted alpha >= 2 is retained. No asserted mass bound,
numerical witness, or unknown enhanced-count estimate is a hypothesis. -/
theorem actual_M12_to_M15_le_literal (alpha : ℝ) (ha : 2≤alpha) (j : Fin 4) :
    actualMass alpha j≤switchedMass (functionalIndex j) := by
  rw [literal_switchedMass_eq_native_integral]
  exact actualMass_le_cap_native_lowerMass alpha ha j

/-- The four masses are the ACTUAL native switched kernels, with no
unit surface for any alpha in the admitted half-line. -/
theorem original_native_K_le_literal (alpha : ℝ) (ha : 2≤alpha) (j : Fin 4) :
    LowerTripleContinuous.K a0 a1 a2 a3 b (nativeIndex j) alpha≤
      switchedMass (functionalIndex j) := by
  rw [← actualMass_eq_native_K alpha ha j]
  exact actual_M12_to_M15_le_literal alpha ha j

end
end ImbalancedChen.P2SeedOmegaSwitchedMassFour
