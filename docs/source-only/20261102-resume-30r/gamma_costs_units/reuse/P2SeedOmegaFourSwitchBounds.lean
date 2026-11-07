import ImbalancedChen.P2SeedOmegaLiteralFunctional
import MathlibNt.Wu2008DoubleSieve.GeoMassFullReduction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original Gamma16..19 actual Buchstab masses are bounded by the four
literal logarithmic masses in the seed functional. The next-to-last
coordinate is retained in the actual kernel and its legal nonunit gate.
The factorials come from the existing proved ordered-domain Lebesgue
integral, not definitions or combinatorial guesses. This is an analytic
mass bound, not an enhanced counting or positive-product licence.
-/

namespace ImbalancedChen.P2SeedOmegaFourSwitchBounds
noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators
open Wu2008DoubleSieve
open SecondFunctionalGeometricMass SecondFunctionalJointTail
open P2SeedOmegaLiteralFibre

def p : SecondFunctionalParameters := ⟨s,s0,phi1,phi2,phi3⟩

theorem p_mother : p.MotherAdmissible := by
  constructor <;> norm_num [p,s,s0,phi1,phi2,phi3]

theorem p_s_two : (2 : ℝ)≤p.s := by norm_num [p,s]

/-- Discarding precisely the selected reciprocal coordinate at its true
lower endpoint. The remaining integral is the ACTUAL ordered mass. -/
theorem selected_ordered_log_cap {n : ℕ} (j : Fin n) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    selectedOrderedMass j a b ≤ (1/a)*(Real.log (b/a)^n/(n.factorial:ℝ)) := by
  have hi := OriginalBlocks.ordered_selected_integrable j (b:=b) ha
  have hp := OrderedPure.pureOrderedMass_integrable n (b:=b) ha
  change (∫ t in orderedDomain n a b,geometricWeight j t)≤_
  calc
    _ ≤ ∫ t in orderedDomain n a b,(1/a)*continuousDensity t := by
      apply setIntegral_mono_on hi (hp.const_mul (1/a))
        (OrderedPure.orderedDomain_measurable n a b)
      intro t ht
      have hd : 0≤continuousDensity t := by
        unfold continuousDensity
        exact Finset.prod_nonneg (fun i _ => div_nonneg zero_le_one (ha.le.trans (ht.1 i).1))
      calc
        _ = (1/t j)*continuousDensity t := by unfold geometricWeight; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ha (ht.1 j).1) hd
    _ = _ := by
      rw [integral_const_mul]
      change (1/a)*pureOrderedMass n a b=_
      rw [OrderedPure.pureOrderedMass_eq_log n ha hab]

theorem geometric16_cap : fourMass p 0≤P2SeedOmegaLiteralFunctional.switchedMass 7 := by
  rw [OriginalBlocks.fourMass_zero_blocks]
  have h := selected_ordered_log_cap (2 : Fin 4)
    (a:=1/p.kappa2) (b:=1/p.kappa3)
    (by norm_num [p,phi2]) (by norm_num [p,phi2,phi3])
  norm_num [p,phi2,phi3,P2SeedOmegaLiteralFunctional.switchedMass,
    P2SeedOmegaLiteralFunctional.l23] at h ⊢
  nlinarith only [h]

theorem geometric17_cap : fourMass p 1≤P2SeedOmegaLiteralFunctional.switchedMass 8 := by
  rw [OriginalBlocks.fourMass_one_blocks p p_mother p_s_two]
  have h := selected_ordered_log_cap (2 : Fin 3)
    (a:=1/p.kappa2) (b:=1/p.kappa3)
    (by norm_num [p,phi2]) (by norm_num [p,phi2,phi3])
  have hlog : 0≤Real.log ((1/p.s)/(1/p.kappa3)) := by
    apply Real.log_nonneg
    norm_num [p,s,phi3]
  have hm := mul_le_mul_of_nonneg_right h hlog
  norm_num [p,s,phi2,phi3,P2SeedOmegaLiteralFunctional.switchedMass,
    P2SeedOmegaLiteralFunctional.l23,P2SeedOmegaLiteralFunctional.l3b] at hm ⊢
  nlinarith only [hm]

theorem geometric18_cap : fourMass p 2≤P2SeedOmegaLiteralFunctional.switchedMass 9 := by
  rw [OriginalBlocks.fourMass_two_blocks p p_mother p_s_two,
    OrderedPure.pureOrderedMass_eq_log 2 (by norm_num [p,phi2])
      (by norm_num [p,phi2,phi3])]
  have h := selected_ordered_log_cap (0 : Fin 2)
    (a:=1/p.kappa3) (b:=1/p.s)
    (by norm_num [p,phi3]) (by norm_num [p,s,phi3])
  have hm := mul_le_mul_of_nonneg_left h
    (show 0≤Real.log ((1/p.kappa3)/(1/p.kappa2))^2/(2:ℝ) by positivity)
  norm_num [p,s,phi2,phi3,P2SeedOmegaLiteralFunctional.switchedMass,
    P2SeedOmegaLiteralFunctional.l23,P2SeedOmegaLiteralFunctional.l3b] at hm ⊢
  nlinarith only [hm]

theorem geometric19_cap : fourMass p 3≤P2SeedOmegaLiteralFunctional.switchedMass 10 := by
  rw [OriginalBlocks.fourMass_three_blocks p p_mother p_s_two]
  have h := selected_ordered_log_cap (1 : Fin 3)
    (a:=1/p.kappa3) (b:=1/p.s)
    (by norm_num [p,phi3]) (by norm_num [p,s,phi3])
  have hlog : 0≤Real.log ((1/p.kappa2)/(1/p.kappa1)) := by
    apply Real.log_nonneg
    norm_num [p,phi1,phi2]
  have hm := mul_le_mul_of_nonneg_left h hlog
  norm_num [p,s,phi1,phi2,phi3,P2SeedOmegaLiteralFunctional.switchedMass,
    P2SeedOmegaLiteralFunctional.l12,P2SeedOmegaLiteralFunctional.l3b] at hm ⊢
  nlinarith only [hm]

/-- The original legal Buchstab kernel is bounded BEFORE its legal gate
is dropped. This uses the proved global omega≤1, including arguments<2. -/
theorem original_four_kernel_le (alpha : ℝ) {t : Fin 4 → ℝ}
    (ht : t ∈ continuousCube 4) :
    FourPrimeContinuous.G alpha t*continuousDensity t≤geometricWeight (2 : Fin 4) t := by
  have hd := continuousDensity_nonneg ht
  have hw : 0<t 2 := by linarith [(ht 2 (mem_univ 2)).1]
  by_cases hl : t ∈ HighNonunitLegal.legal (2 : Fin 4) alpha
  · rw [HighNonunitLegal.G_of_legal hl]
    have hu := HighNonunitLegal.argument_ge_one ht hl
    have hb := div_le_div_of_nonneg_right (LiLiuPrereqBuchstab.buchstab_le_one hu) hw.le
    have hm := mul_le_mul_of_nonneg_right hb hd
    convert hm using 1 <;> unfold geometricWeight <;> ring
  · rw [HighNonunitLegal.G_of_illegal hl,zero_mul]
    exact geometricWeight_nonneg 2 ht

def originalFourMass (alpha : ℝ) (j : Fin 4) : ℝ :=
  ∫ t in massDomainFour (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j,
    FourPrimeContinuous.G alpha t*continuousDensity t

theorem originalFourMass_le_geometric (alpha : ℝ) (j : Fin 4) :
    originalFourMass alpha j≤fourMass p j := by
  have hp : FourPrimeContinuous.CompactParameters
      (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) := by
    norm_num [FourPrimeContinuous.CompactParameters,p,s,phi1,phi2,phi3]
  have hsub := massDomainFour_subset_cube hp j
  exact setIntegral_mono_on (HighNonunitLegal.weighted_integrable_on 2 alpha hsub)
    (geometricWeight_integrable 2 hsub) (massDomainFour_measurable _ _ _ _ j)
    (fun t ht => original_four_kernel_le alpha (hsub ht))

/-- The four ACTUAL four-dimensional omega integrals are bounded by
entries16..19 of the literal seed functional, with no mass-bound premise. -/
theorem original_four_masses_log_caps (alpha : ℝ) :
    originalFourMass alpha 0≤P2SeedOmegaLiteralFunctional.switchedMass 7 ∧
    originalFourMass alpha 1≤P2SeedOmegaLiteralFunctional.switchedMass 8 ∧
    originalFourMass alpha 2≤P2SeedOmegaLiteralFunctional.switchedMass 9 ∧
    originalFourMass alpha 3≤P2SeedOmegaLiteralFunctional.switchedMass 10 :=
  ⟨(originalFourMass_le_geometric alpha 0).trans geometric16_cap,
   (originalFourMass_le_geometric alpha 1).trans geometric17_cap,
   (originalFourMass_le_geometric alpha 2).trans geometric18_cap,
   (originalFourMass_le_geometric alpha 3).trans geometric19_cap⟩

end
end ImbalancedChen.P2SeedOmegaFourSwitchBounds
