import ImbalancedChen.P2SeedOmegaGlobalEnvelope
import MathlibNt.Wu2008DoubleSieve.GeoMassElementaryPrimitives

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original switched domains 9,10,11 and their actual alpha-dependent
Buchstab kernels. The geometric integral suppliers are the pinned
GeoMass modules, not a second model of the ordered masses. The sharp
omegaCap is proved in P2SeedOmegaGlobalEnvelope. No mass inequality or
count estimate is a premise; the same-Q arithmetic count-to-integral
supplier remains separate from these genuine continuous integrals.
-/

namespace ImbalancedChen.P2SeedOmegaFirstThreeKernel
noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SecondFunctionalGeometricMass
open Wu2008DoubleSieve.SecondFunctionalJointTail
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b phi1 phi2 phi3 s omegaCap)

abbrev Point := Fin 3 → ℝ

/-- Exactly [a1,a3]^3_up, [a1,a2]^2_up[a2,b], and
[a1,a2][a2,a3]^2_up. Coordinate1 is the penultimate prime. -/
def domain : Fin 3 → Set Point := ![
  orderedDomain 3 a1 a3,
  LowerTripleContinuous.D a0 a1 a2 a3 b 0,
  LowerTripleContinuous.D a0 a1 a2 a3 b 1]

def upperZero : Fin 3 → ℝ := ![a3,a2,a2]
def upperOne : Fin 3 → ℝ := ![a3,a2,a3]
def upperTwo : Fin 3 → ℝ := ![a3,b,a3]
def cornerMinimum : Fin 3 → ℝ := ![
  2*phi3-3,
  2*phi2-2-phi2/s,
  2*phi3-phi3/phi2-2]

def argument (alpha : ℝ) (t : Point) : ℝ :=
  (alpha-(t 0+t 1+t 2))/t 1
def actualKernel (alpha : ℝ) (t : Point) : ℝ :=
  HighNonunitLegal.G (1 : Fin 3) alpha t*continuousDensity t
def actualMass (alpha : ℝ) (j : Fin 3) : ℝ := ∫ t in domain j,actualKernel alpha t
def geometric (j : Fin 3) : ℝ := geometricMass (1 : Fin 3) (domain j)

theorem domain_coordinates (j : Fin 3) {t : Point} (ht : t ∈ domain j) :
    a1≤t 0 ∧ t 0≤upperZero j ∧ a1≤t 1 ∧ t 1≤upperOne j ∧
      a1≤t 2 ∧ t 2≤upperTwo j := by
  fin_cases j
  · change t ∈ orderedDomain 3 a1 a3 at ht
    exact ⟨(ht.1 0).1,(ht.1 0).2,(ht.1 1).1,(ht.1 1).2,(ht.1 2).1,(ht.1 2).2⟩
  · change t ∈ LowerTripleContinuous.D a0 a1 a2 a3 b 0 at ht
    rw [(LowerTripleContinuous.D_six_literal a0 a1 a2 a3 b).1] at ht
    rcases ht with ⟨h0,h1,h2,h3,h4,h5,_,_⟩
    exact ⟨h0,h1,h2,h3,(by norm_num [a1,a2] : a1≤a2).trans h4,h5⟩
  · change t ∈ LowerTripleContinuous.D a0 a1 a2 a3 b 1 at ht
    rw [(LowerTripleContinuous.D_six_literal a0 a1 a2 a3 b).2.1] at ht
    rcases ht with ⟨h0,h1,h2,h3,h4,h5,_,_⟩
    exact ⟨h0,h1,(by norm_num [a1,a2] : a1≤a2).trans h2,h3,
      (by norm_num [a1,a2] : a1≤a2).trans h4,h5⟩

theorem upper_bounds (j : Fin 3) : upperZero j≤b ∧ upperOne j≤b ∧ upperTwo j≤b := by
  fin_cases j <;> norm_num [upperZero,upperOne,upperTwo,a2,a3,b]

theorem domain_subset_cube (j : Fin 3) : domain j ⊆ continuousCube 3 := by
  intro t ht
  have h := domain_coordinates j ht
  have hb := upper_bounds j
  intro i _
  fin_cases i
  · exact ⟨(by norm_num [a1] : (1/10:ℝ)≤a1).trans h.1,
      h.2.1.trans (hb.1.trans (by norm_num [b]))⟩
  · exact ⟨(by norm_num [a1] : (1/10:ℝ)≤a1).trans h.2.2.1,
      h.2.2.2.1.trans (hb.2.1.trans (by norm_num [b]))⟩
  · exact ⟨(by norm_num [a1] : (1/10:ℝ)≤a1).trans h.2.2.2.2.1,
      h.2.2.2.2.2.trans (hb.2.2.trans (by norm_num [b]))⟩

theorem domain_measurable (j : Fin 3) : MeasurableSet (domain j) := by
  fin_cases j
  · exact SelectedFibres.orderedDomain_measurable 3 a1 a3
  · exact LowerTripleContinuous.D_measurable a0 a1 a2 a3 b 0
  · exact LowerTripleContinuous.D_measurable a0 a1 a2 a3 b 1

/-- Uniform corner bounds, with no upper restriction on alpha. -/
theorem argument_lower (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha)
    {t : Point} (ht : t ∈ domain j) : cornerMinimum j≤argument alpha t := by
  have h := domain_coordinates j ht
  have hv : 0<t 1 := (by norm_num [a1] : (0:ℝ)<a1).trans_le h.2.2.1
  apply (le_div_iff₀ hv).mpr
  fin_cases j
  all_goals dsimp [cornerMinimum,upperZero,upperOne,upperTwo,a2,a3,b,phi2,phi3,s] at h ⊢
  all_goals linarith only [ha,h.2.1,h.2.2.2.1,h.2.2.2.2.2]

theorem corner_strict_slack (j : Fin 3) :
    1<cornerMinimum j ∧ 1<omegaCap*cornerMinimum j := by
  fin_cases j <;> norm_num [cornerMinimum,omegaCap,phi2,phi3,s]

theorem no_nonunit_truncation (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha)
    {t : Point} (ht : t ∈ domain j) : (∑ i,t i)+t 1≤alpha :=
  LowerTripleContinuous.cube_legal ha (domain_subset_cube j ht)

/-- The sum is strictly below two on all three whole closed domains.
Consequently the unit-quotient surface is EMPTY, for every alpha>=2. -/
theorem sum_lt_alpha (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha)
    {t : Point} (ht : t ∈ domain j) : (∑ i,t i)<alpha := by
  have h := domain_coordinates j ht
  have hb := upper_bounds j
  have h0 := h.2.1.trans hb.1
  have h1 := h.2.2.2.1.trans hb.2.1
  have h2 := h.2.2.2.2.2.trans hb.2.2
  rw [LowerTripleContinuous.sum_literal]
  dsimp [b] at h0 h1 h2
  linarith only [ha,h0,h1,h2]

theorem unit_surface_empty (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha) :
    {t : Point | t ∈ domain j ∧ (∑ i,t i)=alpha}=∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro t ht
  exact (ne_of_lt (sum_lt_alpha j ha ht.1)) ht.2

theorem actual_kernel_literal (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha)
    {t : Point} (ht : t ∈ domain j) :
    actualKernel alpha t=LiLiuPrereqBuchstab.buchstab (argument alpha t)/
      (t 0*t 1^2*t 2) :=
  LowerTripleContinuous.weighted_legal_literal (no_nonunit_truncation j ha ht)

/-- Both branches of the true global envelope are paid. Corners below
two use 1/argument<=omegaCap, rather than deleting that region. -/
theorem actual_omega_cap (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha)
    {t : Point} (ht : t ∈ domain j) :
    LiLiuPrereqBuchstab.buchstab (argument alpha t)≤omegaCap := by
  have hl := argument_lower j ha ht
  have hs := corner_strict_slack j
  have hm := mul_le_mul_of_nonneg_left hl P2SeedOmegaGlobalEnvelope.omegaCap_positive.le
  have harg : 0<argument alpha t := zero_lt_one.trans (hs.1.trans_le hl)
  have hinv : 1/argument alpha t≤omegaCap :=
    (div_le_iff₀ harg).mpr (by nlinarith only [hm,hs.2])
  have he := P2SeedOmegaGlobalEnvelope.actual_buchstab_original_global_envelope
    (hs.1.le.trans hl)
  exact he.trans (max_le hinv le_rfl)

theorem actualKernel_le_geometric (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha)
    {t : Point} (ht : t ∈ domain j) :
    actualKernel alpha t≤omegaCap*geometricWeight (1 : Fin 3) t := by
  have hc := domain_subset_cube j ht
  have hv : 0<t 1 := by linarith [(hc 1 (mem_univ _)).1]
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (actual_omega_cap j ha ht) hv.le)
    (continuousDensity_nonneg hc)
  change LowerTripleContinuous.G alpha t*continuousDensity t≤_
  rw [LowerTripleContinuous.G_cube_literal ha hc]
  convert hh using 1 <;> dsimp [geometricWeight,argument] <;> ring

theorem actualMass_le_geometric (j : Fin 3) {alpha : ℝ} (ha : 2≤alpha) :
    actualMass alpha j≤omegaCap*geometric j := by
  calc
    _ ≤ ∫ t in domain j,omegaCap*geometricWeight (1 : Fin 3) t := by
      apply setIntegral_mono_on
        (HighNonunitLegal.weighted_integrable_on 1 alpha (domain_subset_cube j))
        ((geometricWeight_integrable 1 (domain_subset_cube j)).const_mul omegaCap)
        (domain_measurable j)
      intro t ht
      exact actualKernel_le_geometric j ha ht
    _ = _ := integral_const_mul _ _

end
end ImbalancedChen.P2SeedOmegaFirstThreeKernel
