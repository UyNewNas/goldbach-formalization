import ImbalancedChen.P2SeedOmegaSwitchedMassFour
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A quantitative common approximation primitive absent from the qualitative
native continuity API: the FOUR actual original switched masses have an
explicit modulus on the ENTIRE admitted alpha half-line. The pinned true
global Buchstab Lipschitz theorem is reused; no new differentiability or
monotonicity assertion about Buchstab is made. Fixed original colour/order
domains are retained, including their continuous endpoints. This proves
alpha approximation only, not the missing K/4 count licence.
-/

namespace ImbalancedChen.P2SeedOmegaSwitchedAlphaModulus

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SecondFunctionalJointTail
open P2SeedOmegaSwitchedKernelFour
open P2SeedOmegaSwitchedMassFour
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b omegaCap)
open P2SeedOmegaLiteralFunctional (switchedMass)

theorem selected_coordinate_ge_a0 (j : Fin 4) {x : Point} (hx : x ∈ domain j) :
    a0≤x 1 := by
  rw [domain_literal] at hx
  fin_cases j
  all_goals
    norm_num [a0,a1,a2,a3,b] at hx ⊢
    rcases hx with ⟨h0,h1,h2,h3,h4,h5,h01,h12⟩
    linarith only [h2]

theorem geometric_mass_nonnegative (j : Fin 4) :
    0≤lowerMass nativeParameters (nativeIndex j) := by
  unfold lowerMass geometricMass
  rw [← native_domain_eq j]
  exact setIntegral_nonneg (domain_measurable j)
    (fun x hx => geometricWeight_nonneg 1 (domain_subset_cube j hx))

/-- Pointwise alpha regularity before integration, with the actual
next-to-last cutoff v retained in both argument and kernel denominator. -/
theorem actualKernel_alpha_modulus (j : Fin 4) {alpha beta : ℝ}
    (ha : 2≤alpha) (hb : 2≤beta) {x : Point} (hx : x ∈ domain j) :
    |actualKernel alpha x-actualKernel beta x|≤
      (|alpha-beta|/a0)*geometricWeight (1 : Fin 3) x := by
  have hpos := coordinates_positive j hx
  have hd : 0<x 0*x 1^2*x 2 := by positivity
  have hA : 1≤argument alpha x :=
    (original_floor_ge_one j).trans (argument_ge_original_floor j ha hx)
  have hB : 1≤argument beta x :=
    (original_floor_ge_one j).trans (argument_ge_original_floor j hb hx)
  have hw := primeOrdered_buchstab_lipschitz hA hB
  have harg : argument alpha x-argument beta x=(alpha-beta)/x 1 := by
    unfold argument
    ring
  rw [harg,abs_div,abs_of_pos hpos.2.1] at hw
  have hsmall : |alpha-beta|/x 1≤|alpha-beta|/a0 :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num [a0])
      (selected_coordinate_ge_a0 j hx)
  have hg : 0≤geometricWeight (1 : Fin 3) x :=
    geometricWeight_nonneg 1 (domain_subset_cube j hx)
  calc
    _ = |buchstab (argument alpha x)-buchstab (argument beta x)|/
        (x 0*x 1^2*x 2) := by
      rw [actualKernel,actualKernel,← sub_div,abs_div,abs_of_pos hd]
    _ ≤ (|alpha-beta|/x 1)/(x 0*x 1^2*x 2) :=
      div_le_div_of_nonneg_right hw hd.le
    _ = (|alpha-beta|/x 1)*geometricWeight (1 : Fin 3) x := by
      rw [geometricWeight_literal]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hg

/-- Quantitative integral control for arbitrary alpha,beta >=2. Its
coefficient is the actual evaluated geometric integral, not a supplied
oscillation bound or a finite alpha-strip premise. -/
theorem actualMass_alpha_modulus (j : Fin 4) {alpha beta : ℝ}
    (ha : 2≤alpha) (hb : 2≤beta) :
    |actualMass alpha j-actualMass beta j|≤
      (|alpha-beta|/a0)*lowerMass nativeParameters (nativeIndex j) := by
  have hiA := actualKernel_integrable j ha
  have hiB := actualKernel_integrable j hb
  have hidiff := hiA.sub hiB
  have hiabs : IntegrableOn (fun x => |actualKernel alpha x-actualKernel beta x|)
      (domain j) := by
    simpa only [Real.norm_eq_abs] using hidiff.norm
  have hg : IntegrableOn (geometricWeight (1 : Fin 3)) (domain j) :=
    geometricWeight_integrable 1 (domain_subset_cube j)
  have hm := setIntegral_mono_on hiabs (hg.const_mul (|alpha-beta|/a0))
    (domain_measurable j) (fun x hx => actualKernel_alpha_modulus j ha hb hx)
  have hgeom : (∫ x in domain j,geometricWeight (1 : Fin 3) x)=
      lowerMass nativeParameters (nativeIndex j) := by
    unfold lowerMass geometricMass
    rw [← native_domain_eq j]
  calc
    _ = |∫ x in domain j,actualKernel alpha x-actualKernel beta x| := by
      rw [integral_sub hiA hiB]
      rfl
    _ ≤ ∫ x in domain j,|actualKernel alpha x-actualKernel beta x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in domain j,(|alpha-beta|/a0)*geometricWeight (1 : Fin 3) x := hm
    _ = _ := by rw [integral_const_mul,hgeom]

/-- Same modulus in the exact literal coefficient consumed downstream. -/
theorem literal_alpha_modulus (j : Fin 4) {alpha beta : ℝ}
    (ha : 2≤alpha) (hb : 2≤beta) :
    |actualMass alpha j-actualMass beta j|≤
      (|alpha-beta|/(a0*omegaCap))*switchedMass (functionalIndex j) := by
  have h := actualMass_alpha_modulus j ha hb
  rw [literal_switchedMass_eq_native_integral]
  convert h using 1 <;>
    field_simp [P2SeedOmegaGlobalEnvelope.omegaCap_positive.ne',
      ne_of_gt (show 0<a0 by norm_num [a0])]
  <;> ring

def commonModulusConstant : ℝ :=
  1+∑ j : Fin 4,lowerMass nativeParameters (nativeIndex j)/a0

theorem commonModulusConstant_positive : 0<commonModulusConstant := by
  have hs : 0≤∑ j : Fin 4,lowerMass nativeParameters (nativeIndex j)/a0 :=
    Finset.sum_nonneg (fun j _ => div_nonneg (geometric_mass_nonnegative j)
      (by norm_num [a0]))
  dsimp [commonModulusConstant]
  linarith only [hs]

/-- One explicit delta works simultaneously for all four masses on the
whole half-line, so choosing a finite alpha mesh never requires a new
analytic mass premise or a new modulus at every node. -/
theorem common_alpha_approximation {epsilon : ℝ} (he : 0<epsilon) :
    0<epsilon/commonModulusConstant ∧
    ∀ (j : Fin 4) (alpha beta : ℝ),2≤alpha → 2≤beta →
      |alpha-beta|<epsilon/commonModulusConstant →
      |actualMass alpha j-actualMass beta j|<epsilon := by
  have hC := commonModulusConstant_positive
  refine ⟨div_pos he hC,?_⟩
  intro j alpha beta ha hb hdist
  have hsum : lowerMass nativeParameters (nativeIndex j)/a0≤
      ∑ k : Fin 4,lowerMass nativeParameters (nativeIndex k)/a0 :=
    Finset.single_le_sum (fun k _ => div_nonneg (geometric_mass_nonnegative k)
      (by norm_num [a0])) (Finset.mem_univ j)
  have hcoeff : lowerMass nativeParameters (nativeIndex j)/a0≤commonModulusConstant := by
    dsimp [commonModulusConstant]
    linarith only [hsum]
  have hm := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (alpha-beta))
  have hlast := (lt_div_iff₀ hC).mp hdist
  have hmass := actualMass_alpha_modulus j ha hb
  calc
    _ ≤ (lowerMass nativeParameters (nativeIndex j)/a0)*|alpha-beta| := by
      convert hmass using 1 <;> ring
    _ ≤ commonModulusConstant*|alpha-beta| := hm
    _ < epsilon := by simpa only [mul_comm] using hlast

end
end ImbalancedChen.P2SeedOmegaSwitchedAlphaModulus
