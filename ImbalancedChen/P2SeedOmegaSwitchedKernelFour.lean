import ImbalancedChen.P2SeedOmegaGlobalEnvelope
import MathlibNt.Wu2008DoubleSieve.GeoMassOriginalBlocks

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original switched M12,M13,M14,M15, with the NEXT-TO-LAST prime as
quotient cutoff. These are the actual pinned continuous domains/kernels,
at the original five parameters. The four exact argument floors hold for
every alpha >= 2. M14 has arguments below two; the proved global envelope
max(1/u,c_omega), together with the exact corner floor, pays that range.
No supplied cap, final mass, seed saving or numerical receipt is an input.
The original arithmetic-to-kernel asymptotic remains a separate licence.
-/

namespace ImbalancedChen.P2SeedOmegaSwitchedKernelFour

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped BigOperators
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SecondFunctionalJointTail
open P2SeedOmegaLiteralFibre (s s0 phi1 phi2 phi3 a0 a1 a2 a3 b omegaCap)

abbrev Point := Fin 3 → ℝ

def nativeParameters : SecondFunctionalParameters := ⟨s,s0,phi1,phi2,phi3⟩
def nativeIndex : Fin 4 → Fin 6 := ![2,3,4,5]
def functionalIndex : Fin 4 → Fin 13 := ![3,4,5,6]
def argumentFloor : Fin 4 → ℝ := ![3801/1100,103299/38830,3136/1765,15388/7975]
def domain (j : Fin 4) : Set Point :=
  LowerTripleContinuous.D a0 a1 a2 a3 b (nativeIndex j)
def argument (alpha : ℝ) (x : Point) : ℝ :=
  (alpha-(x 0+x 1+x 2))/x 1
def actualKernel (alpha : ℝ) (x : Point) : ℝ :=
  buchstab (argument alpha x)/(x 0*x 1^2*x 2)
def actualMass (alpha : ℝ) (j : Fin 4) : ℝ :=
  ∫ x in domain j,actualKernel alpha x

theorem native_mother : nativeParameters.MotherAdmissible := by
  constructor <;> norm_num [nativeParameters,s,s0,phi1,phi2,phi3]

theorem native_compact : LowerTripleContinuous.CompactParameters a0 a1 a2 a3 b := by
  norm_num [LowerTripleContinuous.CompactParameters,a0,a1,a2,a3,b]

theorem native_domain_eq (j : Fin 4) : domain j=
    LowerTripleContinuous.D (1/nativeParameters.S) (1/nativeParameters.kappa1)
      (1/nativeParameters.kappa2) (1/nativeParameters.kappa3)
      (1/nativeParameters.s) (nativeIndex j) := by
  norm_num [domain,nativeParameters,s,s0,phi1,phi2,phi3,a0,a1,a2,a3,b]

theorem domain_measurable (j : Fin 4) : MeasurableSet (domain j) :=
  LowerTripleContinuous.D_measurable a0 a1 a2 a3 b (nativeIndex j)

theorem domain_subset_cube (j : Fin 4) : domain j ⊆ continuousCube 3 :=
  LowerTripleContinuous.D_subset_cube native_compact (nativeIndex j)

theorem coordinates_positive (j : Fin 4) {x : Point} (hx : x ∈ domain j) :
    0<x 0 ∧ 0<x 1 ∧ 0<x 2 := by
  have h := domain_subset_cube j hx
  have h0 := (h 0 (mem_univ _)).1
  have h1 := (h 1 (mem_univ _)).1
  have h2 := (h 2 (mem_univ _)).1
  exact ⟨by linarith only [h0],by linarith only [h1],by linarith only [h2]⟩

/-- These are exactly the original closed continuous colour/order bands.
No claim about eliminating arithmetic endpoint atoms is made here. -/
theorem domain_literal (j : Fin 4) (x : Point) : x ∈ domain j ↔
    (if j=0 then
      a0≤x 0 ∧ x 0≤a1 ∧ a0≤x 1 ∧ x 1≤a1 ∧ a3≤x 2 ∧ x 2≤b ∧ x 0≤x 1 ∧ x 1≤x 2
    else if j=1 then
      a0≤x 0 ∧ x 0≤a1 ∧ a1≤x 1 ∧ x 1≤a2 ∧ a2≤x 2 ∧ x 2≤b ∧ x 0≤x 1 ∧ x 1≤x 2
    else if j=2 then
      a0≤x 0 ∧ x 0≤a1 ∧ a2≤x 1 ∧ x 1≤b ∧ a2≤x 2 ∧ x 2≤b ∧ x 0≤x 1 ∧ x 1≤x 2
    else
      a1≤x 0 ∧ x 0≤a2 ∧ a2≤x 1 ∧ x 1≤a3 ∧ a3≤x 2 ∧ x 2≤b ∧ x 0≤x 1 ∧ x 1≤x 2) := by
  fin_cases j <;> rfl

theorem argument_ge_original_floor (j : Fin 4) {alpha : ℝ} (ha : 2≤alpha)
    {x : Point} (hx : x ∈ domain j) : argumentFloor j≤argument alpha x := by
  have hv := (coordinates_positive j hx).2.1
  unfold argument
  apply (le_div_iff₀ hv).mpr
  rw [domain_literal] at hx
  fin_cases j
  all_goals
    norm_num [argumentFloor,a0,a1,a2,a3,b] at hx ⊢
    rcases hx with ⟨h0,h1,h2,h3,h4,h5,h01,h12⟩
    linarith only [ha,h1,h3,h5]

theorem original_floor_ge_one (j : Fin 4) : (1:ℝ)≤argumentFloor j := by
  fin_cases j <;> norm_num [argumentFloor]

theorem original_floor_times_cap_gt_one (j : Fin 4) :
    (1:ℝ)<argumentFloor j*omegaCap := by
  fin_cases j <;> norm_num [argumentFloor,omegaCap]

theorem actual_buchstab_le_cap (j : Fin 4) {alpha : ℝ} (ha : 2≤alpha)
    {x : Point} (hx : x ∈ domain j) : buchstab (argument alpha x)≤omegaCap := by
  have hf := argument_ge_original_floor j ha hx
  have harg : 1≤argument alpha x := (original_floor_ge_one j).trans hf
  have harg0 : 0<argument alpha x := zero_lt_one.trans_le harg
  have hm := mul_le_mul_of_nonneg_right hf P2SeedOmegaGlobalEnvelope.omegaCap_positive.le
  have hinv : 1/argument alpha x≤omegaCap := by
    apply (div_le_iff₀ harg0).mpr
    have hstrict := original_floor_times_cap_gt_one j
    nlinarith only [hm,hstrict]
  exact (P2SeedOmegaGlobalEnvelope.actual_buchstab_original_global_envelope harg).trans
    (max_le hinv le_rfl)

theorem geometricWeight_literal (x : Point) :
    geometricWeight (1 : Fin 3) x=1/(x 0*x 1^2*x 2) := by
  simp only [geometricWeight,continuousDensity,Fin.prod_univ_succ,Fin.prod_univ_zero,
    mul_one,div_eq_mul_inv,mul_inv_rev,pow_two]
  ring

theorem actualKernel_le_cap_geometric (j : Fin 4) {alpha : ℝ} (ha : 2≤alpha)
    {x : Point} (hx : x ∈ domain j) :
    actualKernel alpha x≤omegaCap*geometricWeight (1 : Fin 3) x := by
  have hp := coordinates_positive j hx
  have hd : 0<x 0*x 1^2*x 2 := by positivity
  have hw := actual_buchstab_le_cap j ha hx
  rw [actualKernel,geometricWeight_literal]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hw hd.le

/-- There is no quotient-one surface for ANY admitted alpha, not just
for alpha=2. All continuous-domain coordinate sums are strictly smaller. -/
theorem no_unit_surface (j : Fin 4) {alpha : ℝ} (ha : 2≤alpha)
    {x : Point} (hx : x ∈ domain j) : x 0+x 1+x 2<alpha := by
  have hc := domain_subset_cube j hx
  have h0 := (hc 0 (mem_univ _)).2
  have h1 := (hc 1 (mem_univ _)).2
  have h2 := (hc 2 (mem_univ _)).2
  linarith only [h0,h1,h2,ha]

theorem actualKernel_integrable (j : Fin 4) {alpha : ℝ} (ha : 2≤alpha) :
    IntegrableOn (actualKernel alpha) (domain j) :=
  LowerTripleContinuous.literal_integrable native_compact ha (nativeIndex j)

theorem actualMass_eq_native_K (alpha : ℝ) (ha : 2≤alpha) (j : Fin 4) :
    actualMass alpha j=LowerTripleContinuous.K a0 a1 a2 a3 b (nativeIndex j) alpha := by
  symm
  exact LowerTripleContinuous.K_literal native_compact ha (nativeIndex j)

/-- An actual, integrable Buchstab mass is bounded by its actual native
geometric integral. This proves the uniform analytic envelope step. -/
theorem actualMass_le_cap_native_lowerMass (alpha : ℝ) (ha : 2≤alpha) (j : Fin 4) :
    actualMass alpha j≤omegaCap*lowerMass nativeParameters (nativeIndex j) := by
  have hg : IntegrableOn (geometricWeight (1 : Fin 3)) (domain j) :=
    geometricWeight_integrable 1 (domain_subset_cube j)
  have hm : (∫ x in domain j,actualKernel alpha x)≤
      ∫ x in domain j,omegaCap*geometricWeight (1 : Fin 3) x :=
    setIntegral_mono_on (actualKernel_integrable j ha) (hg.const_mul omegaCap)
      (domain_measurable j) (fun x hx => actualKernel_le_cap_geometric j ha hx)
  change actualMass alpha j≤_ at hm
  rw [integral_const_mul] at hm
  have hmass : (∫ x in domain j,geometricWeight (1 : Fin 3) x)=
      lowerMass nativeParameters (nativeIndex j) := by
    unfold lowerMass geometricMass
    rw [← native_domain_eq j]
  rwa [hmass] at hm

end
end ImbalancedChen.P2SeedOmegaSwitchedKernelFour
