import ImbalancedChen.Part3ActualPrincipalCoreFiniteBound
import ImbalancedChen.Part3OriginalOwnedS1PolynomialCaps
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium appendix (15): ordinary rough-divisor moment and actual
polynomial support pay the literal r sum. The same actual strict-receiver
Lambda, q profile and owned key are retained from the finite Gram theorem.
-/

namespace ImbalancedChen.Part3.ActualPrincipalRoughMeanSourceOnly

noncomputable section
open Classical Finset MeasureTheory
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open OriginalOwnedS1PolynomialCaps OriginalPaperPsiCoprimeCount
open OriginalGevreyFinalPsi20261028
open ActualFilteredPrimitiveSWSourceOnly ActualCrudeWeightedVarianceSourceOnly
open ActualLowConductorQuotientSumSourceOnly ActualMediumVarianceAtomBindingSourceOnly
open ActualLambdaPrincipalDivisorBindingSourceOnly ActualPrincipalCoreFiniteBoundSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The original rough block has an ordinary fixed-order divisor mean.
No pointwise r^epsilon bound is used on the log-sized remainder. -/
theorem actual_rough_divisor_mean (k : Key) (s : ℕ) :
    (∑ r ∈ dyadicWindow k.w, tau r^s) ≤
      (2*(roughNat k : ℝ))*(1+Real.log (2*(roughNat k : ℝ)))^(2^s-1) := by
  have hR := roughNat_pos k
  have hcap : (1 : ℝ) ≤ (2*roughNat k : ℕ) := by exact_mod_cast (show 1 ≤ 2*roughNat k by omega)
  have hsub : dyadicWindow k.w ⊆ Finset.Ioc 0 (2*roughNat k) := by
    intro r hr
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hr
    refine Finset.mem_Ioc.mpr ⟨hR.trans_le hlo,?_⟩
    simpa only [roughNat,pow_succ,mul_comm] using hhi.le
  calc
    _ ≤ ∑ r ∈ Finset.Ioc 0 (2*roughNat k), tau r^s :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => pow_nonneg (tau_nonneg r) s)
    _ ≤ _ := by
      have h := sum_fouvryTau_pow_le_real (k := 2) (r := s) (by norm_num) hcap
      simpa only [Nat.floor_natCast,fouvryTau_two,tau,Nat.cast_mul,Nat.cast_ofNat] using h

/-- Occupied original keys have a proved rough support, not an assumed
polynomial-size field. -/
theorem actual_rough_cap {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (hsigma : 0 ≤ sigma)
    (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z) :
    (roughNat k : ℝ) ≤ 4*atom.scale^2 := by
  have hR := (occupied_key_scales_le_physical_cap hk).2
  have hc := physical_cap_le_four_scale_sq hA hsigma
  exact hR.trans hc

def roughLogConstant : ℝ := 3+Real.log 8

theorem roughLogConstant_pos : 0 < roughLogConstant := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
  dsimp only [roughLogConstant]
  linarith

/-- The fixed rough moment logarithm is paid by one common log(x). -/
theorem actual_rough_log_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (hsigma : 0 ≤ sigma)
    (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (hx : 1 ≤ atom.scale) :
    1+Real.log (2*(roughNat k : ℝ)) ≤ roughLogConstant*(1+Real.log atom.scale) := by
  have hX : 0 < atom.scale := zero_lt_one.trans_le hx
  have hR : (0 : ℝ) < roughNat k := by exact_mod_cast roughNat_pos k
  have hcap : 2*(roughNat k : ℝ) ≤ 8*atom.scale^2 := by
    nlinarith [actual_rough_cap hA hsigma z k hk]
  have hl := Real.log_le_log (mul_pos (by norm_num) hR) hcap
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 2 hX.ne'),Real.log_pow] at hl
  have hxlog : 0 ≤ Real.log atom.scale := Real.log_nonneg hx
  have hc : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  dsimp only [roughLogConstant]
  nlinarith [mul_nonneg hc hxlog]

/-- Uniform manuscript (15) for the literal principal core, after actual
Lambda, q,d repetition, totient and ordinary rough-divisor means. -/
theorem uniformAuxiliarySW_actual_principalCore_log_saving
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        principalCore (F i) z k ≤
          C*(F i).U^2/(keyY (F i) k*(Real.log (F i).scale)^A) := by
  let E : ℕ := 2^(4+2*C0)-1
  have hAE : 0 < A+(E : ℝ) := by positivity
  obtain ⟨C,hC,x1,hx1,hbound⟩ :=
    uniformAuxiliarySW_actual_principalCore_finite F B C0 sigma kappa c0 hadmissible hSW
      hsigma (A+(E : ℝ)) hAE
  let Cout := 16*C*(2*roughLogConstant)^E
  have hCout : 0 < Cout := by dsimp only [Cout]; have hc := roughLogConstant_pos; positivity
  refine ⟨Cout,hCout,max x1 (Real.exp 1),lt_of_lt_of_le hx1 (le_max_left _ _),?_⟩
  intro i hx z k hk
  have hx1' : x1 ≤ (F i).scale := (le_max_left _ _).trans hx
  have hexp : Real.exp 1 ≤ (F i).scale := (le_max_right _ _).trans hx
  have hlog : 1 ≤ Real.log (F i).scale := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    simpa only [Real.log_exp] using h
  have hxscale : 1 ≤ (F i).scale := (le_of_lt hx1).trans hx1'
  let t := Real.log (F i).scale
  let N : ℝ := Nat.floor (2*(F i).U)
  let R : ℝ := roughNat k
  have ht : 0 < t := by dsimp only [t]; linarith
  have hR : 0 < R := by exact_mod_cast roughNat_pos k
  have hY : 0 < keyY (F i) k := by
    dsimp only [keyY,keyD]
    have hq := (hadmissible i).2.2.1
    positivity
  have hrough := actual_rough_divisor_mean k (4+2*C0)
  have hrl := actual_rough_log_le (hadmissible i) hsigma.le z k hk hxscale
  have hroughlog : 1+Real.log (2*R) ≤ 2*roughLogConstant*t := by
    have hc := roughLogConstant_pos
    dsimp only [t,R] at *
    nlinarith
  have hrough0 : 0 ≤ 1+Real.log (2*R) := by
    have hr1 : (1 : ℝ) ≤ roughNat k := by exact_mod_cast roughNat_pos k
    have h := Real.log_nonneg (show 1 ≤ 2*R by dsimp only [R]; linarith)
    linarith
  have hmean : (∑ r ∈ dyadicWindow k.w, tau r^(4+2*C0)) ≤
      2*R*(2*roughLogConstant)^E*t^E := by
    refine hrough.trans ?_
    have h := pow_le_pow_left₀ hrough0 hroughlog E
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*R)
    simpa only [mul_pow,mul_assoc] using h'
  have hN : N ≤ 2*(F i).U := Nat.floor_le (by linarith [(hadmissible i).1])
  have hNsq : N^2 ≤ 4*(F i).U^2 := by
    have hn0 : 0 ≤ N := Nat.cast_nonneg _
    nlinarith [pow_le_pow_left₀ hn0 hN 2]
  have hp := hbound i hx1' z k hk
  refine hp.trans ?_
  calc
    _ ≤ (2*C*N^2/(keyY (F i) k*R*t^(A+(E : ℝ)))) *
        (2*R*(2*roughLogConstant)^E*t^E) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = 4*C*(2*roughLogConstant)^E*N^2/(keyY (F i) k*t^A) := by
      rw [Real.rpow_add ht A (E : ℝ),Real.rpow_natCast]
      field_simp [hY.ne',hR.ne',(Real.rpow_pos_of_pos ht A).ne',pow_ne_zero E ht.ne']
      <;> ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc : 0 ≤ 4*C*(2*roughLogConstant)^E := by have hrc := roughLogConstant_pos; positivity
      have h := mul_le_mul_of_nonneg_left hNsq hc
      dsimp only [Cout]
      nlinarith

/-- The full-q positive envelope M*h0*principalCore. This definition
uses independently fixed alpha, same paperPsi and actual Lambda data.
The primitive q restriction is applied in the subsequent module. -/
def actualPrincipalRemainder (atom : MediumAtom) (z : ℝ) (k : Key) : ℝ :=
  atom.V*paperMass*principalCore atom z k

theorem paperMass_nonneg : 0 ≤ paperMass := integral_nonneg (fun x => paperPsi_nonneg x)

/-- Numerical form of (15) for the explicit full-q positive envelope.
The subsequent module proves the actual primitive-q subset bound. The
S3 zero-term centering/CRT binder remains owned by the S3 author. -/
theorem uniformAuxiliarySW_actual_principalRemainder
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        actualPrincipalRemainder (F i) z k ≤
          C*(F i).V*(F i).U^2/(keyY (F i) k*(Real.log (F i).scale)^A) := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_actual_principalCore_log_saving F B C0 sigma kappa c0 hadmissible hSW
      hsigma A hA
  refine ⟨C*(1+paperMass),mul_pos hC (by linarith [paperMass_nonneg]),x0,hx0,?_⟩
  intro i hx z k hk
  have hV : 0 ≤ (F i).V := zero_le_one.trans (hadmissible i).2.1
  have hY : 0 < keyY (F i) k := by
    dsimp only [keyY,keyD]
    have hq := (hadmissible i).2.2.1
    positivity
  have hlog := Real.log_pos (hx0.trans_le hx)
  unfold actualPrincipalRemainder
  calc
    _ ≤ (F i).V*paperMass*(C*(F i).U^2/
        (keyY (F i) k*(Real.log (F i).scale)^A)) :=
      mul_le_mul_of_nonneg_left (hbound i hx z k hk) (mul_nonneg hV paperMass_nonneg)
    _ ≤ _ := by
      have hh : paperMass ≤ 1+paperMass := by linarith
      have hc : 0 ≤ C*(F i).V*(F i).U^2/
          (keyY (F i) k*(Real.log (F i).scale)^A) := by positivity
      have h := mul_le_mul_of_nonneg_right hh hc
      convert h using 1 <;> ring

end
end ImbalancedChen.Part3.ActualPrincipalRoughMeanSourceOnly
