import ImbalancedChen.P2GammaVariablePrimeProfile
import ImbalancedChen.P2GammaPrimeSmallConductorSum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniform variable-amplitude, target-deleted prime rows. V and the profile
order J are fixed before all target/interval/Mellin/profile choices.
The two permitted geometric bounds are explicit norms, never a prime SW
or convolution estimate. The original Gamma smooth-source dictionary is
a separate source obligation and is not postulated here.
-/

namespace ImbalancedChen.P2GammaVariablePrimeSmallConductor
noncomputable section
open Classical Finset Set MeasureTheory Filter
open scoped BigOperators Topology
open P2GammaVariablePrimeProfile P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion
open P2GammaPrimeSmallConductorSum
open AnalyticNumberTheory.LargeSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All permitted varying amplitudes are selected after C and x0. Their
literal target-deleted prime coefficients have fixed C0=1 for arbitrary k. -/
theorem variable_target_prime_character_completeScale
    {eta J A V Ctarget : ℝ} (heta : 0 < eta) (hV : 0 ≤ V)
    (hCtarget : 0 ≤ Ctarget) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc u v, DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v ≤ V*Real.log x^J →
      (∀ y ∈ Icc u v, ‖f y‖ ≤ V*Real.log x^J) →
      ∀ target : ℕ, 0 < target → (target : ℝ) ≤ x^Ctarget →
      ∀ k r : ℕ, 0 < k → 0 < r → ∀ psi : DirichletCharacter ℂ r,
      psi ≠ 1 →
      ‖rowTransform (primeSWInterval u v)
        (targetDeleted target (profilePrimeCoefficient f)) k r psi‖ ≤
        (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A) := by
  obtain ⟨C,hC,x1,hx1,hraw⟩ := variable_profile_character_completeScale heta hV
    (A := A) (J := J)
  have hpay : ∀ᶠ x : ℝ in atTop, Real.log x^(A+J) ≤ x^eta := by
    have hb := (isLittleO_log_rpow_rpow_atTop (A+J) heta).bound (by norm_num : (0:ℝ)<1)
    filter_upwards [hb,eventually_ge_atTop (1 : ℝ)] with x hx hxge
    simpa only [Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hxge) (A+J)),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hxge) eta)] using hx
  obtain ⟨x2,hx2⟩ := eventually_atTop.mp hpay
  let K : ℝ := V*Ctarget/eta
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C+K,add_pos_of_pos_of_nonneg hC hK,max x1 x2,
    hx1.trans_le (le_max_left _ _),?_⟩
  intro x M u v hx hpower hM hlo huv hhi f hfd hfi hvar hsize target htarget hTarget k r hk hr psi hpsi
  have hxx1 : x1 ≤ x := (le_max_left _ _).trans hx
  have hxgt : 1 < x := hx1.trans_le hxx1
  have hL : 0 < Real.log x := Real.log_pos hxgt
  have hden : 0 < Real.log x^A := Real.rpow_pos_of_pos hL _
  have hrawBound := hraw x M u v hxx1 hpower hM hlo huv hhi f hfd hfi hvar k r hk hr psi hpsi
  have hcard := target_prime_card_completeScale heta hxgt hpower hlo huv hhi htarget hTarget
  have hcoeff (n : ℕ) (hn : n ∈ primeSWInterval u v) :
      ‖profilePrimeCoefficient f n‖ ≤ V*Real.log x^J := by
    have hnlo : u < (n : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ u)).mp
      (Finset.mem_Ioc.mp hn).1
    have hnhi : (n : ℝ) ≤ v :=
      (show (n : ℝ) ≤ (Nat.floor v : ℝ) by exact_mod_cast (Finset.mem_Ioc.mp hn).2).trans
        (Nat.floor_le (by linarith : 0 ≤ v))
    by_cases hp : n.Prime
    · simpa only [profilePrimeCoefficient,primeSWBeta,hp,if_true,Complex.ofReal_one,mul_one]
        using hsize n ⟨hnlo.le,hnhi⟩
    · simp only [profilePrimeCoefficient,primeSWBeta,hp,if_false,Complex.ofReal_zero,
        mul_zero,norm_zero]
      positivity
  have hdeletion := rowTransform_target_deletion_le (primeSWInterval u v)
    (profilePrimeCoefficient f) target k r psi (by positivity) hcoeff
    (fun n hn hp => by simp [profilePrimeCoefficient,primeSWBeta,hp])
  have hsmall :
      ‖rowTransform (primeSWInterval u v) (targetDeleted target (profilePrimeCoefficient f)) k r psi-
        rowTransform (primeSWInterval u v) (profilePrimeCoefficient f) k r psi‖ ≤ K*Real.log x^J := by
    apply hdeletion.trans
    have hh := mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ V*Real.log x^J)
    convert hh using 1 <;> dsimp only [K] <;> ring
  have htau : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr
      ⟨1,Nat.mem_divisors.mpr ⟨one_dvd k,hk.ne'⟩⟩
  have hphi : (1 : ℝ) ≤ (r.totient : ℝ) := by
    have hn : 1 ≤ r.totient := Nat.totient_pos.mpr hr
    exact_mod_cast hn
  have hlogPay : Real.log x^J ≤ M/Real.log x^A := by
    apply (le_div_iff₀ hden).mpr
    have hp := (hx2 x ((le_max_right _ _).trans hx)).trans hpower
    rwa [Real.rpow_add hL,mul_comm] at hp
  have hunit : Real.log x^J ≤
      (r.totient : ℝ)*(M*(k.divisors.card : ℝ)/Real.log x^A) := by
    have hM0 : 0 ≤ M := by linarith
    have hquot : M/Real.log x^A ≤ M*(k.divisors.card : ℝ)/Real.log x^A :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right hM0 htau) hden.le
    exact (hlogPay.trans hquot).trans (le_mul_of_one_le_left (by positivity) hphi)
  calc
    _ = ‖rowTransform (primeSWInterval u v) (profilePrimeCoefficient f) k r psi+
      (rowTransform (primeSWInterval u v) (targetDeleted target (profilePrimeCoefficient f)) k r psi-
        rowTransform (primeSWInterval u v) (profilePrimeCoefficient f) k r psi)‖ := by
      congr 1
      ring
    _ ≤ ‖rowTransform (primeSWInterval u v) (profilePrimeCoefficient f) k r psi‖+
      ‖rowTransform (primeSWInterval u v) (targetDeleted target (profilePrimeCoefficient f)) k r psi-
        rowTransform (primeSWInterval u v) (profilePrimeCoefficient f) k r psi‖ := norm_add_le _ _
    _ ≤ (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A)+K*Real.log x^J :=
      add_le_add hrawBound hsmall
    _ ≤ (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A)+
      K*((r.totient : ℝ)*(M*(k.divisors.card : ℝ)/Real.log x^A)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hunit hK) _
    _ = _ := by ring

/-- The full small-r/k sum for arbitrary permitted variable profiles.
Its complementary factor keeps its k gate and is charged by its actual
absolute coefficient mass. No complement-distribution premise is used. -/
theorem variable_profile_small_conductors
    {eta J A V Ctarget : ℝ} (heta : 0 < eta) (hV : 0 ≤ V)
    (hCtarget : 0 ≤ Ctarget) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc u v, DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v ≤ V*Real.log x^J →
      (∀ y ∈ Icc u v, ‖f y‖ ≤ V*Real.log x^J) →
      ∀ target : ℕ, 0 < target → (target : ℝ) ≤ x^Ctarget →
      ∀ R Q : ℕ, ∀ T : Finset ℕ, ∀ b : ℕ → ℂ,
      smallConductorContribution R Q (primeSWInterval u v) T
        (targetDeleted target (profilePrimeCoefficient f)) b ≤
        C*M*rowMass T b*(R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/Real.log x^A := by
  obtain ⟨C,hC,x0,hx0,hbound⟩ := variable_target_prime_character_completeScale heta hV hCtarget
    (A := A) (J := J)
  refine ⟨16*C,by positivity,x0,hx0,?_⟩
  intro x M u v hx hpower hM hlo huv hhi f hfd hfi hvar hsize target htarget hTarget R Q T b
  have hL : 0 < Real.log x := Real.log_pos (hx0.trans_le hx)
  have hE : 0 ≤ C*M/Real.log x^A := by positivity
  have hp := smallConductorContribution_le R Q (primeSWInterval u v) T
    (targetDeleted target (profilePrimeCoefficient f)) b hE (by
      intro k r hk hr psi
      have hh := hbound x M u v hx hpower hM hlo huv hhi f hfd hfi hvar hsize target htarget hTarget
        k r hk (by omega) psi.1 (primitiveCharacter_ne_one hr psi)
      convert hh using 1 <;> ring)
  convert hp using 1 <;> ring

/-- Pure scalar absorption; the profile/prime supplier is already derived. -/
theorem small_cutoff_log_cost_le {L B D A : ℝ} (hL1 : 1 ≤ L) (hD : 0 ≤ D)
    {R Q : ℕ} (hR : (R : ℝ) ≤ L^B)
    (hlogQ : Real.log (max 1 (Q : ℝ)) ≤ D*L) :
    (R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/L^(A+2*B+2) ≤
      (1+D)^2/L^A := by
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hQcost : (1+Real.log (max 1 (Q : ℝ)))^2 ≤ (1+D)^2*L^2 := by
    have hqnonneg : 0 ≤ 1+Real.log (max 1 (Q : ℝ)) := by
      have hl := Real.log_nonneg (le_max_left 1 (Q : ℝ))
      linarith
    have hbase : 1+Real.log (max 1 (Q : ℝ)) ≤ (1+D)*L := by nlinarith
    simpa only [mul_pow] using pow_le_pow_left₀ hqnonneg hbase 2
  have hRcost : (R : ℝ)^2 ≤ L^(2*B) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2
    have heq : (L^B)^2 = L^(2*B) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
      congr 1
      ring
    exact hs.trans_eq heq
  calc
    _ ≤ (L^(2*B)*((1+D)^2*L^2))/L^(A+2*B+2) :=
      div_le_div_of_nonneg_right (mul_le_mul hRcost hQcost (by positivity) (by positivity))
        (Real.rpow_nonneg hL.le _)
    _ = _ := by
      rw [show A+2*B+2 = A+(2*B+2) by ring,
        Real.rpow_add hL,Real.rpow_add hL,Real.rpow_natCast]
      field_simp [(Real.rpow_pos_of_pos hL A).ne',
        (Real.rpow_pos_of_pos hL (2*B)).ne',hL.ne']
      <;> ring

/-- The requested complete small-conductor payment for all admitted
variable profiles. The fixed geometry orders precede the stronger prime
accuracy; every varying profile/interval/target/mode/modulus follows C,x0. -/
theorem variable_profile_small_conductors_logSaving
    {eta J A V Ctarget B D : ℝ} (heta : 0 < eta) (hV : 0 ≤ V)
    (hCtarget : 0 ≤ Ctarget) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc u v, DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v ≤ V*Real.log x^J →
      (∀ y ∈ Icc u v, ‖f y‖ ≤ V*Real.log x^J) →
      ∀ target : ℕ, 0 < target → (target : ℝ) ≤ x^Ctarget →
      ∀ R Q : ℕ, (R : ℝ) ≤ Real.log x^B → (Q : ℝ) ≤ x^D →
      ∀ T : Finset ℕ, ∀ b : ℕ → ℂ,
      smallConductorContribution R Q (primeSWInterval u v) T
        (targetDeleted target (profilePrimeCoefficient f)) b ≤
        C*M*rowMass T b/Real.log x^A := by
  obtain ⟨C,hC,x1,hx1,hbound⟩ := variable_profile_small_conductors heta hV hCtarget
    (A := A+2*B+2) (J := J)
  refine ⟨C*(1+D)^2,mul_pos hC (sq_pos_of_pos (by linarith)),max x1 (Real.exp 1),
    hx1.trans_le (le_max_left _ _),?_⟩
  intro x M u v hx hpower hM hlo huv hhi f hfd hfi hvar hsize target htarget hTarget R Q hR hQ T b
  have hx1' : x1 ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hxgt : 1 < x := hx1.trans_le hx1'
  have hx0 : 0 < x := zero_lt_one.trans hxgt
  have hL1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hmax : max 1 (Q : ℝ) ≤ x^D := max_le (Real.one_le_rpow hxgt.le hD) hQ
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ D*Real.log x := by
    calc
      _ ≤ Real.log (x^D) := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
      _ = _ := Real.log_rpow hx0 D
  have hcost := small_cutoff_log_cost_le hL1 hD hR hlogQ (A := A)
  have hp := hbound x M u v hx1' hpower hM hlo huv hhi f hfd hfi hvar hsize target htarget hTarget R Q T b
  calc
    _ ≤ C*M*rowMass T b*(R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/
        Real.log x^(A+2*B+2) := hp
    _ = (C*M*rowMass T b)*((R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/
        Real.log x^(A+2*B+2)) := by ring
    _ ≤ (C*M*rowMass T b)*((1+D)^2/Real.log x^A) :=
      mul_le_mul_of_nonneg_left hcost (by have := rowMass_nonneg T b; positivity)
    _ = _ := by ring

end
end ImbalancedChen.P2GammaVariablePrimeSmallConductor
