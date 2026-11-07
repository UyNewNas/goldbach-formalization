import ImbalancedChen.Part3MellinPrimeAuxiliarySW
import ImbalancedChen.P2GammaSmallConductorArithmetic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual prime transforms on arbitrary real (u,v] inside [M,2M]. The error
is measured in M even if v-u is arbitrarily small. All constants precede
M,u,v,t,k,r and the character. No UniformAuxiliarySW premise occurs.
-/

namespace ImbalancedChen.P2GammaPrimeCharacterSW
noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open Part3 Part3.MellinPrimeIntervalSW20261026b
open Part3.PrimeMellinProfileVariation20261026b
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open AnalyticNumberTheory.LargeSieve

/-- The independent quotient-unit gate is kept literally. -/
def rowTransform (S : Finset ℕ) (a : ℕ → ℂ) (k r : ℕ)
    (psi : DirichletCharacter ℂ r) : ℂ :=
  ∑ n ∈ S, (if n.Coprime k then a n else 0)*psi (n : ZMod r)

def rowMass (S : Finset ℕ) (a : ℕ → ℂ) : ℝ := ∑ n ∈ S, ‖a n‖

theorem rowMass_nonneg (S : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ rowMass S a := by
  exact Finset.sum_nonneg fun n _ => norm_nonneg _

theorem rowTransform_norm_le_mass (S : Finset ℕ) (a : ℕ → ℂ)
    (k r : ℕ) (psi : DirichletCharacter ℂ r) :
    ‖rowTransform S a k r psi‖ ≤ rowMass S a := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  by_cases hc : n.Coprime k
  · simp only [hc,if_true,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (psi.norm_le_one _)
  · simp only [hc,if_false,zero_mul,norm_zero]
    exact norm_nonneg _

/-- Exact cancellation against the SAME (k*r)-coprime prime mean. -/
theorem character_auxSW_expansion (S : Finset ℕ) (a : ℕ → ℂ)
    (k : ℕ) {r : ℕ} [NeZero r] (psi : DirichletCharacter ℂ r)
    (hpsi : psi ≠ 1) :
    rowTransform S a k r psi =
      ∑ b : ZMod r, psi b * auxiliarySWError S a k r b.val := by
  have hsum : (∑ b : ZMod r, psi b) = 0 :=
    MulChar.sum_eq_zero_of_ne_one hpsi
  let center : ℂ := (∑ n ∈ S, if n.Coprime (k*r) then a n else 0) /
    (r.totient : ℂ)
  have hcenter : (∑ b : ZMod r, psi b*center) = 0 := by
    rw [← Finset.sum_mul,hsum,zero_mul]
  symm
  change (∑ b : ZMod r, psi b *
    ((∑ n ∈ S, if Nat.ModEq r n b.val ∧ n.Coprime k then a n else 0)-center)) = _
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [hcenter,sub_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : n.Coprime k
  · rw [if_pos hc]
    calc
      _ = psi (n : ZMod r)*a n := by
        rw [Finset.sum_eq_single (n : ZMod r)]
        · have hm : Nat.ModEq r n (n : ZMod r).val := by
            apply (ZMod.natCast_eq_natCast_iff n (n : ZMod r).val r).mp
            exact (ZMod.natCast_zmod_val (n : ZMod r)).symm
          rw [if_pos ⟨hm,hc⟩]
        · intro b hb hne
          have hm : ¬Nat.ModEq r n b.val := by
            intro h
            have he := (ZMod.natCast_eq_natCast_iff n b.val r).mpr h
            rw [ZMod.natCast_zmod_val] at he
            exact hne he.symm
          rw [if_neg (fun h => hm h.1),mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = _ := mul_comm _ _
  · simp only [hc,and_false,if_false,mul_zero,zero_mul,Finset.sum_const_zero]

/-- There are phi(r) unit residues, rather than r usable residues. -/
theorem sum_unit_indicator_eq_phi (r : ℕ) [NeZero r] :
    (∑ b : ZMod r, if IsUnit b then (1 : ℝ) else 0) = (r.totient : ℝ) := by
  calc
    _ = ∑ b : ZMod r, (1 : DirichletCharacter ℝ r) b := by
      apply Finset.sum_congr rfl
      intro b hb
      rfl
    _ = (Fintype.card (ZMod r)ˣ : ℝ) := MulChar.sum_one_eq_card_units
    _ = _ := by rw [ZMod.card_units_eq_totient]

/-- Only a finite algebraic lemma: the final prime theorem below supplies E. -/
theorem rowTransform_norm_le_phi_error (S : Finset ℕ) (a : ℕ → ℂ)
    (k : ℕ) {r : ℕ} [NeZero r] (psi : DirichletCharacter ℂ r)
    (hpsi : psi ≠ 1) {E : ℝ} (hE : 0 ≤ E)
    (herr : ∀ b : ℕ, b.Coprime r → ‖auxiliarySWError S a k r b‖ ≤ E) :
    ‖rowTransform S a k r psi‖ ≤ (r.totient : ℝ)*E := by
  rw [character_auxSW_expansion S a k psi hpsi]
  calc
    _ ≤ ∑ b : ZMod r, ‖psi b*auxiliarySWError S a k r b.val‖ := norm_sum_le _ _
    _ ≤ ∑ b : ZMod r, (if IsUnit b then (1 : ℝ) else 0)*E := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hu : IsUnit b
      · have hc : b.val.Coprime r := by
          apply (ZMod.isUnit_iff_coprime b.val r).mp
          simpa only [ZMod.natCast_zmod_val] using hu
        rw [if_pos hu,norm_mul,one_mul]
        exact mul_le_mul (psi.norm_le_one b) (herr b.val hc) (norm_nonneg _) zero_le_one
      · rw [if_neg hu,psi.map_nonunit hu,zero_mul,norm_zero,zero_mul]
    _ = _ := by rw [← Finset.sum_mul,sum_unit_indicator_eq_phi]

/-- Genuine prime SW is used here; no prime-distribution statement is an input.
The divisor exponent is exactly one for arbitrary positive k. -/
theorem mellin_prime_character_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M u v : ℝ,
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M → ∀ t : ℝ,
      ∀ k r : ℕ, 0 < k → 0 < r → ∀ psi : DirichletCharacter ℂ r,
      psi ≠ 1 →
      ‖rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi‖ ≤
        (r.totient : ℝ) * (C*(1+|t|)*M*(k.divisors.card : ℝ)/Real.log (2*M)^D) := by
  obtain ⟨C,hC,hSW⟩ := mellin_prime_interval_SW Phi hPhi D
  refine ⟨C,hC,?_⟩
  intro M u v hM hlo huv hhi t k r hk hr psi hpsi
  let : NeZero r := ⟨hr.ne'⟩
  have hlog : 0 < Real.log (2*M) := Real.log_pos (by linarith)
  apply rowTransform_norm_le_phi_error _ _ k psi hpsi (by positivity)
  intro b hb
  simpa only [fouvryTau_two] using hSW M u v hM hlo huv hhi t k r b hk hr hb

/-- A single complete-scale constant precedes every subinterval, Mellin mode,
auxiliary quotient and nonprincipal character. The r log-range is optional:
the already available genuine prime supplier is stronger than needed here. -/
theorem mellin_prime_character_completeScale
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {eta J A : ℝ} (heta : 0 < eta) (hJ : 0 ≤ J) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ t : ℝ, |t| ≤ Real.log x^J →
      ∀ k r : ℕ, 0 < k → 0 < r → ∀ psi : DirichletCharacter ℂ r,
      psi ≠ 1 →
      ‖rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi‖ ≤
        (r.totient : ℝ) * (C*M*(k.divisors.card : ℝ)/Real.log x^A) := by
  let D : ℕ := Nat.ceil (A+J)
  obtain ⟨C,hC,hraw⟩ := mellin_prime_character_SW Phi hPhi D
  refine ⟨2*C/eta^D,div_pos (by positivity) (pow_pos heta D),Real.exp 1,
    Real.one_lt_exp_iff.mpr (by norm_num),?_⟩
  intro x M u v hx hpower hM hlo huv hhi t ht k r hk hr psi hpsi
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hM0 : 0 < M := by linarith
  have hL1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hL : 0 < Real.log x := zero_lt_one.trans_le hL1
  have hlogM : 0 < Real.log (2*M) := Real.log_pos (by linarith)
  have hcomp : eta*Real.log x ≤ Real.log (2*M) := by
    calc
      _ = Real.log (x^eta) := (Real.log_rpow hx0 eta).symm
      _ ≤ Real.log M := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hpower
      _ ≤ _ := Real.log_le_log hM0 (by linarith)
  have hfreq : 1+|t| ≤ 2*Real.log x^J := by
    have hJ1 := Real.one_le_rpow hL1 hJ
    linarith
  have hceil : Real.log x^(A+J) ≤ Real.log x^D := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hL1 (Nat.le_ceil (A+J))
  have hden : eta^D*Real.log x^(A+J) ≤ Real.log (2*M)^D := by
    calc
      _ ≤ eta^D*Real.log x^D := mul_le_mul_of_nonneg_left hceil (pow_nonneg heta.le D)
      _ = (eta*Real.log x)^D := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg heta.le hL.le) hcomp D
  apply (hraw M u v hM hlo huv hhi t k r hk hr psi hpsi).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ C*(2*Real.log x^J)*M*(k.divisors.card : ℝ)/Real.log (2*M)^D := by
      gcongr
    _ ≤ C*(2*Real.log x^J)*M*(k.divisors.card : ℝ)/(eta^D*Real.log x^(A+J)) :=
      div_le_div_of_nonneg_left (by positivity)
        (mul_pos (pow_pos heta D) (Real.rpow_pos_of_pos hL _)) hden
    _ = _ := by
      rw [Real.rpow_add hL]
      field_simp [(pow_pos heta D).ne', (Real.rpow_pos_of_pos hL A).ne',
        (Real.rpow_pos_of_pos hL J).ne']
      <;> ring

end
end ImbalancedChen.P2GammaPrimeCharacterSW
