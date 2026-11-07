import ImbalancedChen.Part3ActualHighConductorFixedQuotient
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium appendix (14), actual crude variance and divisor-weighted
interpolation. The same alpha carrier, auxiliary r filter and reduced
residue classes are used throughout. Neither an unweighted BDH conclusion
nor the final weighted variance estimate is a premise of the uniform return.
-/

namespace ImbalancedChen.Part3.ActualCrudeWeightedVarianceSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance SharedFirstFactorCharacterDictionary
open ActualFilteredPrincipalCharacterVarianceSourceOnly
open ActualFilteredPrimitiveSWSourceOnly
open ActualLowConductorQuotientSumSourceOnly
open ActualHighConductorFixedQuotientSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem complex_square (z : ℂ) : (‖z‖^2 : ℂ) = z*star z := by
  rw [← Complex.ofReal_pow,← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj z).symm

/-- Centering can only decrease the actual reduced-class diagonal energy.
The positive principal term is removed exactly before any upper bound. -/
theorem filteredVariance_le_compatibleMass_norm (d : MediumAtom) (r : ℕ)
    {ell : ℕ} (hell : 0 < ell) :
    filteredVariance d ell r ≤
      ‖compatibleMass d.alphaCarrier (filteredAlpha d r) ell ell‖ := by
  have hvar : covariance d.alphaCarrier (filteredAlpha d r) ell ell =
      (filteredVariance d ell r : ℂ) := by
    unfold covariance
    simp only [Nat.gcd_self]
    calc
      _ = ∑ b ∈ reducedResidues ell,
          filteredError d ell r b * star (filteredError d ell r b) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [← filteredAP_eq_residueMass d hb,
          ← filteredMass_eq_coprimeMass d ell r]
        rfl
      _ = _ := by
        unfold filteredVariance
        push_cast
        apply Finset.sum_congr rfl
        intro b hb
        exact (complex_square _).symm
  let B := coprimeMass d.alphaCarrier (filteredAlpha d r) ell
  have hprincipal : B*star B/(ell.totient : ℂ) =
      (‖B‖^2/(ell.totient : ℝ) : ℂ) := by
    rw [← complex_square]
    norm_cast
  have h := covariance_identity d.alphaCarrier (filteredAlpha d r)
    (q := ell) (r := ell) hell
  rw [Nat.gcd_self,hvar] at h
  change compatibleMass d.alphaCarrier (filteredAlpha d r) ell ell -
    B*star B/(ell.totient : ℂ) = (filteredVariance d ell r : ℂ) at h
  rw [hprincipal] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  have hpos : 0 ≤ ‖B‖^2/(ell.totient : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  linarith [Complex.re_le_norm (compatibleMass d.alphaCarrier (filteredAlpha d r) ell ell)]

/-- One point per quotient block gives the actual progression occupancy.
This narrow finite argument is extracted from the existing private
SharedFirstFactorLargeResidualZero.progression_card_le. -/
theorem progression_card_le (S : Finset ℕ) (N ell b : ℕ)
    (hS : S ⊆ Finset.Ioc 0 N) :
    ((S.filter (fun n => Nat.ModEq ell n b)).card : ℝ) ≤
      (N : ℝ)/(ell : ℝ)+1 := by
  have hc : (S.filter (fun n => Nat.ModEq ell n b)).card ≤ N/ell+1 := by
    calc
      _ ≤ (Finset.range (N/ell+1)).card := by
        apply Finset.card_le_card_of_injOn (fun n : ℕ => n/ell)
        · intro n hn
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le
            (Nat.div_le_div_right (Finset.mem_Ioc.mp (hS (Finset.mem_filter.mp hn).1)).2))
        · intro n hn m hm heq
          apply Nat.ext_div_modEq heq
          exact (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
      _ = _ := Finset.card_range _
  calc
    _ ≤ ((N/ell : ℕ) : ℝ)+1 := by exact_mod_cast hc
    _ ≤ _ := add_le_add Nat.cast_div_le le_rfl

/-- Actual compatible-pair count of the filtered coefficient, bounded
before the mean is subtracted. The auxiliary mask costs no multiplicity. -/
theorem compatibleMass_norm_le_prefix {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (r ell : ℕ) :
    ‖compatibleMass d.alphaCarrier (filteredAlpha d r) ell ell‖ ≤
      (Nat.floor (2*d.U) : ℝ)*
        ((Nat.floor (2*d.U) : ℝ)/(ell : ℝ)+1) := by
  let N := Nat.floor (2*d.U)
  have hsub : d.alphaCarrier ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp (alpha_subset_prefix hU hn)
    exact Finset.mem_Ioc.mpr ⟨hn1,hnN⟩
  have hcard : (d.alphaCarrier.card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp)
  have hfiltered (n : ℕ) (hn : n ∈ d.alphaCarrier) : ‖filteredAlpha d r n‖ ≤ 1 := by
    by_cases hg : n.Coprime r
    · simpa only [filteredAlpha,if_pos hg] using halpha n hn
    · simp only [filteredAlpha,if_neg hg,norm_zero,zero_le_one]
  unfold compatibleMass
  simp only [ComplexCRT.Compatible,Nat.gcd_self]
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, ∑ m ∈ d.alphaCarrier,
        if Nat.ModEq ell n m then (1 : ℝ) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      by_cases h : n.Coprime ell ∧ m.Coprime ell ∧ Nat.ModEq ell n m
      · simp only [if_pos h,if_pos h.2.2,norm_mul,norm_star]
        simpa only [one_mul] using mul_le_mul (hfiltered n hn) (hfiltered m hm)
          (norm_nonneg _) zero_le_one
      · simp only [if_neg h,norm_zero]
        split_ifs <;> norm_num
    _ = ∑ n ∈ d.alphaCarrier,
        ((d.alphaCarrier.filter (fun m => Nat.ModEq ell m n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Nat.ModEq.comm (a := n),← Finset.sum_filter]
      simp
    _ ≤ ∑ _n ∈ d.alphaCarrier, ((N : ℝ)/(ell : ℝ)+1) :=
      Finset.sum_le_sum (fun n _ => progression_card_le _ N ell n hsub)
    _ = (d.alphaCarrier.card : ℝ)*((N : ℝ)/(ell : ℝ)+1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- The original crude variance bound: no divisor weight and no SW premise.
It is valid uniformly in the actual auxiliary r filter. -/
theorem actual_crude_variance_le {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (r : ℕ) {ell : ℕ} (hell : 0 < ell) (hellN : ell ≤ Nat.floor (2*d.U)) :
    filteredVariance d ell r ≤ 2*(Nat.floor (2*d.U) : ℝ)^2/(ell : ℝ) := by
  let N : ℝ := Nat.floor (2*d.U)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have he : (0 : ℝ) < ell := by exact_mod_cast hell
  have heN : (ell : ℝ) ≤ N := by exact_mod_cast hellN
  have hone : 1 ≤ N/(ell : ℝ) := (le_div_iff₀ he).mpr (by simpa using heN)
  refine (filteredVariance_le_compatibleMass_norm d r hell).trans
    ((compatibleMass_norm_le_prefix hU halpha r ell).trans ?_)
  change N*(N/(ell : ℝ)+1) ≤ 2*N^2/(ell : ℝ)
  calc
    _ ≤ N*(2*(N/(ell : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith : N/(ell : ℝ)+1 ≤ 2*(N/(ell : ℝ))) hN
    _ = _ := by ring

/-- Native fixed-order harmonic divisor moment. The order is selected before Q. -/
theorem sum_tau_pow_div_le (Q s : ℕ) (hQ : 1 ≤ Q) :
    (∑ ell ∈ Finset.Icc 1 Q, tau ell ^ s/(ell : ℝ)) ≤
      (1+Real.log (Q : ℝ)) ^ (2^s) := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hI : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
    ext ell
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  calc
    _ ≤ ∑ ell ∈ Finset.Icc 1 Q, (fouvryTau (2^s) ell : ℝ)/(ell : ℝ) := by
      apply Finset.sum_le_sum
      intro ell hell
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have he0 : ell ≠ 0 := by have := (Finset.mem_Icc.mp hell).1; omega
      have hp := fouvryTau_pow_le 2 s he0
      rw [fouvryTau_two] at hp
      exact_mod_cast hp
    _ ≤ _ := by
      rw [hI]
      simpa only [Nat.floor_natCast] using sum_fouvryTau_div_le_real (2^s) hQR

def weightedVariance (d : MediumAtom) (Q r w : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 Q, tau ell ^ w * filteredVariance d ell r

theorem weightedVariance_nonneg (d : MediumAtom) (Q r w : ℕ) :
    0 ≤ weightedVariance d Q r w :=
  Finset.sum_nonneg (fun ell _ => mul_nonneg (pow_nonneg (tau_nonneg ell) _)
    (filteredVariance_nonneg d ell r))

/-- The second factor in weighted Cauchy is paid from the actual crude
variance, not postulated as a divisor-weighted distribution estimate. -/
theorem weighted_variance_crude_moment {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (Q r w : ℕ) (hQ : 1 ≤ Q) (hQN : Q ≤ Nat.floor (2*d.U)) :
    (∑ ell ∈ Finset.Icc 1 Q, tau ell ^ (2*w)*filteredVariance d ell r) ≤
      2*(Nat.floor (2*d.U) : ℝ)^2 * (1+Real.log (Q : ℝ))^(2^(2*w)) := by
  calc
    _ ≤ ∑ ell ∈ Finset.Icc 1 Q,
        tau ell ^ (2*w)*(2*(Nat.floor (2*d.U) : ℝ)^2/(ell : ℝ)) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact mul_le_mul_of_nonneg_left
        (actual_crude_variance_le hU halpha r (Finset.mem_Icc.mp hell).1
          ((Finset.mem_Icc.mp hell).2.trans hQN)) (pow_nonneg (tau_nonneg ell) _)
    _ = 2*(Nat.floor (2*d.U) : ℝ)^2 *
        (∑ ell ∈ Finset.Icc 1 Q, tau ell ^ (2*w)/(ell : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_tau_pow_div_le Q (2*w) hQ) (by positivity)

/-- Exact low/high interpolation on the original filtered variance. -/
theorem actual_weighted_variance_interpolation {d : MediumAtom}
    (hU : 1 ≤ d.U) (halpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (Q R r w : ℕ) (hQ : 1 ≤ Q) (hQN : Q ≤ Nat.floor (2*d.U)) :
    weightedVariance d Q r w ^ 2 ≤
      (lowEnergy d Q R r + highEnergy d Q R r) *
        (2*(Nat.floor (2*d.U) : ℝ)^2 * (1+Real.log (Q : ℝ))^(2^(2*w))) := by
  have hc := weighted_variance_cauchy d r (Finset.Icc 1 Q) (fun ell => tau ell^w)
  have hpower (ell : ℕ) : (tau ell^w)^2 = tau ell^(2*w) := by
    rw [← pow_mul,Nat.mul_comm]
  simp_rw [hpower] at hc
  rw [low_add_high_eq_actual_variance]
  refine hc.trans ?_
  exact mul_le_mul_of_nonneg_left (weighted_variance_crude_moment hU halpha Q r w hQ hQN)
    (Finset.sum_nonneg (fun _ _ => filteredVariance_nonneg _ _ _))

/-- The uniform finite weighted return follows from original SW plus the
actual native primitive high-conductor return. No whole variance target
is introduced as a hypothesis. Scalar scale-margin absorption remains
explicitly downstream of this finite theorem. -/
theorem uniformAuxiliarySW_weightedVariance_finite
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A L : ℝ, 0 < A → 0 ≤ L →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i, x0 ≤ (F i).scale → ∀ Q R r w : ℕ,
          1 ≤ Q → Q ≤ Nat.floor (2*(F i).U) → 0 < R → 1 ≤ r →
          (R : ℝ) ≤ (Real.log (F i).scale)^L →
          weightedVariance (F i) Q r w ^ 2 ≤
            ((C*(F i).U/(Real.log (F i).scale)^A)^2 * tau r^(2*C0) *
                (R : ℝ) * (1+Real.log (Q : ℝ))^(2*(2^(2*C0))) +
              (2*chen1973Lemma6Eq19SharpConstant) *
                (Nat.floor (2*(F i).U) : ℝ) *
                ((Q : ℝ)+(Nat.floor (2*(F i).U) : ℝ)/(R : ℝ)) *
                ((Nat.log2 Q+1 : ℕ) : ℝ) * (1+Real.log (Q : ℝ))^2) *
              (2*(Nat.floor (2*(F i).U) : ℝ)^2 *
                (1+Real.log (Q : ℝ))^(2^(2*w))) := by
  intro A L hA hL
  obtain ⟨C,hC,x0,hx0,hlow⟩ :=
    uniformAuxiliarySW_lowEnergy F B C0 sigma kappa c0 hadmissible hSW A L hA hL
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx Q R r w hQ hQN hR hr hRlog
  obtain ⟨hU,_,_,_,_,_,_,_,_,_,_,_,halpha,_⟩ := hadmissible i
  refine (actual_weighted_variance_interpolation hU halpha Q R r w hQ hQN).trans ?_
  exact mul_le_mul_of_nonneg_right
    (add_le_add (hlow i hx Q R r hQ hr hRlog)
      (actual_highEnergy_le_native_sieve hU halpha Q R r hQ hR)) (by positivity)

end
end ImbalancedChen.Part3.ActualCrudeWeightedVarianceSourceOnly
