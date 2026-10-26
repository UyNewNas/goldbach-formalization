import ImbalancedChen.P5ZU1011OriginalFifteenDeltaMonomials
import ImbalancedChen.P5ZU1011OriginalFifteenJointSmallBeta
import ImbalancedChen.Part3ActualWSmallThirdAttachment

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The same ORIGINAL15 natural factors accept an actual small integer only in
group3. The existing generic third_attachment_monomials algebra is reused,
not reproved. The rough reserves remain physical delta reserves; the
moving alpha is paid separately, never by shrinking to kappa-sized buffers.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedDeltaAttachment

noncomputable section
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenNearCapBoxProfiles (delta)
open U1011OriginalFifteenJointSelectedCompletion
open U1011OriginalFifteenJointSmallBeta (attachedFactors)
open ImbalancedChen.Part3.ActualWSameKeyMonomials (Monomials)
open ImbalancedChen.Part3.ActualWSmallThirdAttachment (third_attachment_monomials)

/-- A small factor e<N^ell, ell<=delta/8, attaches to the THIRD same
actual factor. All original A in [1,N^(1/3)] and kappa<=delta/64 remain
available, with positive delta margins in every original monomial. -/
theorem actual_beta_attached_delta_monomials {N d e enumeration : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ) (heta : 0 < eta)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (hb : coordinates N t ∈ B.region)
    (hd : U1011OriginalSixteenJointNearCapCompiler.rowCoefficient p B eta N d ≠ 0)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa w ell : ℝ} (hk0 : 0 ≤ kappa)
    (hk : kappa ≤ (delta p B eta : ℝ) / 64)
    (he : e ∈ actualSmallRosserSupport N enumeration w)
    (hesize : (e : ℝ) < (N : ℝ) ^ ell) (hell : ell ≤ (delta p B eta : ℝ) / 8) :
    let abc := attachedFactors p B eta N A t d e
    let delt := (delta p B eta : ℝ)
    abc.1 * abc.2.1 * abc.2.2 = e * (fullPrefix t * d) ∧
      0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧ (abc.1 : ℝ) ≤ A ∧
      A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 - 3 * delt / 2) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - delt) ∧
      (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
        (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
          (N : ℝ) ^ (2 - 117 * delt / 64) := by
  let abc := factors p B eta N A t d
  let delt : ℝ := (delta p B eta : ℝ)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hdelt : 0 < delt := by
    exact_mod_cast (U1011OriginalSixteenNearCapBoxProfiles.rational_parameters
      p B eta hv hw hc heta).2.2.1
  obtain ⟨hprod, haN, hbN, hcN, haA, hfirst, hsecond, hthird⟩ :=
    U1011OriginalFifteenDeltaMonomials.actual_fixed_factors_delta_monomials
      (kappa := (0 : ℝ)) hN ht p hp B eta heta hv hw hc hb hd A hA hAupper
      (by norm_num) (by linarith)
  have ha : (0 : ℝ) < abc.1 := by exact_mod_cast haN
  have hb' : (0 : ℝ) < abc.2.1 := by exact_mod_cast hbN
  have hc' : (0 : ℝ) < abc.2.2 := by exact_mod_cast hcN
  have heN := Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree N enumeration w he).ne_zero
  have hePos : (0 : ℝ) < e := by exact_mod_cast heN
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hmono : Monomials (N : ℝ) (3 * delt / 4) A (abc.1 : ℝ) (abc.2.1 : ℝ) (abc.2.2 : ℝ) := by
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ (N : ℝ) ^ (1 - 3 * delt) := hfirst
        _ = _ := by congr 1; ring
    · have hz : (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
          (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - 4 * delt) := by
        simpa using hsecond
      exact hz.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    · exact hthird.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
  have hattach := third_attachment_monomials hn hApos ha hb' hc' hePos hesize.le
    (show ell ≤ 3 * delt / 4 by change ell ≤ 3 * (delta p B eta : ℝ) / 4; linarith) hmono
  change abc.1 * abc.2.1 * (e * abc.2.2) = e * (fullPrefix t * d) ∧
    0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < e * abc.2.2 ∧ (abc.1 : ℝ) ≤ A ∧ _
  refine ⟨?_, haN, hbN, Nat.mul_pos heN hcN, haA, ?_, ?_, ?_⟩
  · calc
      _ = e * (abc.1 * abc.2.1 * abc.2.2) := by ring
      _ = _ := by rw [hprod]
  · simp only [Nat.cast_mul]
    exact hattach.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by nlinarith))
  · simp only [Nat.cast_mul]
    calc
      _ = (N : ℝ) ^ (21 * kappa / 32) *
          ((N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
            (abc.2.1 : ℝ) ^ 5 * ((e : ℝ) * (abc.2.2 : ℝ)) ^ 2) := by
        rw [show 7 * (1 + 3 * kappa) / 32 = 21 * kappa / 32 + (7 / 32 : ℝ) by ring,
          Real.rpow_add hn0]
        ring
      _ ≤ (N : ℝ) ^ (21 * kappa / 32) * (N : ℝ) ^ (2 - 4 * ((3 * delt / 4) / 2)) :=
        mul_le_mul_of_nonneg_left hattach.2.1 (Real.rpow_nonneg hn0.le _)
      _ = (N : ℝ) ^ (21 * kappa / 32 + (2 - 4 * ((3 * delt / 4) / 2))) :=
        (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by change kappa ≤ delt / 64 at hk; linarith)
  · simp only [Nat.cast_mul]
    exact hattach.2.2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by nlinarith))

end
end ImbalancedChen.P5Z.OriginalPresievedDeltaAttachment

