import ImbalancedChen.ActualThirdOriginalPositive256Log
/- API audit against the pinned mathlib revision e4c91783ca8e6a7c693ae624ade32fd22d4e43c1:
Real.log_div takes the two nonzero proofs, and Real.log_pow is unconditional.
Thus the logarithm identity below uses the available API without changing any
statement, target, range-reduction constant, or quantifier. SOURCEONLY only. -/

/-!
SOURCEONLY / HOLD_ELABORATION / OPEN30.
The original positive ln range reduction needed by ordinary compact leaves.
Every exact /2 is rational argument reduction, not interval division. At most
four such reductions suffice on [1,32]. The final interval multiply/add and
all original 256 terms and P160 floor/UP operations are retained.
-/
namespace ImbalancedChen.OriginalThirdPositiveLogSourceOnly
noncomputable section
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly

/-- Exactly unit_log(reduced)+k*unit_log(2). Python's k*IV invokes IV.__rmul__,
which is IV.__mul__: the actual interval order is unit_log(2) times V(k). -/
def originalLogBranch (reduced : ℝ) (k : ℕ) : IV :=
  add (unitLog reduced 256) (mul (unitLog 2 256) (ofReal (k : ℝ)))

/-- Unroll the producer's while x>2 at most four times. The exact rational
argument after k divisions is x/2^k. Equalities at2,4,8,16,32 keep the
producer's <=2 exit convention. No interval operation is reassociated. -/
def originalLn32 (x : ℝ) : IV :=
  if x≤2 then originalLogBranch x 0
  else if x/2≤2 then originalLogBranch (x/2) 1
  else if x/(2:ℝ)^2≤2 then originalLogBranch (x/(2:ℝ)^2) 2
  else if x/(2:ℝ)^3≤2 then originalLogBranch (x/(2:ℝ)^3) 3
  else originalLogBranch (x/(2:ℝ)^4) 4

private theorem originalLogBranch_scaled_sound (x : ℝ) (k : ℕ)
    (hlo : (2:ℝ)^k≤x) (hhi : x≤2*(2:ℝ)^k) :
    Encloses (originalLogBranch (x/(2:ℝ)^k) k) (Real.log x) := by
  have hp : (0:ℝ)<(2:ℝ)^k := pow_pos (by norm_num) _
  have hx : (0:ℝ)<x := hp.trans_le hlo
  have h1 : (1:ℝ)≤x/(2:ℝ)^k :=
    (le_div_iff₀ hp).2 (by simpa only [one_mul] using hlo)
  have h2 : x/(2:ℝ)^k≤2 := (div_le_iff₀ hp).2 hhi
  have h := add_sound (unitLog_sound h1 h2 256)
    (mul_sound (unitLog_sound (by norm_num : (1:ℝ)≤2) le_rfl 256)
      (ofReal_sound (k : ℝ)))
  have heq : Real.log (x/(2:ℝ)^k)+Real.log 2*(k:ℝ)=Real.log x := by
    rw [Real.log_div hx.ne' hp.ne', Real.log_pow]
    ring
  rw [heq] at h
  exact h

/-- Actual original positive ln enclosure on [1,32], with its original
range-reduction and final rounded product. No logarithm enclosure input. -/
theorem originalLn32_sound {x : ℝ} (h1 : 1≤x) (h32 : x≤32) :
    Encloses (originalLn32 x) (Real.log x) := by
  by_cases h0 : x≤2
  · rw [originalLn32, if_pos h0]
    simpa only [pow_zero, div_one] using
      originalLogBranch_scaled_sound x 0 (by simpa only [pow_zero] using h1)
        (by simpa only [pow_zero, mul_one] using h0)
  · by_cases h2 : x/2≤2
    · rw [originalLn32, if_neg h0, if_pos h2]
      have hlo : (2:ℝ)^1≤x := by
        simpa only [pow_one] using (lt_of_not_ge h0).le
      have hhi : x≤2*(2:ℝ)^1 := by
        simpa only [pow_one] using
          (div_le_iff₀ (by norm_num : (0:ℝ)<2)).1 h2
      simpa only [pow_one] using originalLogBranch_scaled_sound x 1 hlo hhi
    · by_cases h4 : x/(2:ℝ)^2≤2
      · rw [originalLn32, if_neg h0, if_neg h2, if_pos h4]
        have hlo : (2:ℝ)^2≤x := by
          have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).1 (lt_of_not_ge h2)
          norm_num at h ⊢
          exact h.le
        exact originalLogBranch_scaled_sound x 2 hlo
          ((div_le_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^2)).1 h4)
      · by_cases h8 : x/(2:ℝ)^3≤2
        · rw [originalLn32, if_neg h0, if_neg h2, if_neg h4, if_pos h8]
          have hlo : (2:ℝ)^3≤x := by
            have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^2)).1
              (lt_of_not_ge h4)
            norm_num at h ⊢
            exact h.le
          exact originalLogBranch_scaled_sound x 3 hlo
            ((div_le_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^3)).1 h8)
        · rw [originalLn32, if_neg h0, if_neg h2, if_neg h4, if_neg h8]
          have hlo : (2:ℝ)^4≤x := by
            have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^3)).1
              (lt_of_not_ge h8)
            norm_num at h ⊢
            exact h.le
          have hhi : x≤2*(2:ℝ)^4 := by norm_num; exact h32
          exact originalLogBranch_scaled_sound x 4 hlo hhi

end
end ImbalancedChen.OriginalThirdPositiveLogSourceOnly
