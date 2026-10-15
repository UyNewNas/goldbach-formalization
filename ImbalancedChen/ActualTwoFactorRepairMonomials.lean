import ImbalancedChen.ActualSelectedSubproductParameters

/-!
# Three monomial bounds for the actual full-vector repair

This is the capacity-below-one branch of the manuscript's two-factor
repair at spectral exponent 7/32.  The original full D-well vector is
rerun through the actual prefer-left allocation with capacities A and D/A.
The formerly selected b₀ is used only to prove D/A < b₀ ≤ x^u.  It is not
retained as the final right factor.  The final third factor is one.

All three numerical constraints are proved for the actual natural factors.
The proof expands logarithms of positive monomials and pays their exponent
budgets from the original two upper bounds for u.  No monomial constraint
or action permission is an input.  Fixed box partitions, small-factor
reattachment, distribution estimates and arithmetic means remain separate.
-/

namespace ImbalancedChen

noncomputable section

private theorem twoFactorRepair_monomials {x δ θ α A B a b : ℝ}
    (hx : 1 < x) (hδ : δ ≤ 1 / 12) (hθ : θ ≤ 5 / 8)
    (hApos : 0 < A) (hBpos : 0 < B) (hapos : 0 < a) (hbpos : 0 < b)
    (hAB : A * B = x ^ (θ - 2 * δ))
    (hAupper : A ≤ x ^ (1 / 3 - δ / 2))
    (hBupper : B ≤ x ^ actualSelectedSubproductUpper α θ)
    (ha : a ≤ A) (hb : b ≤ B) :
    A ^ 2 * b ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * α / 32) * A * a * b ^ 5 ≤ x ^ (2 - 4 * δ) ∧
      (A / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 ≤ x ^ (2 - 39 * δ / 8) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hlogAB : Real.log A + Real.log B = (θ - 2 * δ) * Real.log x := by
    have h := congrArg Real.log hAB
    rw [Real.log_mul hApos.ne' hBpos.ne', Real.log_rpow hxpos] at h
    exact h
  have hlogA := (Real.le_rpow_iff_log_le hApos hxpos).mp hAupper
  have hlogB := (Real.le_rpow_iff_log_le hBpos hxpos).mp hBupper
  have hlogB₁ : Real.log B ≤ ((32 - 39 * θ) / 34) * Real.log x :=
    hlogB.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hlogB₂ : Real.log B ≤ ((2 - 2 * θ - 7 * α / 32) / 3) * Real.log x :=
    hlogB.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have hloga : Real.log a ≤ Real.log A := (Real.log_le_log_iff hapos hApos).mpr ha
  have hlogb : Real.log b ≤ Real.log B := (Real.log_le_log_iff hbpos hBpos).mpr hb
  have hθL := mul_le_mul_of_nonneg_right hθ hL.le
  have hδL := mul_le_mul_of_nonneg_right hδ hL.le
  refine ⟨?_, ?_, ?_⟩
  · apply Real.le_rpow_of_log_le hxpos
    rw [Real.log_mul (pow_ne_zero 2 hApos.ne') hbpos.ne', Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hxpos
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hapos.ne',
      Real.log_mul (by positivity) hApos.ne', Real.log_rpow hxpos, Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hxpos
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hapos.ne',
      Real.log_mul (by positivity) hApos.ne',
      Real.log_rpow (div_pos hApos hbpos),
      Real.log_div hApos.ne' hbpos.ne', Real.log_pow]
    nlinarith

/-- The complete original vector, rather than the selected remainder, is
allocated in the C<1 case.  The returned factors have all three original
constraints, with the manuscript's stronger second and third slack. -/
theorem actualDwell_full_vector_repair_monomials {x δ θ α A : ℝ}
    (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ < 1 / 100000)
    (hθlo : 1 / 2 ≤ θ) (hθhi : θ ≤ 5 / 8)
    (hAlower : x ^ δ ≤ A) (hAupper : A ≤ x ^ (1 / 3 - δ / 2))
    (input : List ℕ) (hpositive : ∀ p ∈ input, 0 < p)
    (hfull : actualDwellSupport (x ^ (θ - 2 * δ)) input)
    (b₀ : ℕ) (hb₀ : 0 < b₀)
    (hb₀upper : (b₀ : ℝ) ≤ x ^ actualSelectedSubproductUpper α θ)
    (hsmall : x ^ (θ - 2 * δ) / (A * b₀) < 1) :
    let ab := actualTwoCapacityFactors A input
    ab.1 * ab.2 = input.prod ∧ (ab.1 : ℝ) ≤ A ∧
      (ab.2 : ℝ) ≤ x ^ (θ - 2 * δ) / A ∧
      A ^ 2 * (ab.2 : ℝ) ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * α / 32) * A * (ab.1 : ℝ) * (ab.2 : ℝ) ^ 5 ≤ x ^ (2 - 4 * δ) ∧
      (A / (ab.2 : ℝ)) ^ (7 / 16 : ℝ) * A * (ab.1 : ℝ) * (ab.2 : ℝ) ^ 5 ≤
        x ^ (2 - 39 * δ / 8) := by
  have hone : (1 : ℝ) ≤ x ^ δ := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hx.le hδ0.le)
  have hA : 1 ≤ A := hone.trans hAlower
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAleD : A ≤ x ^ (θ - 2 * δ) :=
    hAupper.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have hB : 1 ≤ x ^ (θ - 2 * δ) / A :=
    (le_div_iff₀ hApos).mpr (by simpa only [one_mul] using hAleD)
  obtain ⟨hBlt, hprod, ha, hb⟩ := actualDwell_full_vector_repair hA hB input hfull b₀ hb₀ hsmall
  have hprodpos : 0 < (actualTwoCapacityFactors A input).1 *
      (actualTwoCapacityFactors A input).2 := by
    rw [hprod]
    exact List.prod_pos hpositive
  have hapos : (0 : ℝ) < (actualTwoCapacityFactors A input).1 := by
    exact_mod_cast Nat.pos_of_mul_pos_right hprodpos
  have hbpos : (0 : ℝ) < (actualTwoCapacityFactors A input).2 := by
    exact_mod_cast Nat.pos_of_mul_pos_left hprodpos
  have hAB : A * (x ^ (θ - 2 * δ) / A) = x ^ (θ - 2 * δ) := by
    simpa only [mul_comm] using (div_mul_cancel₀ (x ^ (θ - 2 * δ)) hApos.ne')
  have hmonomials := twoFactorRepair_monomials hx (by linarith : δ ≤ 1 / 12)
    hθhi hApos (zero_lt_one.trans_le hB) hapos hbpos hAB hAupper
    (hBlt.le.trans hb₀upper) ha hb
  exact ⟨hprod, ha, hb, hmonomials⟩

/-- The stronger repaired bounds imply exactly the three target exponents
with c'=1.  The final b' is the rerun right factor and may differ from b₀. -/
theorem actualDwell_full_vector_repair_targets {x δ θ α A : ℝ}
    (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ < 1 / 100000)
    (hθlo : 1 / 2 ≤ θ) (hθhi : θ ≤ 5 / 8)
    (hAlower : x ^ δ ≤ A) (hAupper : A ≤ x ^ (1 / 3 - δ / 2))
    (input : List ℕ) (hpositive : ∀ p ∈ input, 0 < p)
    (hfull : actualDwellSupport (x ^ (θ - 2 * δ)) input)
    (b₀ : ℕ) (hb₀ : 0 < b₀)
    (hb₀upper : (b₀ : ℝ) ≤ x ^ actualSelectedSubproductUpper α θ)
    (hsmall : x ^ (θ - 2 * δ) / (A * b₀) < 1) :
    let ab := actualTwoCapacityFactors A input
    ab.1 * ab.2 = input.prod ∧ (ab.1 : ℝ) ≤ A ∧
      A ^ 2 * (ab.2 : ℝ) ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * α / 32) * A * (ab.1 : ℝ) * (ab.2 : ℝ) ^ 5 ≤ x ^ (2 - 3 * δ) ∧
      (A / (ab.2 : ℝ)) ^ (7 / 16 : ℝ) * A * (ab.1 : ℝ) * (ab.2 : ℝ) ^ 5 ≤
        x ^ (2 - 2 * δ) := by
  obtain ⟨hprod, ha, _, hfirst, hsecond, hthird⟩ :=
    actualDwell_full_vector_repair_monomials hx hδ0 hδ hθlo hθhi hAlower hAupper
      input hpositive hfull b₀ hb₀ hb₀upper hsmall
  exact ⟨hprod, ha, hfirst,
    hsecond.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
    hthird.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))⟩

/-- The same actual pair decision pays its below-one branch.  Original
policy support, the perturbed critical upper bound and the repair capacities
are derived; the final factors rerun every original prime slot. -/
theorem actualExtendedThirdSelectedPair_smallCapacity_targets {e κ δ A : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hκ : κ ≤ e / 4) (hδ0 : 0 < δ) (hδ : δ < 1 / 100000) (hδfine : δ ≤ e / 32)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (x : ℝ) (hx : 1 < x) (p : Fin 3 → ℕ)
    (hs : actualSelectedPrimeCoordinates x p ∈ actualExtendedThirdPhysicalCell m j)
    (tail : List ℕ) (hpositive : ∀ q ∈ p 0 :: p 1 :: p 2 :: tail, 0 < q)
    (hsupport : actualDwellSupport (x ^ actualExtendedThirdPhysicalLevel e m j)
      (p 0 :: p 1 :: p 2 :: tail))
    (hAlower : x ^ δ ≤ A) (hAupper : A ≤ x ^ (1 / 3 - δ / 2))
    (hsmall : x ^ (actualExtendedThirdPairParameter e m j t yz - 2 * δ) /
      (A * (actualSelectedPairProduct yz p : ℝ)) < 1) :
    let ab := actualTwoCapacityFactors A (p 0 :: p 1 :: p 2 :: tail)
    ab.1 * ab.2 = (p 0 :: p 1 :: p 2 :: tail).prod ∧ (ab.1 : ℝ) ≤ A ∧
      A ^ 2 * (ab.2 : ℝ) ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * (1 + 3 * κ) / 32) * A * (ab.1 : ℝ) * (ab.2 : ℝ) ^ 5 ≤
        x ^ (2 - 3 * δ) ∧
      (A / (ab.2 : ℝ)) ^ (7 / 16 : ℝ) * A * (ab.1 : ℝ) * (ab.2 : ℝ) ^ 5 ≤
        x ^ (2 - 2 * δ) := by
  have hp : ∀ i, 0 < p i := by
    intro i
    fin_cases i <;> exact hpositive _ (by simp)
  obtain ⟨hsource, _, _, hbupper⟩ := actualExtendedThirdSelectedPair_arithmeticInputs
    he0 he hκ hδfine hmesh hfull ht yz hk x hx p hp hs tail hsupport
  obtain ⟨hθlo, hθhi, _, _⟩ := actualExtendedThirdSelectedPair_wholeCell
    he0 he hmesh hfull ht yz hk
  have hbpos : 0 < actualSelectedPairProduct yz p := by
    cases yz
    · exact Nat.mul_pos (hp 0) (hp 2)
    · exact Nat.mul_pos (hp 1) (hp 2)
  exact actualDwell_full_vector_repair_targets hx hδ0 hδ hθlo hθhi.le hAlower hAupper
    (p 0 :: p 1 :: p 2 :: tail) hpositive hsource
    (actualSelectedPairProduct yz p) hbpos hbupper hsmall

end

end ImbalancedChen
