import ImbalancedChen.Part3ProperPowerResidualPayment

/-!
# The square-root reserve in the actual proper-power box

The frozen 2026-11-06 manuscript, Appendix D, removes proper prime powers
before Heath--Brown expansion.  The original coordinate scales have a
positive lower bound and the padded complete-product box has volume O(N).

This file uses the actual labelled residual and its already proved box
budget.  The scalar square-root comparison and physical power identity
reuse the source-only arguments in
Part3OriginalProperPowerChartCount.oneBadSlotBox_absolute_mass_scale and
Part3AllKFamilyProperPowerSaving.physical_scale_power_identity, archived
at fa22a56829ee880404516a36d498ce27dcb32f92.  Their older List/Licence
carriers are not imported or substituted for the current source.

The resulting bound exposes the power 1-a/2. The divisor and modulus
masses remain visible; this is not the final arbitrary-logarithmic
distribution estimate.
-/

namespace ImbalancedChen.Part3.ProperPowerDyadicBudget

noncomputable section
open Classical
open scoped BigOperators

private theorem nat_sqrt_mul_sqrt_le {n : ℕ} {r : ℝ} (hr : r ≤ (n : ℝ)) :
    (Nat.sqrt n : ℝ) * Real.sqrt r ≤ (n : ℝ) := by
  have hNatSq : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast Nat.sqrt_le' n
  have hNatRoot : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le hNatSq
  calc
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul hNatRoot (Real.sqrt_le_sqrt hr)
        (Real.sqrt_nonneg r) (Real.sqrt_nonneg _)
    _ = (n : ℝ) := by
      nlinarith only [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The same complete labelled box has a square-root reserve in every
original coordinate scale. This includes the empty rank. -/
theorem properPowerBoxBudget_le_sqrt_lower
    (k : ℕ) (U : Fin k → ℕ) (Y : ℕ) {r : ℝ}
    (hr : 0 < r) (hLower : ∀ i, r ≤ (U i : ℝ))
    (hUpper : ∀ i, U i ≤ Y) :
    (properPowerBoxBudget k U : ℝ) ≤
      (k : ℝ) * (Nat.log 2 Y : ℝ) *
        (∏ i : Fin k, ((U i + 1 : ℕ) : ℝ)) / Real.sqrt r := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hr)).mpr
  calc
    _ = ∑ i : Fin k,
        (Nat.sqrt (U i) : ℝ) * (Nat.log 2 (U i) : ℝ) *
          (∏ j ∈ Finset.univ.erase i, ((U j + 1 : ℕ) : ℝ)) * Real.sqrt r := by
      simp only [properPowerBoxBudget, Nat.cast_sum, Nat.cast_mul, Nat.cast_prod,
        Finset.sum_mul]
    _ ≤ ∑ _i : Fin k,
        (Nat.log 2 Y : ℝ) * ∏ j : Fin k, ((U j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hroot :
          (Nat.sqrt (U i) : ℝ) * Real.sqrt r ≤ ((U i + 1 : ℕ) : ℝ) :=
        (nat_sqrt_mul_sqrt_le (hLower i)).trans (by exact_mod_cast Nat.le_succ (U i))
      have hlog : (Nat.log 2 (U i) : ℝ) ≤ (Nat.log 2 Y : ℝ) := by
        exact_mod_cast Nat.log_mono_right (b := 2) (hUpper i)
      have hO :
          0 ≤ ∏ j ∈ Finset.univ.erase i, ((U j + 1 : ℕ) : ℝ) :=
        Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
      have hprod :
          ((U i + 1 : ℕ) : ℝ) *
              (∏ j ∈ Finset.univ.erase i, ((U j + 1 : ℕ) : ℝ)) =
            ∏ j : Fin k, ((U j + 1 : ℕ) : ℝ) := by
        simpa only [mul_comm] using
          Finset.prod_erase_mul Finset.univ
            (fun j : Fin k => ((U j + 1 : ℕ) : ℝ)) (Finset.mem_univ i)
      calc
        _ = ((Nat.sqrt (U i) : ℝ) * Real.sqrt r) *
            (Nat.log 2 (U i) : ℝ) *
              (∏ j ∈ Finset.univ.erase i, ((U j + 1 : ℕ) : ℝ)) := by ring
        _ ≤ ((U i + 1 : ℕ) : ℝ) * (Nat.log 2 Y : ℝ) *
              (∏ j ∈ Finset.univ.erase i, ((U j + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hroot hlog (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hO
        _ = _ := by rw [mul_right_comm, hprod, mul_comm]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- The upper coordinate scale is computed from the finite box itself. -/
theorem properPowerBoxBudget_le_sqrt_lower_sup
    (k : ℕ) (U : Fin k → ℕ) {r : ℝ}
    (hr : 0 < r) (hLower : ∀ i, r ≤ (U i : ℝ)) :
    (properPowerBoxBudget k U : ℝ) ≤
      (k : ℝ) * (Nat.log 2 (Finset.univ.sup U) : ℝ) *
        (∏ i : Fin k, ((U i + 1 : ℕ) : ℝ)) / Real.sqrt r := by
  exact properPowerBoxBudget_le_sqrt_lower k U (Finset.univ.sup U) hr hLower
    (fun i => Finset.le_sup (f := U) (Finset.mem_univ i))

/-- Reused physical-scale identity: the reserve has the precise exponent
1-a/2, with the original lower-scale constant retained. -/
theorem physical_scale_power_identity {x c a : ℝ} (hx : 0 < x) (hc : 0 < c) :
    x / Real.sqrt (c * x ^ a) =
      (1 / Real.sqrt c) * x ^ (1 - a / 2) := by
  have hs : Real.sqrt (x ^ a) = x ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [Real.sqrt_mul hc.le, hs, Real.rpow_sub hx, Real.rpow_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The original coordinate lower scale and complete padded box volume
derive the fixed power reserve; no residual-bound hypothesis is used. -/
theorem properPowerBoxBudget_le_power_scale
    (k : ℕ) (U : Fin k → ℕ) (Y : ℕ) {x c C a : ℝ}
    (hx : 0 < x) (hc : 0 < c)
    (hLower : ∀ i, c * x ^ a ≤ (U i : ℝ))
    (hUpper : ∀ i, U i ≤ Y)
    (hVolume : (∏ i : Fin k, ((U i + 1 : ℕ) : ℝ)) ≤ C * x) :
    (properPowerBoxBudget k U : ℝ) ≤
      ((k : ℝ) * (Nat.log 2 Y : ℝ) * C / Real.sqrt c) * x ^ (1 - a / 2) := by
  calc
    _ ≤ (k : ℝ) * (Nat.log 2 Y : ℝ) *
        (∏ i : Fin k, ((U i + 1 : ℕ) : ℝ)) / Real.sqrt (c * x ^ a) :=
      properPowerBoxBudget_le_sqrt_lower k U Y
        (mul_pos hc (Real.rpow_pos_of_pos hx _)) hLower hUpper
    _ ≤ (k : ℝ) * (Nat.log 2 Y : ℝ) * (C * x) / Real.sqrt (c * x ^ a) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hVolume
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        (Real.sqrt_nonneg _)
    _ = ((k : ℝ) * (Nat.log 2 Y : ℝ) * C) *
        (x / Real.sqrt (c * x ^ a)) := by ring
    _ = _ := by
      rw [physical_scale_power_identity hx hc]
      ring

/-- The geometric power reserve pays the actual labelled residual after
the complete modulus sum, with its original rho and exact-product diagonal. -/
theorem labelledProperPowerResidual_signedError_norm_le_power_scale
    (k P N J D Y : ℕ) (B Q : Finset ℕ) (ρ : ℕ → ℂ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (U : Fin k → ℕ)
    {M Cρ x c C a : ℝ} (hM : 0 ≤ M) (hCρ : 0 ≤ Cρ)
    (hx : 0 < x) (hc : 0 < c)
    (hW : ∀ t, |W t| ≤ M)
    (hU : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 → ∀ i, (t i).val ≤ U i)
    (hLower : ∀ i, c * x ^ a ≤ (U i : ℝ))
    (hUpper : ∀ i, U i ≤ Y)
    (hVolume : (∏ i : Fin k, ((U i + 1 : ℕ) : ℝ)) ≤ C * x)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (hD : ∀ b ∈ B, b ≠ N → (Nat.dist b N).divisors.card ≤ D) :
    ‖finiteProductSignedError B Q N ρ (labelledProperPowerResidual k P W)‖ ≤
      (M * (((k : ℝ) * (Nat.log 2 Y : ℝ) * C / Real.sqrt c) * x ^ (1 - a / 2))) *
        (Cρ * (D : ℝ) ^ (J + 1) + SignedModulusPayment.meanMass Q ρ) +
      (M * (properPowerDiagonalBudget k N : ℝ)) * SignedModulusPayment.modulusMass Q ρ := by
  apply (labelledProperPowerResidual_signedError_norm_le
    k P N J D B Q ρ W U hM hCρ hW hU hρ hD).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left
      (properPowerBoxBudget_le_power_scale k U Y hx hc hLower hUpper hVolume) hM
  · exact add_nonneg (mul_nonneg hCρ (pow_nonneg (Nat.cast_nonneg _) _))
      (SignedModulusPayment.meanMass_nonneg Q ρ)

end
end ImbalancedChen.Part3.ProperPowerDyadicBudget
