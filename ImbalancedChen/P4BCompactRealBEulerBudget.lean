import ImbalancedChen.P4BPrimeEulerOperatorWords
import ImbalancedChen.P4BSmoothRealBAllOrderFamily

/-!
# Full mixed prime Euler budgets uniform over a compact real-b band

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
One constant is chosen after k and bHi and before all b in [0,bHi],
positive widths, targets, cutoffs, positive prime-variable points and words.
The full mixed bound is derived from scalar smooth-step derivatives and
the actual affine wall rows; no uniform derivative bound is assumed.
-/

namespace ImbalancedChen.P4B

noncomputable section
open scoped BigOperators

/-- Upgrade the actual band's wall-row application bound to operator norm. -/
theorem smoothPhysicalWallRow_norm_le_compact_realB
    {b bHi : ℝ} (hb : 0 ≤ b) (hbMax : b ≤ bHi)
    (N : ℕ) (hN : 2 ≤ N) (i : Fin 4) :
    ‖smoothPhysicalWallRow b N i‖ ≤ (2 + bHi) * (1 + Real.log (N : ℝ)) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  have hbHi : 0 ≤ bHi := hb.trans hbMax
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by linarith only [hbHi]) (add_nonneg zero_le_one hlog))
  intro h
  simpa only [Real.norm_eq_abs] using
    smoothPhysicalWallRow_apply_abs_le_of_b_le hb hbMax N hN i h

/-- Full mixed Frechet norm of the actual physical profile, with the
constant uniform over the entire real-b band before selecting b. -/
theorem exists_compact_realB_physical_iteratedFDeriv_budget
    (k : ℕ) {bHi : ℝ} (hbHi : 0 ≤ bHi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 ≤ b → b ≤ bHi →
      ∀ width : ℝ, 0 < width → ∀ N : ℕ, 2 ≤ N →
      ∀ T : ℝ, ∀ x : Fin 2 → ℝ,
        ‖iteratedFDeriv ℝ k (smoothPhysicalProfile b N T width) x‖ ≤
          (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k := by
  obtain ⟨B, hB, hscalar⟩ := exists_smoothGateUpperStep_finite_derivative_budget k
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcb : 0 ≤ 2 + bHi := by linarith only [hbHi]
  let C : ℝ := B ^ 4 * (4 * (2 + bHi)) ^ k
  refine ⟨C, mul_nonneg (pow_nonneg hB0 4)
    (pow_nonneg (mul_nonneg (by norm_num) hcb) k), ?_⟩
  intro b hb hbMax width hwidth N hN T x
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  let R : ℝ := ((2 + bHi) * (1 + Real.log (N : ℝ))) / width
  have hR : 0 ≤ R := div_nonneg
    (mul_nonneg hcb (add_nonneg zero_le_one hlog)) hwidth.le
  let f : Fin 4 → (Fin 2 → ℝ) → ℝ := fun i y =>
    smoothGateUpperStep width (smoothPhysicalWallOffset b N T i + smoothPhysicalWallRow b N i y)
  have hstep : ContDiff ℝ ∞ (smoothGateUpperStep width) := contDiff_smoothGateUpperStep width
  have hf (i : Fin 4) : ContDiff ℝ ∞ (f i) :=
    hstep.comp (contDiff_const.add (smoothPhysicalWallRow b N i).contDiff)
  have hfactor (i : Fin 4) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ B * R ^ j := by
    calc
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤
          |iteratedDeriv j (smoothGateUpperStep width)
            (smoothPhysicalWallOffset b N T i + smoothPhysicalWallRow b N i x)| *
              ‖smoothPhysicalWallRow b N i‖ ^ j :=
        norm_iteratedFDeriv_scalar_affine_le j (smoothGateUpperStep width) hstep
          (smoothPhysicalWallOffset b N T i) (smoothPhysicalWallRow b N i) x
      _ ≤ (B / width ^ j) * (((2 + bHi) * (1 + Real.log (N : ℝ))) ^ j) :=
        mul_le_mul (hscalar j hj width hwidth _)
          (pow_le_pow_left₀ (norm_nonneg _)
            (smoothPhysicalWallRow_norm_le_compact_realB hb hbMax N hN i) j)
          (pow_nonneg (norm_nonneg _) j) (div_nonneg hB0 (pow_nonneg hwidth.le j))
      _ = B * R ^ j := by dsimp only [R]; rw [div_pow]; ring
  have heq : smoothPhysicalProfile b N T width = fun y => ∏ i : Fin 4, f i y := by
    funext y
    unfold smoothPhysicalProfile
    apply Finset.prod_congr rfl
    intro i _hi
    exact congrArg (smoothGateUpperStep width)
      (smoothPhysicalProfileMargin_eq_offset_add_row b N T y i)
  rw [heq]
  have hfour := norm_iteratedFDeriv_four_gate_product_budget k f hf x R B hR hB0 hfactor
  have hscale : B ^ 4 * (4 * R) ^ k =
      (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k := by
    dsimp [C, R]
    simp only [mul_pow, div_pow]
    ring
  exact hfour.trans_eq hscale

/-- Full tensor bound on genuine multiplicative prime charts, uniform in
b and N. All mixed directions, rather than only diagonal ones, are controlled. -/
theorem exists_compact_realB_prime_mixed_chart_budget
    (k : ℕ) {bHi : ℝ} (hbHi : 0 ≤ bHi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 ≤ b → b ≤ bHi →
      ∀ width : ℝ, 0 < width → ∀ N : ℕ, 2 ≤ N →
      ∀ T : ℝ, ∀ p : Fin 2 → ℝ, p ∈ positivePrimeOrthant → ∀ z : Fin 2 → ℝ,
        ‖iteratedFDeriv ℝ k
          (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) z‖ ≤
          C / width ^ k := by
  obtain ⟨C, hC, hbudget⟩ := exists_compact_realB_physical_iteratedFDeriv_budget k hbHi
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hscale : 0 ≤ 1 + (Real.log 2)⁻¹ :=
    add_nonneg zero_le_one (inv_nonneg.mpr htwo.le)
  refine ⟨C * (1 + (Real.log 2)⁻¹) ^ k,
    mul_nonneg hC (pow_nonneg hscale k), ?_⟩
  intro b hb hbMax width hwidth N hN T p hp z
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hi : 0 ≤ (Real.log (N : ℝ))⁻¹ := inv_nonneg.mpr hlog.le
  have hnormalized : 0 ≤ (Real.log (N : ℝ))⁻¹ * (1 + Real.log (N : ℝ)) :=
    mul_nonneg hi (add_nonneg zero_le_one hlog.le)
  rw [iteratedFDeriv_smoothPrimeVariableProfile_primeEulerChart k b N T width hp z,
    norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hi]
  calc
    (Real.log (N : ℝ))⁻¹ ^ k *
        ‖iteratedFDeriv ℝ k (smoothPhysicalProfile b N T width)
          (primeVariableLogPoint N p + (Real.log (N : ℝ))⁻¹ • z)‖ ≤
        (Real.log (N : ℝ))⁻¹ ^ k *
          ((C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k) :=
      mul_le_mul_of_nonneg_left (hbudget b hb hbMax width hwidth N hN T _)
        (pow_nonneg hi k)
    _ = (C / width ^ k) *
        ((Real.log (N : ℝ))⁻¹ * (1 + Real.log (N : ℝ))) ^ k := by
      rw [mul_pow]
      ring
    _ ≤ (C / width ^ k) * (1 + (Real.log 2)⁻¹) ^ k :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hnormalized (physical_log_growth_normalized_le hN) k)
        (div_nonneg hC (pow_nonneg hwidth.le k))
    _ = (C * (1 + (Real.log 2)⁻¹) ^ k) / width ^ k := by ring

/-- The actual mixed Euler-operator words of the genuine P4B profile,
uniform throughout the compact b-band. This uses the proved operator
dictionary, so the conclusion is stated in original prime variables. -/
theorem exists_compact_realB_prime_EulerWord_budget
    (k : ℕ) {bHi : ℝ} (hbHi : 0 ≤ bHi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 ≤ b → b ≤ bHi →
      ∀ width : ℝ, 0 < width → ∀ N : ℕ, 2 ≤ N →
      ∀ T : ℝ, ∀ p : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
      ∀ w : Fin k → Fin 2,
        |primeEulerWord k w (smoothPrimeVariableProfile b N T width) p| ≤
          C / width ^ k := by
  obtain ⟨C, hC, hbudget⟩ := exists_compact_realB_prime_mixed_chart_budget k hbHi
  refine ⟨C, hC, ?_⟩
  intro b hb hbMax width hwidth N hN T p hp w
  rw [primeEulerWord_eq_mixed_chart_tensor (smoothPrimeVariableProfile b N T width)
    (contDiffOn_smoothPrimeVariableProfile b N T width) hp k w]
  let D := iteratedFDeriv ℝ k
    (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) 0
  let m : Fin k → (Fin 2 → ℝ) := fun j => primeEulerCoordinateUnit (w j)
  have hpnonneg : 0 ≤ ∏ j : Fin k, ‖m j‖ :=
    Finset.prod_nonneg (fun j _hj => norm_nonneg _)
  have hple : (∏ j : Fin k, ‖m j‖) ≤ 1 :=
    Finset.prod_le_one (fun j _hj => norm_nonneg _)
      (fun j _hj => primeEulerCoordinateUnit_norm_le (w j))
  change |D m| ≤ _
  calc
    |D m| ≤ ‖D‖ * ∏ j : Fin k, ‖m j‖ := by
      simpa only [Real.norm_eq_abs] using D.le_opNorm m
    _ ≤ (C / width ^ k) * 1 :=
      mul_le_mul (hbudget b hb hbMax width hwidth N hN T p hp 0) hple hpnonneg
        (div_nonneg hC (pow_nonneg hwidth.le k))
    _ = C / width ^ k := mul_one _

end

end ImbalancedChen.P4B
