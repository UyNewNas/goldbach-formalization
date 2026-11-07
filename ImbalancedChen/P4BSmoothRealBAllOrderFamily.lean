import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget

/-!
# All affine directional orders uniformly over a real-b band

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For each derivative order k and upper endpoint bHi, choose one constant
before b in [0,bHi], the positive width, N >= 2, the cutoff T, base point
and direction. The actual four affine walls and genuine smoothTransition
derivatives produce this constant. No derivative budget is an input.
The width^-k, physical (1+log N)^k and direction norm^k are retained.

This is a geometric family prerequisite. It neither supplies the signed
prime-product estimate nor asserts actualwinner whole-box licensing.
-/

namespace ImbalancedChen.P4B

noncomputable section

/-- The real-b parameter has a uniform row bound before choosing the
profile point or cutoff. -/
theorem smoothPhysicalWallRow_apply_abs_le_of_b_le
    {b bHi : ℝ} (hb : 0 ≤ b) (hbHi : b ≤ bHi)
    (N : ℕ) (hN : 2 ≤ N) (i : Fin 4) (h : Fin 2 → ℝ) :
    |smoothPhysicalWallRow b N i h| ≤
      ((2 + bHi) * (1 + Real.log (N : ℝ))) * ‖h‖ := by
  have hlog : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have := Real.log_nonneg hNreal
    linarith
  apply (smoothPhysicalWallRow_apply_abs_le b N hN i h).trans
  rw [abs_of_nonneg hb]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (add_le_add_left hbHi 2) hlog) (norm_nonneg h)

/-- The constant depends only on k and the real-b upper endpoint, while
all physical parameters are quantified afterwards. It includes k=0 and
the zero direction without division by a direction norm. -/
theorem exists_realB_family_directional_derivative_budget
    (k : ℕ) {bHi : ℝ} (hbHi : 0 ≤ bHi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 ≤ b → b ≤ bHi →
      ∀ width : ℝ, 0 < width → ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ x h : Fin 2 → ℝ,
        |iteratedDeriv k (smoothPhysicalProfileLine b N T width x h) 0| ≤
          (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k * ‖h‖ ^ k := by
  obtain ⟨B, hB, hscalar⟩ := exists_smoothGateUpperStep_finite_derivative_budget k
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcb : 0 ≤ 2 + bHi := by linarith only [hbHi]
  let C : ℝ := B ^ 4 * (4 * (2 + bHi)) ^ k
  refine ⟨C, mul_nonneg (pow_nonneg hB0 4)
    (pow_nonneg (mul_nonneg (by norm_num) hcb) k), ?_⟩
  intro b hb hbMax width hwidth N hN T x h
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  let R : ℝ := (((2 + bHi) * (1 + Real.log (N : ℝ))) * ‖h‖) / width
  have hR : 0 ≤ R :=
    div_nonneg (mul_nonneg (mul_nonneg hcb (by linarith)) (norm_nonneg h)) hwidth.le
  let f : Fin 4 → ℝ → ℝ := fun i t => smoothGateUpperStep width
    (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * t)
  have hstep : ContDiff ℝ ∞ (smoothGateUpperStep width) :=
    contDiff_smoothGateUpperStep width
  have hf (i : Fin 4) : ContDiff ℝ ∞ (f i) :=
    hstep.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hfactor (i : Fin 4) (j : ℕ) (hj : j ≤ k) :
      |iteratedDeriv j (f i) 0| ≤ B * R ^ j := by
    change |iteratedDeriv j (fun t => smoothGateUpperStep width
      (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * t)) 0| ≤ _
    rw [iteratedDeriv_comp_real_affine j (smoothGateUpperStep width) hstep
      (smoothPhysicalProfileMargin b N T x i) (smoothPhysicalWallRow b N i h) 0,
      abs_mul, abs_pow]
    calc
      |smoothPhysicalWallRow b N i h| ^ j *
          |iteratedDeriv j (smoothGateUpperStep width)
            (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * 0)| ≤
          |smoothPhysicalWallRow b N i h| ^ j * (B / width ^ j) :=
        mul_le_mul_of_nonneg_left (hscalar j hj width hwidth _)
          (pow_nonneg (abs_nonneg _) j)
      _ ≤ (((2 + bHi) * (1 + Real.log (N : ℝ))) * ‖h‖) ^ j *
            (B / width ^ j) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _)
            (smoothPhysicalWallRow_apply_abs_le_of_b_le hb hbMax N hN i h) j)
          (div_nonneg hB0 (pow_nonneg hwidth.le j))
      _ = B * R ^ j := by
        dsimp only [R]
        rw [div_pow]
        ring
  rw [smoothPhysicalProfileLine_eq_affine_gate_product]
  have hfour := abs_iteratedDeriv_four_gate_product_le k f hf 0 R B hR hB0 hfactor
  have hscale : B ^ 4 * (4 * R) ^ k =
      (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k * ‖h‖ ^ k := by
    dsimp [C, R]
    simp only [mul_pow, div_pow]
    ring
  exact hfour.trans_eq hscale

end

end ImbalancedChen.P4B
