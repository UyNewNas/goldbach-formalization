import ImbalancedChen.P4BSmoothPrimeEulerFlowBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Full mixed Frechet budgets and positive prime logarithmic charts

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The scalar affine chain rule is lifted to the full iterated Frechet norm.
Pinned Mathlib's binomial product bound then controls all mixed directions,
not only the diagonal. No mixed derivative bound is a hypothesis for the
actual profile. The genuine positive prime chart is p_i exp(z_i).
-/

namespace ImbalancedChen.P4B

noncomputable section
open scoped BigOperators

/-- The full norm of an affine scalar pullback, retaining exactly k row factors. -/
theorem norm_iteratedFDeriv_scalar_affine_le
    (k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (x : Fin 2 → ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => f (a + L y)) x‖ ≤
      |iteratedDeriv k f (a + L x)| * ‖L‖ ^ k := by
  let g : ℝ → ℝ := fun t => f (a + t)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ k (g ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hg x (by simp)]
  have hnorm := (iteratedFDeriv ℝ k g (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => L)
  have hshift : iteratedDeriv k g (L x) = iteratedDeriv k f (a + L x) :=
    congrFun (iteratedDeriv_comp_const_add k f a) (L x)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, hshift] using hnorm

/-- Binomial norm payment for full derivatives, valid also at order zero. -/
theorem norm_iteratedFDeriv_two_mul_budget
    (k : ℕ) (f g : (Fin 2 → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : Fin 2 → ℝ) (R Cf Cg : ℝ) (hR : 0 ≤ R) (hCf : 0 ≤ Cf)
    (hleft : ∀ j : ℕ, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ Cf * R ^ j)
    (hright : ∀ j : ℕ, j ≤ k → ‖iteratedFDeriv ℝ j g x‖ ≤ Cg * R ^ j) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ Cf * Cg * (2 * R) ^ k := by
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  calc
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k - j) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (Cf * Cg * R ^ k) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hproduct := mul_le_mul (hleft j hjk)
        (hright (k - j) (Nat.sub_le k j))
        (norm_nonneg _) (mul_nonneg hCf (pow_nonneg hR j))
      calc
        (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j f x‖ *
            ‖iteratedFDeriv ℝ (k - j) g x‖ =
            (k.choose j : ℝ) * (‖iteratedFDeriv ℝ j f x‖ *
              ‖iteratedFDeriv ℝ (k - j) g x‖) := by ring
        _ ≤ (k.choose j : ℝ) * ((Cf * R ^ j) * (Cg * R ^ (k - j))) :=
          mul_le_mul_of_nonneg_left hproduct (Nat.cast_nonneg _)
        _ = (k.choose j : ℝ) * (Cf * Cg * (R ^ j * R ^ (k - j))) := by ring
        _ = (k.choose j : ℝ) * (Cf * Cg * R ^ k) := by
          rw [← pow_add, Nat.add_sub_of_le hjk]
    _ = 2 ^ k * (Cf * Cg * R ^ k) := by rw [← Finset.sum_mul, hsum]
    _ = Cf * Cg * (2 * R) ^ k := by rw [mul_pow]; ring

/-- The four gates have a full derivative norm budget, with exact order k. -/
theorem norm_iteratedFDeriv_four_gate_product_budget
    (k : ℕ) (f : Fin 4 → (Fin 2 → ℝ) → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : Fin 2 → ℝ)
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hfactor : ∀ i : Fin 4, ∀ j : ℕ, j ≤ k →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ B * R ^ j) :
    ‖iteratedFDeriv ℝ k (fun y => ∏ i : Fin 4, f i y) x‖ ≤
      B ^ 4 * (4 * R) ^ k := by
  let g0 : (Fin 2 → ℝ) → ℝ := fun y => f 0 y * f 1 y
  let g1 : (Fin 2 → ℝ) → ℝ := fun y => f 2 y * f 3 y
  have hg0 : ContDiff ℝ ∞ g0 := (hf 0).mul (hf 1)
  have hg1 : ContDiff ℝ ∞ g1 := (hf 2).mul (hf 3)
  have hpair0 (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j g0 x‖ ≤ (B * B) * (2 * R) ^ j :=
    norm_iteratedFDeriv_two_mul_budget j (f 0) (f 1) (hf 0) (hf 1)
      x R B B hR hB
      (fun i hi => hfactor 0 i (hi.trans hj))
      (fun i hi => hfactor 1 i (hi.trans hj))
  have hpair1 (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j g1 x‖ ≤ (B * B) * (2 * R) ^ j :=
    norm_iteratedFDeriv_two_mul_budget j (f 2) (f 3) (hf 2) (hf 3)
      x R B B hR hB
      (fun i hi => hfactor 2 i (hi.trans hj))
      (fun i hi => hfactor 3 i (hi.trans hj))
  have hprod : (fun y => ∏ i : Fin 4, f i y) = fun y => g0 y * g1 y := by
    funext y
    rw [Fin.prod_univ_four]
    dsimp [g0, g1]
    ring
  rw [hprod]
  have hfinal := norm_iteratedFDeriv_two_mul_budget k g0 g1 hg0 hg1
    x (2 * R) (B * B) (B * B) (mul_nonneg (by norm_num) hR)
    (mul_nonneg hB hB) hpair0 hpair1
  simpa only [show (B * B) * (B * B) = B ^ 4 by ring,
    show (2 : ℝ) * (2 * R) = 4 * R by ring] using hfinal

/-- All-order full Frechet norm of the actual physical profile. This
controls arbitrary mixed directions, not just repeated equal directions. -/
theorem exists_smoothPhysicalProfile_iteratedFDeriv_budget (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ x : Fin 2 → ℝ,
        ‖iteratedFDeriv ℝ k (smoothPhysicalProfile b N T width) x‖ ≤
          (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k := by
  obtain ⟨B, hB, hscalar⟩ := exists_smoothGateUpperStep_finite_derivative_budget k
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcb : 0 ≤ 2 + |b| := by linarith [abs_nonneg b]
  let C : ℝ := B ^ 4 * (4 * (2 + |b|)) ^ k
  refine ⟨C, mul_nonneg (pow_nonneg hB0 4)
    (pow_nonneg (mul_nonneg (by norm_num) hcb) k), ?_⟩
  intro width hwidth N hN T x
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  let R : ℝ := ((2 + |b|) * (1 + Real.log (N : ℝ))) / width
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
      _ ≤ (B / width ^ j) * (((2 + |b|) * (1 + Real.log (N : ℝ))) ^ j) :=
        mul_le_mul (hscalar j hj width hwidth _)
          (pow_le_pow_left₀ (norm_nonneg _) (smoothPhysicalWallRow_norm_le b N hN i) j)
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

/-- Independent multiplicative coordinates on the positive prime orthant. -/
def primeEulerChart (p z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => p i * Real.exp (z i)

theorem primeVariableLogPoint_primeEulerChart (N : ℕ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) (z : Fin 2 → ℝ) :
    primeVariableLogPoint N (primeEulerChart p z) =
      primeVariableLogPoint N p + (Real.log (N : ℝ))⁻¹ • z := by
  funext i
  simp only [primeVariableLogPoint, primeEulerChart, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Real.log_mul (hp i).ne' (Real.exp_pos (z i)).ne', Real.log_exp]
  simp only [div_eq_mul_inv]
  ring

/-- Exact identity for the entire mixed derivative tensor of the genuine
prime chart. All k slots receive the normalization (log N)^-1. -/
theorem iteratedFDeriv_smoothPrimeVariableProfile_primeEulerChart
    (k : ℕ) (b : ℝ) (N : ℕ) (T width : ℝ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) (z : Fin 2 → ℝ) :
    iteratedFDeriv ℝ k
      (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) z =
      (Real.log (N : ℝ))⁻¹ ^ k • iteratedFDeriv ℝ k (smoothPhysicalProfile b N T width)
        (primeVariableLogPoint N p + (Real.log (N : ℝ))⁻¹ • z) := by
  let g : (Fin 2 → ℝ) → ℝ := fun y =>
    smoothPhysicalProfile b N T width (primeVariableLogPoint N p + y)
  have hg : ContDiff ℝ k g :=
    (contDiff_smoothPhysicalProfile b N T width).comp (contDiff_const.add contDiff_id)
  have heq : (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) =
      fun y => g ((Real.log (N : ℝ))⁻¹ • y) := by
    funext y
    unfold smoothPrimeVariableProfile
    rw [primeVariableLogPoint_primeEulerChart N hp]
  rw [heq]
  rw [congrFun (iteratedFDeriv_comp_const_smul (Real.log (N : ℝ))⁻¹ hg) z]
  congr 1
  exact iteratedFDeriv_comp_add_left k (primeVariableLogPoint N p)
    ((Real.log (N : ℝ))⁻¹ • z)

/-- Full mixed prime-chart derivative norm, uniform even in the chart
point z. The displayed bound has no N or prime-coordinate dependence. -/
theorem exists_smoothPrimeVariableProfile_mixed_chart_budget (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p : Fin 2 → ℝ,
      p ∈ positivePrimeOrthant → ∀ z : Fin 2 → ℝ,
        ‖iteratedFDeriv ℝ k
          (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) z‖ ≤
          C / width ^ k := by
  obtain ⟨C, hC, hbudget⟩ := exists_smoothPhysicalProfile_iteratedFDeriv_budget k b
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hscale : 0 ≤ 1 + (Real.log 2)⁻¹ :=
    add_nonneg zero_le_one (inv_nonneg.mpr htwo.le)
  refine ⟨C * (1 + (Real.log 2)⁻¹) ^ k,
    mul_nonneg hC (pow_nonneg hscale k), ?_⟩
  intro width hwidth N hN T p hp z
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
      mul_le_mul_of_nonneg_left (hbudget width hwidth N hN T _)
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

/-- Every ordered list of unit directions is controlled by the same
constant. In particular the directions can independently select either
coordinate, with any repetitions: these are the mixed log-coordinate
derivatives on the actual positive prime chart. -/
theorem exists_smoothPrimeVariableProfile_mixed_chart_apply_budget
    (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p : Fin 2 → ℝ,
      p ∈ positivePrimeOrthant → ∀ z : Fin 2 → ℝ,
      ∀ m : Fin k → (Fin 2 → ℝ), (∀ i, ‖m i‖ ≤ 1) →
        |iteratedFDeriv ℝ k
          (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) z m| ≤
          C / width ^ k := by
  obtain ⟨C, hC, hbudget⟩ := exists_smoothPrimeVariableProfile_mixed_chart_budget k b
  refine ⟨C, hC, ?_⟩
  intro width hwidth N hN T p hp z m hm
  let D := iteratedFDeriv ℝ k
    (fun y => smoothPrimeVariableProfile b N T width (primeEulerChart p y)) z
  have hpnonneg : 0 ≤ ∏ i : Fin k, ‖m i‖ := Finset.prod_nonneg (fun i _hi => norm_nonneg _)
  have hple : (∏ i : Fin k, ‖m i‖) ≤ 1 :=
    Finset.prod_le_one (fun i _hi => norm_nonneg _) (fun i _hi => hm i)
  change |D m| ≤ _
  calc
    |D m| ≤ ‖D‖ * ∏ i : Fin k, ‖m i‖ := by
      simpa only [Real.norm_eq_abs] using D.le_opNorm m
    _ ≤ (C / width ^ k) * 1 :=
      mul_le_mul (hbudget width hwidth N hN T p hp z) hple hpnonneg
        (div_nonneg hC (pow_nonneg hwidth.le k))
    _ = C / width ^ k := mul_one _

end

end ImbalancedChen.P4B
