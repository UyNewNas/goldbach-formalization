import ImbalancedChen.P2FiniteMarkedGamma5LogProfileCore
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO ENDPOINT CREDIT.

All mixed logarithmic derivatives of the actual Gamma5 gate product have a
uniform inverse-width budget. The constant precedes both moving logarithmic
endpoints, the positive width, and the base point. The variable complete prefix,
the two fresh slots, every rough-tail slot (including the empty tail), and the
original product wall are those of P2FiniteMarkedGamma5LogExtension.profile.

The scalar estimate is reused from P4BSmoothStepDerivativeBudget. The finite
product estimate is Mathlib's norm_iteratedFDeriv_prod_le, with its actual
multinomial coefficients; no private Wu product proof is copied or assumed.

This pays a quantitative logarithmic smoothness obligation. It does not assert
a compactly supported smooth physical extension, a uniform tail-rank bound,
a collar estimate, or a prime-product distribution conclusion.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5LogExtension

noncomputable section
open Finset Real P4B
open P2SeedOmegaLiteralFibre (a0 a2)
open scoped BigOperators Classical ContDiff

private def prefixRow (r : ℕ) : Point r →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ((Fin 2 → ℝ) × (Fin r → ℝ))

private def pairRow {r : ℕ} (i : Fin 2) : Point r →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin r → ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ ((Fin 2 → ℝ) × (Fin r → ℝ))))

private def tailRow {r : ℕ} (i : Fin r) : Point r →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin r → ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ ((Fin 2 → ℝ) × (Fin r → ℝ))))

/-- The actual constant linear row of each original Gamma5 wall. In
particular the bad-square row has coefficient two, and the product row
contains every rough-tail coordinate with multiplicity one. -/
def marginRow {r : ℕ} : Gate r → Point r →L[ℝ] ℝ
  | .lower i => pairRow i + a0 • prefixRow r
  | .upper i => -(a2 • prefixRow r) - pairRow i
  | .pairOrder => pairRow 1 - pairRow 0
  | .badSquare => prefixRow r + (2 : ℝ) • pairRow 0 + pairRow 1
  | .rough i => tailRow i + a0 • prefixRow r
  | .tailOrder i j => tailRow j - tailRow i
  | .product => -(prefixRow r + pairRow 0 + pairRow 1 + ∑ i, tailRow i)

theorem margin_eq_offset_add_row {r : ℕ} (logQ logN : ℝ)
    (v : Point r) (g : Gate r) :
    margin logQ logN v g = margin logQ logN (0 : Point r) g + marginRow g v := by
  cases g <;> simp [margin, marginRow, prefixRow, pairRow, tailRow, smul_eq_mul] <;> ring

theorem margin_scale {r : ℕ} (c logQ logN : ℝ) (v : Point r) (g : Gate r) :
    margin (c * logQ) (c * logN) (c • v) g = c * margin logQ logN v g := by
  cases g <;>
    simp only [margin, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum] <;> ring

/-- Each fixed original affine gate has a uniform unit-width tensor budget.
The constant is derived from the scalar transition estimate and the norm of
its actual row; it does not depend on either moving endpoint or base point. -/
theorem gate_unit_tensor_budget {r : ℕ} (g : Gate r) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (logQ logN : ℝ) (x : Point r),
      ‖iteratedFDeriv ℝ q
        (fun y : Point r => smoothGateUpperStep 1 (margin logQ logN y g)) x‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := exists_smoothGateUpperStep_derivative_budget q
  refine ⟨C * ‖marginRow g‖ ^ q,
    mul_nonneg (zero_le_one.trans hC) (pow_nonneg (norm_nonneg _) _), ?_⟩
  intro logQ logN x
  let a := margin logQ logN (0 : Point r) g
  let f := fun t : ℝ => smoothGateUpperStep 1 (a + t)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_smoothGateUpperStep _).comp (contDiff_const.add contDiff_id)
  have heq : (fun y : Point r => smoothGateUpperStep 1 (margin logQ logN y g)) =
      f ∘ marginRow g := by
    funext y
    rw [margin_eq_offset_add_row]
    rfl
  rw [heq, (marginRow g).iteratedFDeriv_comp_right hf x
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hscalar : ‖iteratedFDeriv ℝ q f (marginRow g x)‖ ≤ C := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have he := congrFun (iteratedDeriv_comp_const_add q (smoothGateUpperStep 1) a)
      (marginRow g x)
    rw [show iteratedDeriv q f (marginRow g x) = _ from he]
    simpa only [one_pow, div_one] using H 1 zero_lt_one (a + marginRow g x)
  calc
    _ ≤ ‖iteratedFDeriv ℝ q f (marginRow g x)‖ * ‖marginRow g‖ ^ q := by
      simpa only [prod_const, card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ q f (marginRow g x)).norm_compContinuousLinearMap_le
          (fun _ : Fin q => marginRow g)
    _ ≤ C * ‖marginRow g‖ ^ q :=
      mul_le_mul_of_nonneg_right hscalar (pow_nonneg (norm_nonneg _) _)

/-- The finite Leibniz estimate is applied to exactly the active original
gate program. Its constant depends only on the fixed rank and derivative
order. Inactive tail-order pairs are not inserted into the product. -/
theorem profile_unit_tensor_budget (r q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (logQ logN : ℝ) (x : Point r),
      ‖iteratedFDeriv ℝ q (profile logQ logN 1) x‖ ≤ C := by
  choose C hC HC using fun (g : Gate r) (n : ℕ) => gate_unit_tensor_budget g n
  refine ⟨∑ p ∈ (program r).sym q,
    ((p : Multiset (Gate r)).countPerms : ℝ) *
      ∏ g ∈ program r, C g ((p : Multiset (Gate r)).count g), ?_, ?_⟩
  · exact sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _)
      (prod_nonneg (fun g _ => hC g _)))
  intro logQ logN x
  have hF (g : Gate r) : ContDiff ℝ ∞
      (fun y : Point r => smoothGateUpperStep 1 (margin logQ logN y g)) :=
    (contDiff_smoothGateUpperStep _).comp (contDiff_margin logQ logN g)
  have hprod := norm_iteratedFDeriv_prod_le
    (fun (g : Gate r) (_ : g ∈ program r) => hF g) (x := x) (n := q)
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  apply hprod.trans
  apply sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact prod_le_prod (fun _ _ => norm_nonneg _)
    (fun g _ => HC g ((p : Multiset (Gate r)).count g) logQ logN x)

/-- Exact common-width rescaling of the complete original profile. Both
physical logarithmic endpoints and every logarithmic slot scale together. -/
theorem profile_scaled_unit {r : ℕ} (logQ logN width : ℝ) :
    profile (r := r) logQ logN width = fun x : Point r =>
      profile (logQ / width) (logN / width) 1 (width⁻¹ • x) := by
  funext x
  unfold profile
  apply prod_congr rfl
  intro g _
  have hm : margin (logQ / width) (logN / width) (width⁻¹ • x) g =
      margin logQ logN x g / width := by
    simpa only [div_eq_mul_inv, mul_comm] using margin_scale width⁻¹ logQ logN x g
  simp only [smoothGateUpperStep, div_one, hm]

/-- All mixed logarithmic derivatives of the actual Gamma5 profile obey
the inverse-width budget. No derivative, PP, density, or endpoint estimate
is supplied as a premise. The constant is chosen before both endpoints,
the width, and every base point. -/
theorem profile_tensor_budget (r q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (logQ logN width : ℝ), 0 < width → ∀ x : Point r,
      ‖iteratedFDeriv ℝ q (profile logQ logN width) x‖ ≤ C / width ^ q := by
  obtain ⟨C, hC, H⟩ := profile_unit_tensor_budget r q
  refine ⟨C, hC, ?_⟩
  intro logQ logN width hw x
  let u := profile (r := r) (logQ / width) (logN / width) 1
  let M : Point r →L[ℝ] Point r :=
    width⁻¹ • ContinuousLinearMap.id ℝ (Point r)
  have hu : ContDiff ℝ ∞ u := contDiff_profile _ _ _
  have hM : ‖M‖ ≤ width⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hw.le)
    intro y
    simp only [M, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
    exact le_rfl
  rw [profile_scaled_unit logQ logN width]
  change ‖iteratedFDeriv ℝ q (u ∘ M) x‖ ≤ _
  rw [M.iteratedFDeriv_comp_right hu x
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ q u (M x)‖ * ‖M‖ ^ q := by
      simpa only [prod_const, card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ q u (M x)).norm_compContinuousLinearMap_le
          (fun _ : Fin q => M)
    _ ≤ C * (width⁻¹) ^ q :=
      mul_le_mul (H _ _ _) (pow_le_pow_left₀ (norm_nonneg _) hM q)
        (pow_nonneg (norm_nonneg _) _) hC
    _ = C / width ^ q := by rw [inv_pow, div_eq_mul_inv]

end
end ImbalancedChen.P2FiniteMarkedGamma5LogExtension
