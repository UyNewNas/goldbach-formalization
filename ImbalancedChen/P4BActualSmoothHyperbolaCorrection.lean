import ImbalancedChen.P4BWeightedHyperbolaSlotDecay
import ImbalancedChen.P4BActualCompactSmoothFamily
import ImbalancedChen.P4BPrimitiveModulusEndpoints

/-!
# Actual-family hyperbola decay with the literal active modulus cap

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual compact smooth family's proved support supplies the original
prime-slot lower bounds and the complete-product cap, including products
above N. The modulus cap is the exact supremum of nonzero entries of the
same attached rho. Thus the finite result assumes no source mass, coefficient
amplitude, artificial rough coprimality, PP saving, or polynomial range.
The logarithm of that exact active cap remains visible. Its required full22
polynomial bound is a separate original-policy obligation, still OPEN.
-/

namespace ImbalancedChen.P4BActualSmoothHyperbolaCorrection

noncomputable section
open scoped Classical BigOperators
open Part3 P4B P4BLabelledPairDictionary P4BLabelledOuterPushforward
open P4BNoncoprimeSlotTail P4BWeightedHyperbolaSlotDecay
open P4BPrimitiveModulusEndpoints P4BActualCompactSmoothFamily

/-- This is the literal active support, rather than the displayed set's
possibly much larger zero-coefficient envelope. -/
def actualActiveUpperCap (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((attachedUpperModuli nu r epsilon retain cap N).filter
    (fun d => attachedUpperCoefficient nu r epsilon retain cap N d ≠ 0)).sup id

theorem actual_active_modulus_mem_Icc
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N d : ℕ) (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N)
    (hactive : attachedUpperCoefficient nu r epsilon retain cap N d ≠ 0) :
    d ∈ Finset.Icc 1 (actualActiveUpperCap nu r epsilon retain cap N) := by
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr
      (attachedUpperModuli_pos nu r epsilon retain cap N hd).ne'
  · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hd, hactive⟩)

/-- The complete outer correction is bounded using only the exact active
range and the actual construction's proved one-bound. -/
theorem actual_outer_correction_le_active_hyperbola
    {N K L : ℕ} (hL : 2 ≤ L)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, |V t| ≤ B)
    (hrough : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → ∀ i, L ≤ (t i).val)
    (hproduct : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → labelledProduct t ≤ K) :
    |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass (productCarrier N) (productWeight N V) d -
          finiteSourceMass (productCarrier N) (productWeight N V)) / (Nat.totient d : ℝ))| ≤
      (16 * B * (K : ℝ) / ((L : ℝ) - 1)) *
        (1 + Real.log (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ))) := by
  let Q := actualActiveUpperCap nu r epsilon retain cap N
  have hrho : ∀ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      |attachedUpperCoefficient nu r epsilon retain cap N d| ≤ 1 := by
    intro d _hd
    exact actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d
  have hfinite := outer_signed_correction_le_slot_cost_of_active_range N V
    (attachedUpperModuli nu r epsilon retain cap N) Q
    (attachedUpperCoefficient nu r epsilon retain cap N)
    (fun d hd ha => actual_active_modulus_mem_Icc nu r epsilon retain cap N d hd ha)
    1 (by norm_num) hrho
  have hlog : 0 ≤ 1 + Real.log (max 1 (Q : ℝ)) := by
    have := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    linarith
  have heq : (∑ t ∈ labelledPrimeTuples 2 N, |V t| * (1 *
      (∑ i : Fin 2, (4 / (((t i).val : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))))))) =
      (∑ t ∈ labelledPrimeTuples 2 N,
        |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1))) *
          (1 + Real.log (max 1 (Q : ℝ))) := by
    simp_rw [← Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  rw [heq] at hfinite
  exact hfinite.trans (mul_le_mul_of_nonneg_right
    (full_weighted_slot_cost_le hL V B hB hV hrough hproduct) hlog)

/-- The concrete actual family discharges the slot and product geometry.
Only the caller's natural rounding endpoints L and K remain in this finite
version; no distribution estimate or unsifted mass input is used. -/
theorem actual_compact_smooth_correction_le_hyperbola
    {b0 b1 kappa kappaZero theta precision widthMax b : ℝ}
    (F : ActualCompactSmoothFamily b0 b1 kappa kappaZero theta precision widthMax)
    (hb0 : b0 ≤ b) (hb1 : b ≤ b1) {N K L : ℕ} (hN : 2 ≤ N) (hL : 2 ≤ L)
    (hLpow : (L : ℝ) ≤ (N : ℝ) ^ theta)
    (hK : Real.exp F.width * (N : ℝ) ≤ (K : ℝ))
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass (productCarrier N)
            (productWeight N (smoothPhysicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) F.width)) d -
          finiteSourceMass (productCarrier N)
            (productWeight N (smoothPhysicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) F.width))) / (Nat.totient d : ℝ))| ≤
      (16 * (K : ℝ) / ((L : ℝ) - 1)) *
        (1 + Real.log (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ))) := by
  have hV : ∀ t ∈ labelledPrimeTuples 2 N,
      |smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t| ≤ 1 := by
    intro t _ht
    have hbnd := smoothPhysicalPairOuterRamp_bounds b N
      (manuscriptHalfProductCutoff kappa N) F.width t
    simpa only [abs_of_nonneg hbnd.1] using hbnd.2
  have hrough : ∀ t ∈ labelledPrimeTuples 2 N,
      smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t ≠ 0 →
        ∀ i, L ≤ (t i).val := by
    intro t ht hn i
    have hp := primeTuplePoint_mem_positivePrimeOrthant ht
    have hn' : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
        F.width (primeTuplePoint N t) ≠ 0 := by
      simpa only [smoothPhysicalPairOuterRamp_eq_primeVariableProfile] using hn
    have hprime := F.prime_lower_support b hb0 hb1 N hN (primeTuplePoint N t) hp hn' i
    have hreal := hLpow.trans_lt hprime
    change (L : ℝ) < ((t i).val : ℝ) at hreal
    exact_mod_cast hreal.le
  have hproduct : ∀ t ∈ labelledPrimeTuples 2 N,
      smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t ≠ 0 →
        labelledProduct t ≤ K := by
    intro t ht hn
    have hp := primeTuplePoint_mem_positivePrimeOrthant ht
    have hn' : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
        F.width (primeTuplePoint N t) ≠ 0 := by
      simpa only [smoothPhysicalPairOuterRamp_eq_primeVariableProfile] using hn
    have hprod := (F.product_window b hb0 hb1 N hN (primeTuplePoint N t) hp hn').2
    have hreal : (labelledProduct t : ℝ) ≤ (K : ℝ) := by
      simpa only [labelledProduct, Fin.prod_univ_two, Nat.cast_mul, primeTuplePoint] using
        (hprod.trans_le hK).le
    exact_mod_cast hreal
  simpa only [mul_one] using actual_outer_correction_le_active_hyperbola
    hL nu r epsilon retain cap
    (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width)
    1 (by norm_num) hV hrough hproduct

end
end ImbalancedChen.P4BActualSmoothHyperbolaCorrection
