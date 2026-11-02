import Mathlib
import ImbalancedChen.Part3TwoLongNaturalInternalP2

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The three ACTUAL D profiles consume the internally derived natural P2.
This removes FixedMP2 from the original finite same-rho Brun consumer.
It is not the complete rough E4: the E1/E3 exact means, rough replacement,
Mellin-twisted log profiles and the true HB row bindings remain explicit
separate obligations. No claim is made about merely C2 arbitrary profiles.
-/
namespace ImbalancedChen.Part3.TwoLongThreeBrunInternalP2
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles
open ImbalancedChen.Part3.TwoLongActualDoublePeriodization
open ImbalancedChen.Part3.TwoLongActualThreeBrunP2Receiver
open ImbalancedChen.Part3.TwoLongInternalP2Modes
open ImbalancedChen.Part3.TwoLongNaturalInternalP2

def leftSchwartz {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (label : Fin 3) : 𝓢(ℝ, ℂ) :=
  if label=1 then actualGapSchwartz hd hs else actualUpperSchwartz hd hs

def rightSchwartz {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (label : Fin 3) : 𝓢(ℝ, ℂ) :=
  if label=2 then actualGapSchwartz hd hs else actualUpperSchwartz hd hs

theorem leftSchwartz_coe {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (label : Fin 3) : (leftSchwartz hd hs label : ℝ → ℂ) = leftProfile delta label := by
  funext x
  by_cases h : label=1 <;> simp [leftSchwartz,leftProfile,h]

theorem rightSchwartz_coe {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (label : Fin 3) : (rightSchwartz hd hs label : ℝ → ℂ) = rightProfile delta label := by
  funext x
  by_cases h : label=2 <;> simp [rightSchwartz,rightProfile,h]

/-- At the genuine divisor scales U/d1,V/d2 and short product m*d1*d2.
No coprimality of the expanded short product is imposed: the nonprimitive
case is paid by the proved zero original count and zero original mean. -/
theorem actualSmoothCore_internalP2 (hWeil : CompositeWeilInput)
    {delta U V : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (label : Fin 3) (alpha : ℂ)
    (m a q d₁ d₂ : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ‖actualSmoothCore delta label alpha U V m d₁ d₂ a q‖ ≤
      (internalP2Constant*gapCost^2/delta^4)*‖alpha‖*modulusBudget q := by
  have hL := leftSchwartz_coe hd hs label
  have hR := rightSchwartz_coe hd hs label
  have hLS : Function.support (leftSchwartz hd hs label : ℝ → ℂ) ⊆
      Icc (1/2 : ℝ) (5/2) := by rw [hL]; exact leftProfile_support hd hs label
  have hRS : Function.support (rightSchwartz hd hs label : ℝ → ℂ) ⊆
      Icc (1/2 : ℝ) (5/2) := by rw [hR]; exact rightProfile_support hd hs label
  have hD₁ : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hD₂ : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hp := naturalCore_P2 hWeil (leftSchwartz hd hs label) (rightSchwartz hd hs label)
    hLS hRS (div_pos hU hD₁) (div_pos hV hD₂) (m*d₁*d₂) a q hq ha alpha
  rw [hL,hR] at hp
  have hC := internalP2Constant_pos.le
  have hG := gapCost_nonneg
  have hB := modulusBudget_nonneg q
  have hNL := N2_nonneg (leftProfile delta label)
  have hNR := N2_nonneg (rightProfile delta label)
  calc
    _ ≤ internalP2Constant*‖alpha‖*N2 (leftProfile delta label)*
        N2 (rightProfile delta label)*modulusBudget q := hp
    _ ≤ internalP2Constant*‖alpha‖*(gapCost/delta^2)*
        (gapCost/delta^2)*modulusBudget q := by
      gcongr
      · exact leftProfile_N2 hd hs label
      · exact rightProfile_N2 hd hs label
    _ = _ := by field_simp [hd.ne']; ring

theorem actualSmoothCore_q1 (delta : ℝ) (label : Fin 3) (alpha : ℂ)
    (U V : ℝ) (m d₁ d₂ a : ℕ) :
    actualSmoothCore delta label alpha U V m d₁ d₂ a 1 = 0 :=
  naturalCore_q1 _ _ _ _ _ _ _ _ _

/-- The same independently defined finite E4 smooth-core consumer as D,
now with its internal P2 hypothesis eliminated. Q includes q=1, rho stays
literal and signed, and the original profiles/scales/Brun pair coefficients
are unchanged. The remaining modulus moment is explicit, not assumed paid.
All three labels (upper-upper, gap-upper, upper-gap) are covered. -/
theorem finite_threeBrun_sameRho_internalP2 (hWeil : CompositeWeilInput)
    {delta U V : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (label : Fin 3) (m a : ℕ) (Q : Finset ℕ) (R : Finset (ℕ×ℕ))
    (rho : ℕ → ℂ) (alpha c : (ℕ×ℕ) → ℂ)
    (hQ : ∀ q ∈ Q, 0 < q ∧ Nat.Coprime a q)
    (hR : ∀ d ∈ R, 0 < d.1 ∧ 0 < d.2) :
    ‖∑ q ∈ Q, rho q * ∑ d ∈ R, c d *
      actualSmoothCore delta label (alpha d) U V m d.1 d.2 a q‖ ≤
      (internalP2Constant*gapCost^2/delta^4)*
        (∑ d ∈ R, ‖c d‖*‖alpha d‖)*
        (∑ q ∈ Q, ‖rho q‖*modulusBudget q) := by
  let C : ℝ := internalP2Constant*gapCost^2/delta^4
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ d ∈ R,
        c d * actualSmoothCore delta label (alpha d) U V m d.1 d.2 a q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ∑ d ∈ R,
        ‖c d‖*‖actualSmoothCore delta label (alpha d) U V m d.1 d.2 a q‖ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ∑ d ∈ R,
        ‖c d‖*(C*‖alpha d‖*modulusBudget q) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro d hdr
      exact mul_le_mul_of_nonneg_left
        (actualSmoothCore_internalP2 hWeil hd hs hU hV label (alpha d) m a q d.1 d.2
          (hQ q hq).1 (hQ q hq).2 (hR d hdr).1 (hR d hdr).2) (norm_nonneg _)
    _ = ∑ q ∈ Q, (C*∑ d ∈ R, ‖c d‖*‖alpha d‖)*(‖rho q‖*modulusBudget q) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hdr
      ring
    _ = _ := by rw [Finset.mul_sum]

end
end ImbalancedChen.Part3.TwoLongThreeBrunInternalP2
