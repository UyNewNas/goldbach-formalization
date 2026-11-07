import Mathlib
import ImbalancedChen.Part3TwoLongQuantitativeTransitionProfiles
import ImbalancedChen.Part3TwoLongFixedMRectangularCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The manuscript's universal fixed-m P2 bound is an UNSUPPLIED INTERNAL
interface here. It must be derived from P1 double periodization together
with the named composite Weil/Ramanujan inputs; it is not a deferred
classical primitive. This source only displays a conditional receiver.
Actual three smooth profiles and their uniform delta^-2 N2 bounds are
constructed independently in the companion source. Neither the conditional
finite inequality nor this contract discharges P2 or completes original E4.
-/
namespace ImbalancedChen.Part3.TwoLongActualThreeBrunP2Receiver
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles

/-- Literal divisor count in the composite P2 bound. -/
def tau (q : ℕ) : ℝ := q.divisors.card

def modulusBudget (q : ℕ) : ℝ :=
  Real.sqrt (q : ℝ) * tau q + (tau q)^2 / (Nat.totient q : ℝ)

theorem modulusBudget_nonneg (q : ℕ) : 0 ≤ modulusBudget q := by
  unfold modulusBudget tau
  positivity

/-- Exact UNSUPPLIED INTERNAL P2 interface, quantified over all fixed-m
compact C2 profiles. The original paper derives P2 from P1 and the named
composite Weil/Ramanujan inputs. It is not itself an external primitive.
No theorem in this file supplies this proposition, and no P2 proof
obligation is discharged by assuming it in the conditional receiver. -/
def FixedMP2 (constant : ℝ) : Prop :=
  ∀ (f g : ℝ → ℂ), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    Function.support f ⊆ Icc (1/2 : ℝ) (5/2) →
    Function.support g ⊆ Icc (1/2 : ℝ) (5/2) →
    ∀ (U V : ℝ), 0 < U → 0 < V → ∀ (m a q : ℕ), 0 < q → Nat.Coprime a q →
    ∀ alpha : ℂ,
      ‖fixedMCore (wideWindow U) (wideWindow V) m a q alpha f g U V‖ ≤
        constant * ‖alpha‖ * N2 f * N2 g * modulusBudget q

def leftProfile (delta : ℝ) (label : Fin 3) (x : ℝ) : ℂ :=
  if label = 1 then (gap delta x : ℂ) else (upper delta x : ℂ)

def rightProfile (delta : ℝ) (label : Fin 3) (x : ℝ) : ℂ :=
  if label = 2 then (gap delta x : ℂ) else (upper delta x : ℂ)

theorem leftProfile_C2 (delta : ℝ) (label : Fin 3) : ContDiff ℝ 2 (leftProfile delta label) := by
  by_cases h : label = 1
  · simpa [leftProfile,h] using
      (Complex.ofRealCLM.contDiff.comp (gap_smooth delta)).of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)
  · simpa [leftProfile,h] using
      (Complex.ofRealCLM.contDiff.comp (upper_smooth delta)).of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)

theorem rightProfile_C2 (delta : ℝ) (label : Fin 3) : ContDiff ℝ 2 (rightProfile delta label) := by
  by_cases h : label = 2
  · simpa [rightProfile,h] using
      (Complex.ofRealCLM.contDiff.comp (gap_smooth delta)).of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)
  · simpa [rightProfile,h] using
      (Complex.ofRealCLM.contDiff.comp (upper_smooth delta)).of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)

theorem leftProfile_support {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (label : Fin 3) : Function.support (leftProfile delta label) ⊆ Icc (1/2 : ℝ) (5/2) := by
  intro x hx
  by_cases h : label = 1
  · apply gap_support hd hs
    simpa [leftProfile,h] using hx
  · apply upper_support hd hs
    simpa [leftProfile,h] using hx

theorem rightProfile_support {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (label : Fin 3) : Function.support (rightProfile delta label) ⊆ Icc (1/2 : ℝ) (5/2) := by
  intro x hx
  by_cases h : label = 2
  · apply gap_support hd hs
    simpa [rightProfile,h] using hx
  · apply upper_support hd hs
    simpa [rightProfile,h] using hx

theorem upperCost_le_gapCost : upperCost ≤ gapCost := by
  have h := D_nonneg
  unfold upperCost gapCost
  linarith

theorem leftProfile_N2 {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) (label : Fin 3) :
    N2 (leftProfile delta label) ≤ gapCost/delta^2 := by
  by_cases h : label = 1
  · simpa [leftProfile,h] using gap_N2 hd hs
  · have hc := div_le_div_of_nonneg_right upperCost_le_gapCost (sq_nonneg delta)
    simpa [leftProfile,h] using (upper_N2 hd hs).trans hc

theorem rightProfile_N2 {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) (label : Fin 3) :
    N2 (rightProfile delta label) ≤ gapCost/delta^2 := by
  by_cases h : label = 2
  · simpa [rightProfile,h] using gap_N2 hd hs
  · have hc := div_le_div_of_nonneg_right upperCost_le_gapCost (sq_nonneg delta)
    simpa [rightProfile,h] using (upper_N2 hd hs).trans hc

private theorem N2_nonneg (f : ℝ → ℂ) : 0 ≤ N2 f :=
  add_nonneg (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))
    (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))

/-- Label 0 is upper, label 1 is left gap, label 2 is right gap.
All Brun divisors change only m and the two scales U/d1,V/d2. -/
def actualSmoothCore (delta : ℝ) (label : Fin 3) (alpha : ℂ)
    (U V : ℝ) (m d₁ d₂ a q : ℕ) : ℂ :=
  fixedMCore (wideWindow (U/d₁)) (wideWindow (V/d₂)) (m*d₁*d₂) a q
    alpha (leftProfile delta label) (rightProfile delta label) (U/d₁) (V/d₂)

/-- Conditional actual-profile application of the UNSUPPLIED INTERNAL P2
interface. The independently constructed profiles remove profile-shape/N2
obligations only; the internal P2 derivation remains required. -/
theorem actualSmoothCore_le {constant delta U V : ℝ}
    (hconstant : 0 ≤ constant) (hP2 : FixedMP2 constant)
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (label : Fin 3) (alpha : ℂ) (m a q d₁ d₂ : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ‖actualSmoothCore delta label alpha U V m d₁ d₂ a q‖ ≤
      (constant * gapCost^2 / delta^4) * ‖alpha‖ * modulusBudget q := by
  have hC := gapCost_nonneg
  have hD₁ : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hD₂ : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hBudget := modulusBudget_nonneg q
  have hNleft := N2_nonneg (leftProfile delta label)
  have hNright := N2_nonneg (rightProfile delta label)
  have hp := hP2 (leftProfile delta label) (rightProfile delta label)
    (leftProfile_C2 delta label) (rightProfile_C2 delta label)
    (leftProfile_support hd hs label) (rightProfile_support hd hs label)
    (U/d₁) (V/d₂) (div_pos hU hD₁) (div_pos hV hD₂)
    (m*d₁*d₂) a q hq ha alpha
  calc
    _ ≤ constant * ‖alpha‖ * N2 (leftProfile delta label) *
        N2 (rightProfile delta label) * modulusBudget q := hp
    _ ≤ constant * ‖alpha‖ * (gapCost/delta^2) *
        (gapCost/delta^2) * modulusBudget q := by
      gcongr
      · exact leftProfile_N2 hd hs label
      · exact rightProfile_N2 hd hs label
    _ = _ := by field_simp [hd.ne']; ring

/-- Conditional finite E4-type inequality for the actual normalized
smooth cores, assuming the still-unsupplied INTERNAL P2 interface.
This is not a proof of original P2/E4. Complex amplitudes, Brun weights and
signed rho are fixed before q, with the same rho in count and exact mean. -/
theorem finite_threeBrun_sameRho_E4 {constant delta U V : ℝ}
    (hconstant : 0 ≤ constant) (hP2 : FixedMP2 constant)
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (label : Fin 3) (m a : ℕ) (Q : Finset ℕ) (R : Finset (ℕ×ℕ))
    (rho : ℕ → ℂ) (alpha c : (ℕ×ℕ) → ℂ)
    (hQ : ∀ q ∈ Q, 0 < q ∧ Nat.Coprime a q)
    (hR : ∀ d ∈ R, 0 < d.1 ∧ 0 < d.2) :
    ‖∑ q ∈ Q, rho q * ∑ d ∈ R, c d *
      actualSmoothCore delta label (alpha d) U V m d.1 d.2 a q‖ ≤
      (constant * gapCost^2 / delta^4) *
        (∑ d ∈ R, ‖c d‖ * ‖alpha d‖) *
        (∑ q ∈ Q, ‖rho q‖ * modulusBudget q) := by
  let F : ℝ := constant * gapCost^2 / delta^4
  have hF : 0 ≤ F := by unfold F; positivity
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ d ∈ R,
        c d * actualSmoothCore delta label (alpha d) U V m d.1 d.2 a q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ∑ d ∈ R,
        ‖c d‖ * ‖actualSmoothCore delta label (alpha d) U V m d.1 d.2 a q‖ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ∑ d ∈ R,
        ‖c d‖ * (F * ‖alpha d‖ * modulusBudget q) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro d hdr
      exact mul_le_mul_of_nonneg_left
        (actualSmoothCore_le hconstant hP2 hd hs hU hV label (alpha d) m a q d.1 d.2
          (hQ q hq).1 (hQ q hq).2 (hR d hdr).1 (hR d hdr).2) (norm_nonneg _)
    _ = ∑ q ∈ Q, (F * ∑ d ∈ R, ‖c d‖ * ‖alpha d‖) *
        (‖rho q‖ * modulusBudget q) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hdr
      ring
    _ = _ := by rw [Finset.mul_sum]

end
end ImbalancedChen.Part3.TwoLongActualThreeBrunP2Receiver
