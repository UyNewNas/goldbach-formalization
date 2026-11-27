import ImbalancedChen.Part3ActualHardTailLabelBudget
import ImbalancedChen.Part3ActualLabelBudgetCardinality
import ImbalancedChen.Part3ActualModeCoefficientNormsCore
import ImbalancedChen.Part3ActualSmoothMassTruncation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual mode coefficients in the common six-piece tail

This finite consumer uses the original actualModeLambda/Omega definitions and
their recovered norm theorems. The accepted six-piece common hard tail is
composed with the original ordered-label budget after removing the y=0 source.
No coefficient norm hypothesis is added to either public six-piece theorem.

The substitution R=x^epsilon/10 produces exactly the original cutoff formula
ceil((C/B)*x^epsilon). Its explicit power of x is valid for every epsilon when
x>0. The analytic constant is chosen before all scales, atoms and modes.

B and C remain explicit positive scales. The results retain the original label
budget or its explicit finite cardinality bound, including closed endpoints.
They make no uniform family claim about that budget, Z, outer mode sums,
the original signed error or spectral J/A.
-/

namespace ImbalancedChen.Part3.ActualModeSmoothMassTail20261127

noncomputable section
open Classical Finset CommonSmoothCutoff
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualCompletedHardTailMass20261026b
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualModeBetaPositiveCountSourceOnly
open ActualModeCommonPoissonLanes20261126 ActualSmoothMassTruncation20261127

/-- Both coefficient norm inputs come from their original actual-mode suppliers. -/
theorem actualMode_sourceAbsMass_le_rawLabelBudget
    {b : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible b sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g * l)] (Z : ℝ)
    (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)) :
    sourceAbsMass (nonzeroSource (actualSource e D delta g l Z negative))
      (actualModeLambda e D delta g l mode negative u k)
      (actualModeOmega e D g l Z tag mode negative k) ≤
        rawLabelBudget (baseCarrier e (D / delta))
          (e.sharedSmoothFrequencyBound Z D) (scaleF e D g) := by
  apply (sourceAbsMass_nonzero_le (actualSource e D delta g l Z negative)
    (actualModeLambda e D delta g l mode negative u k)
    (actualModeOmega e D g l Z tag mode negative k)).trans
  unfold actualSource
  apply sourceAbsMass_le_rawLabelBudget
  · intro t ht
    exact actualModeLambda_norm_le he D delta g l mode negative u k ht
  · intro h _hh
    exact actualModeOmega_norm_le e D g l Z tag mode negative k h

/-- The same hard cutoff controls all six pieces for the original mode coefficients.
The only sixfold loss is the already proved finite triangle inequality. -/
theorem actualMode_sixSmoothMass_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ B : ℝ, 0 < B → ∀ C : ℝ, 0 < C →
      ∀ R : ℝ, 0 < R →
      ∀ (b : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
        MediumAdmissible b sigma kappa c0 e →
      ∀ (D delta g l : ℕ) [NeZero (g * l)] (Z : ℝ)
        (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)),
        let lam := actualModeLambda e D delta g l mode negative u k
        let om := actualModeOmega e D g l Z tag mode negative k
        ‖(sixSmoothMass B C (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue negative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lam om) : ℂ) -
          actualTruncatedSix e D delta g l Z negative lam om
            (Nat.ceil (10 * C * R / B)) B C‖ ≤
          (6 * A * C ^ 2 / R ^ (r - 1)) *
            rawLabelBudget (baseCarrier e (D / delta))
              (e.sharedSmoothFrequencyBound Z D) (scaleF e D g) := by
  obtain ⟨A, hA, htail⟩ := actual_sixSmoothMass_common_hard_tail r hr
  refine ⟨A, hA, ?_⟩
  intro B hB C hC R hR b sigma kappa c0 e he D delta g l inst Z tag mode negative u k
  let : NeZero (g * l) := inst
  dsimp only
  apply (htail B hB C hC R hR e D delta g l Z negative
    (actualModeLambda e D delta g l mode negative u k)
    (actualModeOmega e D g l Z tag mode negative k)).trans
  exact mul_le_mul_of_nonneg_left
    (actualMode_sourceAbsMass_le_rawLabelBudget he D delta g l Z tag mode negative u k)
    (by positivity)

/-- The physical threshold gives the literal original integer cutoff formula. -/
theorem common_cutoff_xepsilon (B C x epsilon : ℝ) :
    Nat.ceil (10 * C * (x ^ epsilon / 10) / B) =
      Nat.ceil ((C / B) * x ^ epsilon) := by
  congr 1
  ring

/-- Exact substitution only: the complete label budget remains explicit.
No positivity of epsilon is needed until a subsequent decay argument. -/
theorem actualMode_sixSmoothMass_common_hard_tail_xepsilon (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ B : ℝ, 0 < B → ∀ C : ℝ, 0 < C →
      ∀ x : ℝ, 0 < x → ∀ epsilon : ℝ,
      ∀ (b : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
        MediumAdmissible b sigma kappa c0 e →
      ∀ (D delta g l : ℕ) [NeZero (g * l)] (Z : ℝ)
        (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)),
        let lam := actualModeLambda e D delta g l mode negative u k
        let om := actualModeOmega e D g l Z tag mode negative k
        ‖(sixSmoothMass B C (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue negative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lam om) : ℂ) -
          actualTruncatedSix e D delta g l Z negative lam om
            (Nat.ceil ((C / B) * x ^ epsilon)) B C‖ ≤
          (6 * A * 10 ^ (r - 1) * C ^ 2) *
            rawLabelBudget (baseCarrier e (D / delta))
              (e.sharedSmoothFrequencyBound Z D) (scaleF e D g) *
            x ^ (-(epsilon * ((r - 1 : ℕ) : ℝ))) := by
  obtain ⟨A, hA, htail⟩ := actualMode_sixSmoothMass_common_hard_tail r hr
  refine ⟨A, hA, ?_⟩
  intro B hB C hC x hx epsilon b sigma kappa c0 e he D delta g l inst Z tag mode negative u k
  let : NeZero (g * l) := inst
  have hR : 0 < x ^ epsilon / 10 :=
    div_pos (Real.rpow_pos_of_pos hx epsilon) (by norm_num)
  have h := htail B hB C hC (x ^ epsilon / 10) hR
    b sigma kappa c0 e he D delta g l Z tag mode negative u k
  dsimp only at h ⊢
  rw [common_cutoff_xepsilon] at h
  calc
    _ ≤ (6 * A * C ^ 2 / (x ^ epsilon / 10) ^ (r - 1)) *
        rawLabelBudget (baseCarrier e (D / delta))
          (e.sharedSmoothFrequencyBound Z D) (scaleF e D g) := h
    _ = _ := by
      rw [div_pow, ← Real.rpow_mul_natCast hx.le, Real.rpow_neg hx.le]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

/-- The finite cardinality estimate replaces only the retained label budget.
The actual H and F parameters remain visible; this is not a family growth bound. -/
theorem actualMode_sixSmoothMass_common_hard_tail_xepsilon_cardinality
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ B : ℝ, 0 < B → ∀ C : ℝ, 0 < C →
      ∀ x : ℝ, 0 < x → ∀ epsilon : ℝ,
      ∀ (b : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
        MediumAdmissible b sigma kappa c0 e →
      ∀ (D delta g l : ℕ) [NeZero (g * l)] (Z : ℝ)
        (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)),
        let lam := actualModeLambda e D delta g l mode negative u k
        let om := actualModeOmega e D g l Z tag mode negative k
        ‖(sixSmoothMass B C (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue negative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lam om) : ℂ) -
          actualTruncatedSix e D delta g l Z negative lam om
            (Nat.ceil ((C / B) * x ^ epsilon)) B C‖ ≤
          (6 * A * 10 ^ (r - 1) * C ^ 2) *
            ((2 * scaleF e D g + 1) *
              ((e.Q2 + 1) * (2 * (e.sharedSmoothFrequencyBound Z D : ℝ))) ^ 2) *
            x ^ (-(epsilon * ((r - 1 : ℕ) : ℝ))) := by
  obtain ⟨A, hA, htail⟩ := actualMode_sixSmoothMass_common_hard_tail_xepsilon r hr
  refine ⟨A, hA, ?_⟩
  intro B hB C hC x hx epsilon b sigma kappa c0 e he D delta g l inst Z tag mode negative u k
  let : NeZero (g * l) := inst
  have h := htail B hB C hC x hx epsilon
    b sigma kappa c0 e he D delta g l Z tag mode negative u k
  dsimp only at h ⊢
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.rpow_pos_of_pos hx _))
  exact mul_le_mul_of_nonneg_left
    (ActualLabelBudgetCardinality20261127.actual_rawLabelBudget_le he D delta g Z)
    (by positivity)

end

end ImbalancedChen.Part3.ActualModeSmoothMassTail20261127
