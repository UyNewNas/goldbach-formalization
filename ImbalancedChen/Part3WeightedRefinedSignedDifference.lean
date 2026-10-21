import ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weighted energy on genuine refinements of the signed-difference source

Each original source index has one label. A refinement is taken inside a
subset of the existing source carrier, with its original positive f,
signed frequencies, nonzero difference and output map. The label type need
not be finite: only the finite image of the source subset is summed.

This is a coefficient energy estimate. No embedding of the actual packet
carrier, separation of its c dependence, or spectral estimate is asserted.
-/

namespace ImbalancedChen.Part3.WeightedRefinedSignedDifference

noncomputable section

open Classical Finset LichtmanSignedDifferenceMultiplicity
open scoped BigOperators

abbrev Source := (ℕ × ℕ × ℕ) × (ℤ × ℤ)

variable {R : Type*} [DecidableEq R]

def refinedFiber (U : Finset Source) (ell : Source → R)
    (r : R) (zy : ℕ × ℤ) : Finset Source :=
  U.filter (fun t => ell t = r ∧ output t = zy)

def refinedCoefficient (U : Finset Source) (ell : Source → R)
    (w : Source → ℂ) (r : R) (zy : ℕ × ℤ) : ℂ :=
  ∑ t ∈ refinedFiber U ell r zy, w t

def refinedL2 (S H F : ℝ) (nu : ℕ) (U : Finset Source)
    (ell : Source → R) (w : Source → ℂ) : ℝ :=
  ∑ r ∈ U.image ell, ∑ zy ∈ (sourceCarrier S H F).image output,
    if (nu : ℤ) ∣ zy.2 then ‖refinedCoefficient U ell w r zy‖ ^ 2 else 0

private theorem norm_refinedCoefficient_le (U : Finset Source)
    (ell : Source → R) (w : Source → ℂ) (M : ℝ)
    (hw : ∀ t ∈ U, ‖w t‖ ≤ M) (r : R) (zy : ℕ × ℤ) :
    ‖refinedCoefficient U ell w r zy‖ ≤
      M * ((refinedFiber U ell r zy).card : ℝ) := by
  unfold refinedCoefficient
  calc
    _ ≤ ∑ t ∈ refinedFiber U ell r zy, ‖w t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ refinedFiber U ell r zy, M := by
      apply Finset.sum_le_sum
      intro t ht
      exact hw t (Finset.mem_filter.mp ht).1
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

private theorem sum_refinedFiber_card (U : Finset Source)
    (ell : Source → R) (zy : ℕ × ℤ) :
    (∑ r ∈ U.image ell, (refinedFiber U ell r zy).card) =
      (U.filter (fun t => output t = zy)).card := by
  have hmap : Set.MapsTo ell
      (U.filter (fun t => output t = zy)) (U.image ell) := by
    intro t ht
    exact Finset.mem_image_of_mem ell (Finset.mem_filter.mp ht).1
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := ell) (s := U.filter (fun t => output t = zy)) (t := U.image ell) hmap
  have hfiber (r : R) :
      ((U.filter (fun t => output t = zy)).filter (fun t => ell t = r)) =
        refinedFiber U ell r zy := by
    ext t
    simp only [refinedFiber, Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  simpa only [hfiber] using hcard.symm

private theorem output_energy_le (S H F : ℝ) (U : Finset Source)
    (hU : U ⊆ sourceCarrier S H F) (ell : Source → R)
    (w : Source → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ t ∈ U, ‖w t‖ ≤ M) (zy : ℕ × ℤ) :
    (∑ r ∈ U.image ell, ‖refinedCoefficient U ell w r zy‖ ^ 2) ≤
      M ^ 2 * (multiplicity S H F zy.1 zy.2 : ℝ) ^ 2 := by
  have hcard :
      (∑ r ∈ U.image ell, (refinedFiber U ell r zy).card) ≤
        multiplicity S H F zy.1 zy.2 := by
    rw [sum_refinedFiber_card U ell zy]
    unfold multiplicity
    apply Finset.card_le_card
    intro t ht
    exact Finset.mem_filter.mpr
      ⟨hU (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩
  have hsum :
      (∑ r ∈ U.image ell, ((refinedFiber U ell r zy).card : ℝ)) ≤
        (multiplicity S H F zy.1 zy.2 : ℝ) := by
    exact_mod_cast hcard
  have hsum0 : 0 ≤ ∑ r ∈ U.image ell,
      ((refinedFiber U ell r zy).card : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  calc
    _ ≤ ∑ r ∈ U.image ell, (M * ((refinedFiber U ell r zy).card : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _hr
      have hn := norm_refinedCoefficient_le U ell w M hw r zy
      have hright : 0 ≤ M * ((refinedFiber U ell r zy).card : ℝ) :=
        mul_nonneg hM (Nat.cast_nonneg _)
      simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg _) hright
    _ = M ^ 2 * ∑ r ∈ U.image ell,
        ((refinedFiber U ell r zy).card : ℝ) ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ M ^ 2 * (∑ r ∈ U.image ell,
        ((refinedFiber U ell r zy).card : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _))
        (sq_nonneg M)
    _ ≤ M ^ 2 * (multiplicity S H F zy.1 zy.2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) (sq_nonneg M)

private theorem refinedL2_nonneg (S H F : ℝ) (nu : ℕ)
    (U : Finset Source) (ell : Source → R) (w : Source → ℂ) :
    0 ≤ refinedL2 S H F nu U ell w := by
  unfold refinedL2
  apply Finset.sum_nonneg
  intro r _hr
  apply Finset.sum_nonneg
  intro zy _hzy
  by_cases hd : (nu : ℤ) ∣ zy.2
  · simpa only [if_pos hd] using sq_nonneg ‖refinedCoefficient U ell w r zy‖
  · simp only [if_neg hd, le_refl]

private theorem refinedL2_le_multiplicityL2 (S H F : ℝ) (nu : ℕ)
    (U : Finset Source) (hU : U ⊆ sourceCarrier S H F)
    (ell : Source → R) (w : Source → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ t ∈ U, ‖w t‖ ≤ M) :
    refinedL2 S H F nu U ell w ≤ M ^ 2 * multiplicityL2 S H F nu := by
  unfold refinedL2 multiplicityL2
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro zy _hzy
  by_cases hd : (nu : ℤ) ∣ zy.2
  · simp only [if_pos hd]
    exact output_energy_le S H F U hU ell w M hM hw zy
  · simp only [if_neg hd, Finset.sum_const_zero, mul_zero, le_refl]

/-- Any genuine finite labeling of a subset of the original signed source
has the original explicit 576 energy budget and the original true endpoint.
The label image is a partition of the source indices, not a replication
over an additional external residue parameter. -/
theorem weighted_refined_signedDifference_L2
    (S H F : ℝ) (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F)
    (nu : ℕ) (hnu : 0 < nu)
    (U : Finset Source) (hU : U ⊆ sourceCarrier S H F)
    (ell : Source → R) (w : Source → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hw : ∀ t ∈ U, ‖w t‖ ≤ M) :
    refinedL2 S H F nu U ell w ≤
      M ^ 2 * 576 * (divisorMaximum S H F : ℝ) ^ 5 *
        (harmonic (Nat.floor (2 * S)) : ℝ) *
          (1 + H / S) * (H * S) ^ 2 * F / (nu : ℝ) ∧
      (8 * F * H * S ≤ (nu : ℝ) → refinedL2 S H F nu U ell w = 0) := by
  have hbase := signedDifference_multiplicityL2_bound S H F hS hH hF nu hnu
  have hdom := refinedL2_le_multiplicityL2 S H F nu U hU ell w M hM hw
  constructor
  · calc
      _ ≤ M ^ 2 * multiplicityL2 S H F nu := hdom
      _ ≤ M ^ 2 * (576 * (divisorMaximum S H F : ℝ) ^ 5 *
          (harmonic (Nat.floor (2 * S)) : ℝ) *
            (1 + H / S) * (H * S) ^ 2 * F / (nu : ℝ)) :=
        mul_le_mul_of_nonneg_left hbase.1 (sq_nonneg M)
      _ = _ := by ring
  · intro hlarge
    apply le_antisymm
    · calc
        _ ≤ M ^ 2 * multiplicityL2 S H F nu := hdom
        _ = 0 := by rw [hbase.2 hlarge, mul_zero]
    · exact refinedL2_nonneg S H F nu U ell w

end

end ImbalancedChen.Part3.WeightedRefinedSignedDifference
