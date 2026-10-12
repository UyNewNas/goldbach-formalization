import ImbalancedChen.FrozenRosserPolicy
import ImbalancedChen.RosserShortPrefixAdmissibility

/-!
# Literal fourth continuations and fifth own-cube density terms

The inherited first and third cubes are checked at the current level.
The fifth admission indicator is retained, so a restored old-rejected
branch is not lost. Accepted branches have the actual lower density at
the real quotient `Q / P`, with cutoff the fifth prime.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

private theorem four_sorted (p1 p2 p3 p4 : ℕ)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    [p4, p3, p2, p1].Pairwise (· < ·) := by
  simp [List.pairwise_cons]
  omega

private theorem five_sorted (p1 p2 p3 p4 p5 : ℕ)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    [p5, p4, p3, p2, p1].Pairwise (· < ·) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_, four_sorted p1 p2 p3 p4 h43 h32 h21⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

private theorem positive_prod_of_le_head (pre : List ℕ) (q : ℕ)
    (hq : 0 < q) (hle : ∀ p ∈ pre, q ≤ p) : (0 : ℝ) < pre.prod := by
  have hn : 0 < pre.prod := List.prod_pos (fun p hp => hq.trans_le (hle p hp))
  exact_mod_cast hn

/-- The fourth upper continuation has positive sign and an upper residual.
Its total-product cutoff is discharged by the earlier third cube. -/
theorem frozen_upper_four_actualDensity (Q : List ℕ → ℝ) (N cap : ℕ)
    (p1 p2 p3 p4 : ℕ) (h4 : 0 < p4)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hfirst : (p1 : ℝ) ^ 3 < Q [p4, p3, p2, p1])
    (hthird : (p1 : ℝ) * p2 * p3 ^ 3 < Q [p4, p3, p2, p1]) (mass : ℝ) :
    firstExitRetainedPolynomial (frozenParityRosserPolicy false 4 Q)
        (fun p => 1 / ((p : ℝ) - 1)) [p4, p3, p2, p1] true mass
        (roughPrimeUniverse N cap 0 p4) =
      mass * actualSmallRosserPlusDensity N cap p4
        (Q [p4, p3, p2, p1] / ([p4, p3, p2, p1].prod : ℝ)) := by
  have hle : ∀ p ∈ [p4, p3, p2, p1], p4 ≤ p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  have hadm := (ordinaryRosserPrefixAdmissible_upper_four_iff
    (Q [p4, p3, p2, p1]) p1 p2 p3 p4 h4 h43 h32 h21).mpr ⟨hfirst, hthird⟩
  have hh := firstExitRetainedPolynomial_frozenParityRosser_actualDensity
    false 4 Q N cap p4 [p4, p3, p2, p1] rfl (by omega) hadm
    (four_sorted p1 p2 p3 p4 h43 h32 h21)
    (positive_prod_of_le_head _ p4 h4 hle)
    (fun p hp => by exact_mod_cast hle p hp) true mass rfl
  simpa only [ordinaryRosserResidualLower, show Even (4 : ℕ) from ⟨2, rfl⟩,
    if_true, Bool.false_eq_true, if_false, signedTreeCoefficient_true] using hh

/-- Once the inherited tests hold, the actual fifth policy checks precisely
the fifth own cube. This is an equivalence, including the rejected case. -/
theorem frozen_upper_five_admitted_iff (Q : List ℕ → ℝ)
    (p1 p2 p3 p4 p5 : ℕ) (h5 : 0 < p5)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hfirst : (p1 : ℝ) ^ 3 < Q [p5, p4, p3, p2, p1])
    (hthird : (p1 : ℝ) * p2 * p3 ^ 3 < Q [p5, p4, p3, p2, p1]) :
    frozenParityRosserPolicy false 5 Q false [p5, p4, p3, p2, p1] = true ↔
      (([p5, p4, p3, p2, p1].prod : ℕ) : ℝ) * p5 ^ 2 < Q [p5, p4, p3, p2, p1] := by
  change decide (ordinaryRosserPrefixAdmissible false (Q [p5, p4, p3, p2, p1])
    [p5, p4, p3, p2, p1]) = true ↔ _
  rw [decide_eq_true_eq]
  rw [ordinaryRosserPrefixAdmissible_upper_five_iff _ p1 p2 p3 p4 p5 h5 h54 h43 h32 h21]
  exact and_iff_right hfirst |>.trans (and_iff_right hthird)

/-- Accepted fifth branches have the negative lower residual density;
rejected branches contribute exactly zero before any asymptotic estimate. -/
theorem frozen_upper_five_ownCube_actualDensity (Q : List ℕ → ℝ) (N cap : ℕ)
    (p1 p2 p3 p4 p5 : ℕ) (h5 : 0 < p5)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hfirst : (p1 : ℝ) ^ 3 < Q [p5, p4, p3, p2, p1])
    (hthird : (p1 : ℝ) * p2 * p3 ^ 3 < Q [p5, p4, p3, p2, p1]) (mass : ℝ) :
    (if frozenParityRosserPolicy false 5 Q false [p5, p4, p3, p2, p1] = true then
      firstExitRetainedPolynomial (frozenParityRosserPolicy false 5 Q)
        (fun p => 1 / ((p : ℝ) - 1)) [p5, p4, p3, p2, p1] false mass
        (roughPrimeUniverse N cap 0 p5) else 0) =
      if (([p5, p4, p3, p2, p1].prod : ℕ) : ℝ) * p5 ^ 2 < Q [p5, p4, p3, p2, p1] then
        -mass * actualSmallRosserMinusDensity N cap p5
          (Q [p5, p4, p3, p2, p1] / ([p5, p4, p3, p2, p1].prod : ℝ)) else 0 := by
  simp only [frozen_upper_five_admitted_iff Q p1 p2 p3 p4 p5 h5 h54 h43 h32 h21 hfirst hthird]
  split_ifs with hcube
  · have hle : ∀ p ∈ [p5, p4, p3, p2, p1], p5 ≤ p := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
    have hadm := (ordinaryRosserPrefixAdmissible_upper_five_iff
      (Q [p5, p4, p3, p2, p1]) p1 p2 p3 p4 p5 h5 h54 h43 h32 h21).mpr
      ⟨hfirst, hthird, hcube⟩
    have hh := firstExitRetainedPolynomial_frozenParityRosser_actualDensity
      false 5 Q N cap p5 [p5, p4, p3, p2, p1] rfl (by omega) hadm
      (five_sorted p1 p2 p3 p4 p5 h54 h43 h32 h21)
      (positive_prod_of_le_head _ p5 h5 hle)
      (fun p hp => by exact_mod_cast hle p hp) false mass rfl
    simpa only [ordinaryRosserResidualLower, show ¬Even (5 : ℕ) by decide,
      if_false, Bool.not_false, if_true, signedTreeCoefficient_false] using hh
  · rfl

/-- The same literal policy acceptance supplies the strict analytic-domain
gate `Q/P > p5^2`; no assertion about a lower density outside it is made. -/
theorem frozen_upper_five_admitted_residual_gt_sq (Q : List ℕ → ℝ)
    (p1 p2 p3 p4 p5 : ℕ) (h5 : 0 < p5)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hadm : frozenParityRosserPolicy false 5 Q false [p5, p4, p3, p2, p1] = true) :
    (p5 : ℝ) ^ 2 < Q [p5, p4, p3, p2, p1] / ([p5, p4, p3, p2, p1].prod : ℝ) := by
  have hfull : ordinaryRosserPrefixAdmissible false
      (Q [p5, p4, p3, p2, p1]) [p5, p4, p3, p2, p1] := by
    exact of_decide_eq_true hadm
  exact ordinaryRosserPrefixAdmissible_upper_five_residual_gt_sq
    _ p1 p2 p3 p4 p5 h5 h54 h43 h32 h21 hfull

/-- The lower fourth policy's active test is its own cube, once the
inherited second cube has been checked at the current frozen level. -/
theorem frozen_lower_four_admitted_iff (Q : List ℕ → ℝ)
    (p1 p2 p3 p4 : ℕ) (h4 : 0 < p4)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hsecond : (p1 : ℝ) * p2 ^ 3 < Q [p4, p3, p2, p1]) :
    frozenParityRosserPolicy true 4 Q true [p4, p3, p2, p1] = true ↔
      (([p4, p3, p2, p1].prod : ℕ) : ℝ) * p4 ^ 2 < Q [p4, p3, p2, p1] := by
  change decide (ordinaryRosserPrefixAdmissible true (Q [p4, p3, p2, p1])
    [p4, p3, p2, p1]) = true ↔ _
  rw [decide_eq_true_eq,
    ordinaryRosserPrefixAdmissible_lower_four_iff _ p1 p2 p3 p4 h4 h43 h32 h21]
  exact and_iff_right hsecond

/-- Lower fourth restoration has positive sign and retains its own gate;
it is not the sign or the cutoff of the upper fifth restoration. -/
theorem frozen_lower_four_ownCube_actualDensity (Q : List ℕ → ℝ) (N cap : ℕ)
    (p1 p2 p3 p4 : ℕ) (h4 : 0 < p4)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hsecond : (p1 : ℝ) * p2 ^ 3 < Q [p4, p3, p2, p1]) (mass : ℝ) :
    (if frozenParityRosserPolicy true 4 Q true [p4, p3, p2, p1] = true then
      firstExitRetainedPolynomial (frozenParityRosserPolicy true 4 Q)
        (fun p => 1 / ((p : ℝ) - 1)) [p4, p3, p2, p1] true mass
        (roughPrimeUniverse N cap 0 p4) else 0) =
      if (([p4, p3, p2, p1].prod : ℕ) : ℝ) * p4 ^ 2 < Q [p4, p3, p2, p1] then
        mass * actualSmallRosserMinusDensity N cap p4
          (Q [p4, p3, p2, p1] / ([p4, p3, p2, p1].prod : ℝ)) else 0 := by
  simp only [frozen_lower_four_admitted_iff Q p1 p2 p3 p4 h4 h43 h32 h21 hsecond]
  split_ifs with hcube
  · have hle : ∀ p ∈ [p4, p3, p2, p1], p4 ≤ p := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
    have hadm := (ordinaryRosserPrefixAdmissible_lower_four_iff
      (Q [p4, p3, p2, p1]) p1 p2 p3 p4 h4 h43 h32 h21).mpr ⟨hsecond, hcube⟩
    have hh := firstExitRetainedPolynomial_frozenParityRosser_actualDensity
      true 4 Q N cap p4 [p4, p3, p2, p1] rfl (by omega) hadm
      (four_sorted p1 p2 p3 p4 h43 h32 h21)
      (positive_prod_of_le_head _ p4 h4 hle)
      (fun p hp => by exact_mod_cast hle p hp) true mass rfl
    simpa only [ordinaryRosserResidualLower, show Even (4 : ℕ) from ⟨2, rfl⟩,
      if_true, signedTreeCoefficient_true] using hh
  · rfl

end

end ImbalancedChen
