import ImbalancedChen.P3OriginalU5FixedWidthSlabReserve
import ImbalancedChen.P2CanonicalWallFullResidualPayment

/-!
# One fixed width for finitely many arbitrary moving wall centers

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

The linear-coordinate representation, target-deleted prime slab envelope,
canonical prime prefix/tail factorization and complete residual Euler mass
are existing suppliers. This file only joins their exact interfaces.

The width and threshold precede every center, enumeration cap, policy and
rounding mesh. The complete residual sum is retained. No wall coverage,
rounding convergence, density, common physical Q or PP estimate is assumed
or concluded here.
-/

namespace ImbalancedChen.P3OriginalU5MovingWallPayment

noncomputable section
open scoped Classical BigOperators
open P1ActualMovingAffineWallMass P1ActualMovingAffineSlab
open P3OriginalU5FixedWidthSlabReserve
open P2ActualResidualUniverseMass P2CanonicalWallFullResidualPayment

/-- The existing linear-coordinate representation transfers the fixed-width
envelope to any nonzero continuous linear form. -/
theorem exists_fixed_width_linear_center_reserve {d : ℕ}
    (a b : Fin d → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ center : ℝ,
        linearSlabMass N a b L center delta < eta := by
  cases d with
  | zero =>
      exfalso
      apply hL
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      change L x = 0
      rw [hx, map_zero]
  | succ d =>
      obtain ⟨j, hj⟩ := exists_nonzero_coordinate (linearCoefficients_ne_zero hL)
      obtain ⟨delta, hd, N0, hN0, hbound⟩ :=
        exists_fixed_width_uniform_center_reserve a b (linearCoefficients L)
          ha hab j hj eta heta
      refine ⟨delta, hd, N0, hN0, ?_⟩
      intro N hN center
      rw [linearSlabMass_eq]
      exact hbound N hN center

theorem linearSlabMass_mono_radius {d : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (c delta width : ℝ) (hwidth : delta ≤ width) :
    linearSlabMass N a b L c delta ≤ linearSlabMass N a b L c width := by
  unfold linearSlabMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hbox, hwall⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hbox, hwall.trans hwidth⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Finite union payment uses the exact same arithmetic tuple carrier and
weight. A tuple in several walls is safely counted several times. -/
theorem actual_wall_union_le_sum_slabs {d k : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin k → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    actualPrimeAffineWallStripMass N a b L c delta ≤
      ∑ i : Fin k, linearSlabMass N a b (L i) (c i) delta := by
  have hpoint (p : Fin d → ℕ) (hp : p ∈ actualPrimeBoxTuples N a b) :
      (if actualPrimeTupleLog N p ∈ primeAffineWallStrip L c delta then
        tupleWeight p else 0) ≤
      ∑ i : Fin k, if |L i (actualPrimeTupleLog N p) - c i| ≤ delta then
        tupleWeight p else 0 := by
    have hweight : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hp
    have hnonneg (i : Fin k) :
        0 ≤ (if |L i (actualPrimeTupleLog N p) - c i| ≤ delta then
          tupleWeight p else 0) := by
      split_ifs
      · exact hweight
      · exact le_rfl
    by_cases hwall : actualPrimeTupleLog N p ∈ primeAffineWallStrip L c delta
    · rw [if_pos hwall]
      obtain ⟨i, hi⟩ := hwall
      calc
        tupleWeight p = (if |L i (actualPrimeTupleLog N p) - c i| ≤ delta then
            tupleWeight p else 0) := (if_pos hi).symm
        _ ≤ _ := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    · rw [if_neg hwall]
      exact Finset.sum_nonneg (fun i _ => hnonneg i)
  calc
    actualPrimeAffineWallStripMass N a b L c delta =
        ∑ p ∈ actualPrimeBoxTuples N a b,
          if actualPrimeTupleLog N p ∈ primeAffineWallStrip L c delta then
            tupleWeight p else 0 := by
      rw [actualPrimeAffineWallStripMass, Finset.sum_filter]
      rfl
    _ ≤ ∑ p ∈ actualPrimeBoxTuples N a b,
        ∑ i : Fin k, if |L i (actualPrimeTupleLog N p) - c i| ≤ delta then
          tupleWeight p else 0 := Finset.sum_le_sum hpoint
    _ = ∑ i : Fin k, linearSlabMass N a b (L i) (c i) delta := by
      rw [Finset.sum_comm]
      simp only [linearSlabMass, Finset.sum_filter]

/-- The finite family may be empty. Every numerical wall center is chosen
after the same positive width and the same target threshold. -/
theorem exists_fixed_width_uniform_centers_reserve {d k : ℕ}
    (a b : Fin d → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : Fin k → (Fin d → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ c : Fin k → ℝ,
        actualPrimeAffineWallStripMass N a b L c delta < eta := by
  let eps : ℝ := eta / ((k : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have heach (i : Fin k) :=
    exists_fixed_width_linear_center_reserve a b ha hab (L i) (hL i) eps heps
  choose width hwidth threshold _hthreshold hsmall using heach
  let widths : Finset ℝ := insert 1 (Finset.univ.image width)
  have hne : widths.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let delta : ℝ := widths.min' hne
  have hdelta : 0 < delta := by
    have hm : delta ∈ widths := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]
      exact zero_lt_one
    · obtain ⟨i, _hi, heq⟩ := Finset.mem_image.mp h
      exact heq ▸ hwidth i
  have hle (i : Fin k) : delta ≤ width i := by
    exact Finset.min'_le widths (width i)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine ⟨delta, hdelta, max 2 (Finset.univ.sup threshold), le_max_left _ _, ?_⟩
  intro N hN c
  have hsum : (∑ i : Fin k, linearSlabMass N a b (L i) (c i) delta) ≤
      ∑ _i : Fin k, eps := by
    apply Finset.sum_le_sum
    intro i _hi
    have hiN : threshold i ≤ N :=
      (Finset.le_sup (f := threshold) (Finset.mem_univ i)).trans
        ((le_max_right _ _).trans hN)
    exact (linearSlabMass_mono_radius N a b (L i) (c i) delta (width i) (hle i)).trans
      (hsmall i N hiN (c i)).le
  have hreserve : (k : ℝ) * eps < eta := by
    dsimp only [eps]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show (0 : ℝ) < (k : ℝ) + 1 by positivity)).mpr
    nlinarith
  have hsum' : (∑ i : Fin k, linearSlabMass N a b (L i) (c i) delta) ≤
      (k : ℝ) * eps := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  exact (actual_wall_union_le_sum_slabs N a b L c delta).trans_lt (hsum'.trans_lt hreserve)

/-- Reserve, a fixed positive width, then a common threshold. All centers,
caps, policies and rounding meshes follow those choices, and the entire
residual modulus mass is paid using the existing canonical factorization. -/
theorem exists_uniform_centers_full_residual_wall_payment {j k : ℕ}
    (omega v : ℝ) (homega : 0 < omega) (hov : omega < v)
    (L : Fin k → (Fin j → ℝ) →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      ∀ (keep : List ℕ → Bool) (tau : ℝ) (c : Fin k → ℝ),
        wallRoundingCharge keep N cap omega v tau L c delta < eta := by
  obtain ⟨C, hC, Nm, hNm, hmass⟩ :=
    exists_eventual_uniform_mass_bound omega v homega hov
  obtain ⟨delta, hdelta, Ns, _hNs, hstrip⟩ :=
    exists_fixed_width_uniform_centers_reserve (fun _ => omega) (fun _ => v)
      (fun _ => homega) (fun _ => hov) L hL (eta / (2 * C)) (by positivity)
  refine ⟨delta, hdelta, max Nm Ns, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap keep tau c
  have hm := hmass N ((le_max_left _ _).trans hN) hEven cap
  have hs := hstrip N ((le_max_right _ _).trans hN) c
  have hS0 : 0 ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin j => omega) (fun _ => v) L c delta := by
    unfold actualPrimeAffineWallStripMass
    apply Finset.sum_nonneg
    intro p hp
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
  have hupper := mul_le_mul_of_nonneg_left hm hS0
  have hs' : actualPrimeAffineWallStripMass N (fun _ : Fin j => omega)
      (fun _ => v) L c delta * (2 * C) < eta :=
    (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hs
  have hb := wallRoundingCharge_le_two_mass keep N cap omega v tau L c delta
  nlinarith

end
end ImbalancedChen.P3OriginalU5MovingWallPayment
