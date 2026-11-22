import ImbalancedChen.P2WuProductInnerThetaPayment

/-!
Source only, uncompiled.

On the original Wu indexed families, the complete-product cap removes little
unsifted mass on the native boxTheta scale. The integer complement may be
zero. Fibres keep the original prime-slot multiplicity.

For a further weight between zero and one, the absolute error on the full
prime-tuple domain splits over the source and its complement. On the source,
the complete-product loss and the subsequent wall loss add exactly.
-/
namespace ImbalancedChen.P2WuProductInnerUnsiftedLoss

noncomputable section
open Classical Wu2008DoubleSieve
open scoped BigOperators
open P2NativeOmega3RankTupleReceiver P2WuProductInnerProfile P2WuProductInnerThetaPayment
open P5Z.ActualSingletonLogCollarFamily

/-- The exact difference of the two unsifted masses on this source. -/
def innerLoss {r N : ℕ} (B : ℕ) (S : Finset (Fin r → Fin (N+1))) : ℝ :=
  ∑ u ∈ S, 1 - innerWeight B N u

theorem innerLoss_eq_mass_sub {r N : ℕ} (B : ℕ) (S : Finset (Fin r → Fin (N+1))) :
    innerLoss B S = p5z_labelledMass S (fun _ => 1) -
      p5z_labelledMass S (innerWeight B N) := by
  unfold innerLoss p5z_labelledMass
  rw [Finset.sum_sub_distrib]

private theorem unsifted_integer_collar {r N : ℕ}
    (S : Finset (Fin r → Fin (N+1))) (hS : S ⊆ Part3.labelledPrimeTuples r N)
    (hcap : ∀ u ∈ S, Part3.labelledProduct u ≤ N) (z : ℕ) :
    (∑ u ∈ S, if N - Part3.labelledProduct u < z then (1 : ℝ) else 0) ≤
      (r^r : ℕ) * (z : ℝ) := by
  let F := (Finset.range (N+1)).filter (fun m => N-m < z)
  have hc : F.card ≤ z := by
    calc
      F.card ≤ (Finset.range z).card := by
        apply Finset.card_le_card_of_injOn (fun m : ℕ => N-m)
        · intro m hm
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
        · intro m hm n hn heq
          have hm' := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
          have hn' := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
          omega
      _ = z := Finset.card_range z
  have hpush := p5z_markedProductWeight_sum S (fun _ => 1) hcap
    (fun m => if N-m < z then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero, one_mul] at hpush
  rw [← hpush, ← Finset.sum_filter]
  change (∑ m ∈ F, p5z_markedProductWeight S (fun _ => 1) m) ≤ _
  calc
    _ ≤ ∑ _m ∈ F, ((r^r : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      simpa only [one_mul] using
        p5z_markedProductWeight_le S hS (fun _ => 1) 1 (by norm_num)
          (fun _ _ => le_rfl) m
    _ = ((r^r : ℕ) : ℝ) * (F.card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (Nat.cast_nonneg _)

/-- Unlike the prime-output collar, this includes every composite complement
and the zero complement at m=N with all of its original labels. -/
theorem finite_unsifted_inner_loss {r N : ℕ} (hN : 2 ≤ N) (B : ℕ)
    (S : Finset (Fin r → Fin (N+1))) (hS : S ⊆ Part3.labelledPrimeTuples r N)
    (hcap : ∀ u ∈ S, Part3.labelledProduct u ≤ N) :
    innerLoss B S ≤ (r^r : ℕ) * (Nat.ceil (logWidth B N * (N : ℝ)) : ℝ) := by
  let z := Nat.ceil (logWidth B N * (N : ℝ))
  apply le_trans ?_ (unsifted_integer_collar S hS hcap z)
  unfold innerLoss
  apply Finset.sum_le_sum
  intro u hu
  by_cases hnear : N - Part3.labelledProduct u < z
  · rw [if_pos hnear]
    linarith only [(innerWeight_bounds B N u).1]
  · have hfar : z ≤ N - Part3.labelledProduct u := Nat.le_of_not_gt hnear
    have hout : logWidth B N * (N : ℝ) ≤ ((N - Part3.labelledProduct u : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hfar)
    rw [Nat.cast_sub (hcap u hu)] at hout
    have hlin : ((Part3.labelledProduct u : ℕ) : ℝ) ≤ (N : ℝ) * (1-logWidth B N) := by
      nlinarith only [hout]
    have hm : 0 < Part3.labelledProduct u :=
      Finset.prod_pos (fun j _ => ((Finset.mem_filter.mp (hS hu)).2 j).pos)
    have hone := capReal_one_of_linear_bound (logWidth_bounds B hN).1
      (by omega : 0 < N) (by exact_mod_cast hm) hlin
    have hprofile : innerWeight B N u = 1 := by
      simpa only [innerWeight, innerProfile, productProfile, if_pos hN,
        ← Nat.cast_prod, Part3.labelledProduct] using hone
    simp only [hprofile, if_neg hnear, sub_self, le_refl]

/-- A single threshold for the entire unsifted labelled mass loss. -/
theorem uniform_indexed_unsifted_inner_loss (k R : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
        (∑ r ∈ Finset.range (R+1),
          innerLoss (collarExponent k) (indexedFamily k δ r N b)) ≤
          ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2) := by
  obtain ⟨T,hT4,hT⟩ := uniform_collar_scale k R hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN b hb
  have hN4 := hT4.trans hN
  have hrow (r : ℕ) := finite_unsifted_inner_loss (by omega : 2 ≤ N)
    (collarExponent k) (indexedFamily k δ r N b) (indexedFamily_prime k δ r N b)
    (by
      simp only [indexedFamily, if_pos hb]
      exact family_product_cap (fun j p hp => (mem_convolutionWuWindows.mp hp).1))
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range (R+1)) => hrow r)
  have hcost :
      (∑ r ∈ Finset.range (R+1),
        (r^r : ℕ) * (Nat.ceil (logWidth (collarExponent k) N * (N : ℝ)) : ℝ)) =
      (rankMultiplicity R : ℝ) * (Nat.ceil (logWidth (collarExponent k) N * (N : ℝ)) : ℝ) := by
    rw [← Finset.sum_mul]
    simp only [rankMultiplicity, Nat.cast_sum, Nat.cast_pow]
  rw [hcost] at hsum
  exact hsum.trans (hT N hN b.1 b.2.1 b.2.2 hb)

/-- The two contributions from the remaining walls on the native prime grid. -/
def otherWallLoss {r N : ℕ} (B : ℕ) (S : Finset (Fin r → Fin (N+1)))
    (W : (Fin r → Fin (N+1)) → ℝ) : ℝ :=
  (∑ u ∈ Part3.labelledPrimeTuples r N \ S, innerWeight B N u * W u) +
  (∑ u ∈ S, innerWeight B N u * (1-W u))

/-- Exact error against the sharp indexed weight before any estimates. -/
theorem indexed_wall_error_eq (k B r N : ℕ) (δ : ℝ) (b : BoxIndex)
    (W : (Fin r → Fin (N+1)) → ℝ)
    (hW : ∀ u ∈ Part3.labelledPrimeTuples r N, 0 ≤ W u ∧ W u ≤ 1) :
    (∑ u ∈ Part3.labelledPrimeTuples r N,
      |innerWeight B N u * W u - indexedWeight k δ r N b u|) =
    otherWallLoss B (indexedFamily k δ r N b) W +
      innerLoss B (indexedFamily k δ r N b) := by
  let S := indexedFamily k δ r N b
  let U := Part3.labelledPrimeTuples r N
  let f := fun u => |innerWeight B N u * W u - indexedWeight k δ r N b u|
  have hsub : S ⊆ U := indexedFamily_prime k δ r N b
  have hsplit : (∑ u ∈ U \ S, f u) + (∑ u ∈ S, f u) = ∑ u ∈ U, f u :=
    Finset.sum_sdiff hsub
  have hout : (∑ u ∈ U \ S, f u) = ∑ u ∈ U \ S, innerWeight B N u * W u := by
    apply Finset.sum_congr rfl
    intro u hu
    obtain ⟨huU,huS⟩ := Finset.mem_sdiff.mp hu
    have hz : indexedWeight k δ r N b u = 0 := if_neg huS
    simpa only [f, hz, sub_zero] using
      abs_of_nonneg (mul_nonneg (innerWeight_bounds B N u).1 (hW u huU).1)
  have hin : (∑ u ∈ S, f u) =
      (∑ u ∈ S, innerWeight B N u * (1-W u)) + (∑ u ∈ S, 1-innerWeight B N u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hone : indexedWeight k δ r N b u = 1 := if_pos hu
    have hc := innerWeight_bounds B N u
    have hmul : innerWeight B N u * W u ≤ 1 :=
      (mul_le_mul_of_nonneg_left (hW u (hsub hu)).2 hc.1).trans (by simpa using hc.2)
    simp only [f, hone, abs_of_nonpos (sub_nonpos.mpr hmul)]
    ring
  change (∑ u ∈ U, f u) = _
  rw [← hsplit, hout, hin]
  exact (add_assoc _ _ _).symm

/-- A common threshold pays the complete-product term even when the other
wall weights depend on the rank and on every moving box parameter. -/
theorem uniform_indexed_wall_error (k R : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      ∀ W : (r : ℕ) → (Fin r → Fin (N+1)) → ℝ,
      (∀ r ∈ Finset.range (R+1), ∀ u ∈ Part3.labelledPrimeTuples r N,
        0 ≤ W r u ∧ W r u ≤ 1) →
      (∑ r ∈ Finset.range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
        |innerWeight (collarExponent k) N u * W r u - indexedWeight k δ r N b u|) ≤
      (∑ r ∈ Finset.range (R+1),
        otherWallLoss (collarExponent k) (indexedFamily k δ r N b) (W r)) +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2) := by
  obtain ⟨T,hT4,hT⟩ := uniform_indexed_unsifted_inner_loss k R hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN b hb W hW
  calc
    _ = ∑ r ∈ Finset.range (R+1),
        (otherWallLoss (collarExponent k) (indexedFamily k δ r N b) (W r) +
          innerLoss (collarExponent k) (indexedFamily k δ r N b)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact indexed_wall_error_eq k (collarExponent k) r N δ b (W r) (hW r hr)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add_left (hT N hN b hb) _

end
end ImbalancedChen.P2WuProductInnerUnsiftedLoss
