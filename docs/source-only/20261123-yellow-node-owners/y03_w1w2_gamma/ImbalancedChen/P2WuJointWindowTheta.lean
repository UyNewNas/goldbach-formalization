import ImbalancedChen.P2WuJointWindowCarrier
import ImbalancedChen.P2WuOriginalWindowUpperTheta

/-!
The full prefix is opened before counting: several coordinates can leak
simultaneously. A finite union over the original slots and the two faces
pays these words on the original moving box's Theta scale. One threshold
works for all ranks up to R, all admissible boxes and every labelled word.
-/
namespace ImbalancedChen.P2WuJointWindowTheta

noncomputable section
open Finset Filter Wu2008DoubleSieve
open P2NativeOmega3RankTupleReceiver P2WuProductInnerProfile
open P2WuProductInnerThetaPayment P2WuProductInnerUnsiftedLoss
open P2WuJointWindowProfile P2WuJointWindowCarrier P2WuOriginalWindowUpperTheta
open P5Z.ActualSingletonLogCollarFamily
open scoped Classical BigOperators

/-- Both physical endpoints absorb the integer roundoff uniformly, even
when a particular moving window contains no prime. -/
theorem eventually_both_widths (k B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      ∀ j, 0 < lower b j ∧ 0 < b.2.2 j ∧
        1 ≤ lower b j * logWidth B N ∧ 1 ≤ b.2.2 j * logWidth B N := by
  let η := δ^(k+1)
  have hη : 0 < η := pow_pos hδ _
  filter_upwards [convolutionWuWindows_eventually_lower_cutoff hη,
    eventually_one_le_window_width B (half_pos hη), eventually_ge_atTop (2 : ℕ)]
    with N hcut hwidth hN
  intro b hb j
  have hV : (N : ℝ)^η ≤ b.2.2 j := hb.2.2.2.2.1 j
  have hL : (N : ℝ)^(η/2) ≤ lower b j := hcut b.2.1 hb.2.1 hb.2.2.1 (b.2.2 j) hV
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : 0 < (N : ℝ)^(η/2) := Real.rpow_pos_of_pos (by linarith only [hN1]) _
  have hV' : (N : ℝ)^(η/2) ≤ b.2.2 j :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hη] : η/2 ≤ η)).trans hV
  exact ⟨hp.trans_le hL, hp.trans_le hV', hwidth _ hL, hwidth _ hV'⟩

private theorem strip_payment {r N : ℕ} (S : Finset (Fin r → Fin (N+1)))
    (hS : S ⊆ Part3.labelledPrimeTuples r N) (l : Fin r) {a w : ℝ}
    (ha : 0 < a) (hw : 0 < w) (hround : 1 ≤ 2*(a*w))
    (hcap : ∀ u ∈ S, Part3.labelledProduct u ≤ N)
    (hstrip : ∀ u ∈ S, a ≤ physical u l ∧ physical u l ≤ a*(1+w)) :
    (S.card : ℝ) ≤ 3 * (((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) := by
  have hc := count_slot_strip S hS l ha hw.le hcap hstrip
  have hlin : (a*w+1)*((N : ℝ)/a) ≤ 3*(w*(N : ℝ)) := by
    calc
      _ ≤ (3*(a*w))*((N : ℝ)/a) := mul_le_mul_of_nonneg_right
        (by linarith only [hround]) (div_nonneg (Nat.cast_nonneg _) ha.le)
      _ = _ := by field_simp [ha.ne'] <;> ring
  calc
    (S.card : ℝ) ≤ ((r^r : ℕ) : ℝ) * ((a*w+1)*((N : ℝ)/a)) := hc
    _ ≤ ((r^r : ℕ) : ℝ) * (3 * (Nat.ceil (w*(N : ℝ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (hlin.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)))
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem finite_prefix_leakage {k r N B : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hw : 0 < w) (hw1 : w ≤ 1)
    (hends : ∀ j, 0 < lower b j ∧ 0 < b.2.2 j ∧
      1 ≤ lower b j * w ∧ 1 ≤ b.2.2 j * w) :
    (∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
      innerWeight B N u * jointWeight δ w r N b u) ≤
      (6*(k : ℝ)+1) * (((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) := by
  let A := Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b
  let F := A.filter (fun u => jointWeight δ w r N b u ≠ 0)
  let C := ((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcount : (∑ u ∈ A, innerWeight B N u * jointWeight δ w r N b u) ≤ (F.card : ℝ) := by
    calc
      _ ≤ ∑ u ∈ A, if jointWeight δ w r N b u ≠ 0 then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro u _
        by_cases hz : jointWeight δ w r N b u = 0
        · simp [hz]
        · rw [if_pos hz]
          calc
            _ ≤ innerWeight B N u * 1 := mul_le_mul_of_nonneg_left
              (jointWeight_bounds δ w r N b u).2 (innerWeight_bounds B N u).1
            _ ≤ 1 := by simpa only [mul_one] using (innerWeight_bounds B N u).2
      _ = _ := by rw [← sum_filter]; simp [F]
  have hbad (u) (hu : u ∈ F) :=
    native_outside_nonzero hb hw (fun j => (hends j).1) (fun j => (hends j).2.1)
      (mem_sdiff.mp (mem_filter.mp hu).1).2 (mem_filter.mp hu).2
  have hprime : F ⊆ Part3.labelledPrimeTuples r N := by
    intro u hu
    exact (mem_sdiff.mp (mem_filter.mp hu).1).1
  apply hcount.trans
  by_cases hr : b.1 ≤ r
  · let strip (j : Fin b.1) (a : ℝ) := F.filter (fun u =>
      a ≤ physical u (Fin.castLE hr j) ∧ physical u (Fin.castLE hr j) ≤ a*(1+w))
    let U (j : Fin b.1) := strip j (lowerBase (lower b j) w) ∪ strip j (b.2.2 j)
    have hsub : F ⊆ univ.biUnion U := by
      intro u hu
      obtain ⟨_, _, j, hj⟩ := hbad u hu
      refine mem_biUnion.mpr ⟨j, mem_univ _, ?_⟩
      rcases hj with hl | hh
      · apply mem_union_left
        apply mem_filter.mpr
        rw [lowerBase_mul hw]
        exact ⟨hu, hl.1.le, hl.2.le⟩
      · exact mem_union_right _ (mem_filter.mpr ⟨hu, hh.1, hh.2.le⟩)
    have hcard : (F.card : ℝ) ≤ ∑ j, ((U j).card : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    have hs (j : Fin b.1) (a : ℝ) (ha : 0 < a) (hround : 1 ≤ 2*(a*w)) :
        ((strip j a).card : ℝ) ≤ 3*C :=
      strip_payment (strip j a) (fun _ hu => hprime (mem_filter.mp hu).1)
        (Fin.castLE hr j) ha hw hround (fun u hu => (hbad u (mem_filter.mp hu).1).1)
        (fun _ hu => (mem_filter.mp hu).2)
    have hcost (j : Fin b.1) : ((U j).card : ℝ) ≤ 6*C := by
      let a := lowerBase (lower b j) w
      have ha : 0 < a := lowerBase_pos (hends j).1 hw
      have heq : a*(1+w) = lower b j := lowerBase_mul hw
      have hround : 1 ≤ 2*(a*w) := by
        calc
          1 ≤ lower b j * w := (hends j).2.2.1
          _ = (a*(1+w))*w := congrArg (fun z : ℝ => z*w) heq.symm
          _ = (a*w)*(1+w) := by ring
          _ ≤ (a*w)*2 := mul_le_mul_of_nonneg_left (by linarith only [hw1]) (mul_nonneg ha.le hw.le)
          _ = 2*(a*w) := mul_comm _ _
      have hl := hs j a ha hround
      have hright := (hends j).2.2.2
      have hu := hs j (b.2.2 j) (hends j).2.1 (by linarith only [hright])
      have htwo : ((U j).card : ℝ) ≤ ((strip j a).card : ℝ) + ((strip j (b.2.2 j)).card : ℝ) := by
        exact_mod_cast (card_union_le (strip j a) (strip j (b.2.2 j)))
      linarith only [htwo, hl, hu]
    have hk : (b.1 : ℝ) ≤ k := by exact_mod_cast hb.1
    calc
      (F.card : ℝ) ≤ ∑ j, ((U j).card : ℝ) := hcard
      _ ≤ ∑ _j : Fin b.1, 6*C := sum_le_sum (fun j _ => hcost j)
      _ = (6*(b.1 : ℝ))*C := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ (6*(k : ℝ)+1)*C := mul_le_mul_of_nonneg_right (by linarith only [hk]) hC
  · have he : F = ∅ := eq_empty_iff_forall_notMem.mpr (fun u hu => by
      obtain ⟨_, h, _⟩ := hbad u hu
      exact hr h)
    rw [he, card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) hC

/-- Every original prefix wall is smooth in the same weight. The first
quantity vanishes in all ranks. The sum of exterior leakage is charged
once, even at intersections; the final L1 includes the complete-product
cap already measured on this very box. -/
theorem uniform_joint_prefix_error (k R : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      let B := collarExponent k
      let w := logWidth B N
      let X := boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
      (∀ r : ℕ, (∑ u ∈ indexedFamily k δ r N b,
        innerWeight B N u * (1-jointWeight δ w r N b u)) = 0) ∧
      (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
        innerWeight B N u * jointWeight δ w r N b u) ≤ (ε/2)*X ∧
      (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
        |innerWeight B N u * jointWeight δ w r N b u - indexedWeight k δ r N b u|) ≤ ε*X := by
  let D : ℝ := 6*(k : ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨T₁, h₁, hwall⟩ := uniform_indexed_wall_error k R hδ hδhi (half_pos hε)
  obtain ⟨T₂, _, hscale⟩ := uniform_collar_scale k R hδ hδhi (div_pos (half_pos hε) hD)
  obtain ⟨T₃, hwidth⟩ := eventually_atTop.mp (eventually_both_widths k (collarExponent k) hδ)
  refine ⟨max (max T₁ T₂) T₃, h₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N hN b hb
  dsimp only
  let B := collarExponent k
  let w := logWidth B N
  let X := boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
  have hN12 := (le_max_left (max T₁ T₂) T₃).trans hN
  have hN1 := (le_max_left T₁ T₂).trans hN12
  have hN2 := (le_max_right T₁ T₂).trans hN12
  have hN3 := (le_max_right (max T₁ T₂) T₃).trans hN
  have hN4 := h₁.trans hN1
  have hw : 0 < w ∧ w ≤ 1 := logWidth_bounds B (by omega : 2 ≤ N)
  have hends := hwidth N hN3 b hb
  have hin (r : ℕ) : (∑ u ∈ indexedFamily k δ r N b,
      innerWeight B N u * (1-jointWeight δ w r N b u)) = 0 := by
    apply sum_eq_zero
    intro u hu
    rw [jointWeight_one hb hw.1 (fun j => (hends j).1) (fun j => (hends j).2.1) hu,
      sub_self, mul_zero]
  have hsum := sum_le_sum (fun r (_ : r ∈ range (R+1)) =>
    finite_prefix_leakage (r:=r) (B:=B) hb hw.1 hw.2 hends)
  have hcost : (∑ r ∈ range (R+1),
      D * (((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ))) =
      D * ((rankMultiplicity R : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) := by
    rw [← mul_sum, ← sum_mul]
    simp only [rankMultiplicity, Nat.cast_sum, Nat.cast_pow]
  change (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
    innerWeight B N u * jointWeight δ w r N b u) ≤
    ∑ r ∈ range (R+1), D * (((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) at hsum
  rw [hcost] at hsum
  have hscaled := hscale N hN2 b.1 b.2.1 b.2.2 hb
  have hout : (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
      innerWeight B N u * jointWeight δ w r N b u) ≤ (ε/2)*X := by
    calc
      _ ≤ D * ((rankMultiplicity R : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) := hsum
      _ ≤ D * (((ε/2)/D)*X) := mul_le_mul_of_nonneg_left hscaled hD.le
      _ = _ := by field_simp [hD.ne'] <;> ring
  have hall := hwall N hN1 b hb (fun r => jointWeight δ w r N b)
    (fun r _ u _ => jointWeight_bounds δ w r N b u)
  have heq (r : ℕ) : otherWallLoss B (indexedFamily k δ r N b) (jointWeight δ w r N b) =
      ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
        innerWeight B N u * jointWeight δ w r N b u := by
    rw [otherWallLoss, hin r, add_zero]
  change (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
    |innerWeight B N u * jointWeight δ w r N b u - indexedWeight k δ r N b u|) ≤
    (∑ r ∈ range (R+1), otherWallLoss B (indexedFamily k δ r N b) (jointWeight δ w r N b)) +
    (ε/2)*X at hall
  simp_rw [heq] at hall
  refine ⟨hin, hout, ?_⟩
  change (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
    |innerWeight B N u * jointWeight δ w r N b u - indexedWeight k δ r N b u|) ≤ ε*X
  linarith only [hall, hout]

end
end ImbalancedChen.P2WuJointWindowTheta
