import ImbalancedChen.P2WuOriginalWindowUpperWall
import ImbalancedChen.Part3ElementaryE1RealEndpoint

/-!
Source only, uncompiled.

For the original strict upper endpoint of any chosen convolution slot,
the opened labels have no loss on the source. Fixing the integer at that
slot restricts the complete positive product to its multiples at most N.
The existing labelled multiplicity bound then pays the whole outer collar
on the moving box's own Theta scale.
-/
namespace ImbalancedChen.P2WuOriginalWindowUpperTheta

noncomputable section
open Classical Finset Filter Wu2008DoubleSieve
open scoped BigOperators
open P2NativeOmega3RankTupleReceiver P2WuProductInnerProfile
open P2WuProductInnerThetaPayment P2WuProductInnerUnsiftedLoss
open P2WuOriginalWindowUpperWall P5Z.ActualSingletonLogCollarFamily
open Part3.ElementaryTauTruncation.IntervalPayment

private theorem count_fixed_slot {r N : ℕ} (S : Finset (Fin r → Fin (N+1)))
    (hS : S ⊆ Part3.labelledPrimeTuples r N) (l : Fin r) (p : ℕ)
    (hcap : ∀ u ∈ S, Part3.labelledProduct u ≤ N)
    (hslot : ∀ u ∈ S, (u l).val = p) :
    S.card ≤ (N/p) * r^r := by
  let M := (Ioc 0 N).filter (fun m => p ∣ m)
  have hmap : (S : Set (Fin r → Fin (N+1))).MapsTo Part3.labelledProduct M := by
    intro u hu
    have hpos : 0 < Part3.labelledProduct u :=
      prod_pos (fun j _ => ((mem_filter.mp (hS hu)).2 j).pos)
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpos,hcap u hu⟩,?_⟩
    rw [← hslot u hu]
    exact dvd_prod_of_mem (fun j => (u j).val) (mem_univ l)
  calc
    S.card = ∑ m ∈ M, (S.filter (fun u => Part3.labelledProduct u = m)).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _m ∈ M, r^r :=
      sum_le_sum (fun m _ => p5z_marked_prime_product_fibre_card_le S hS m)
    _ = _ := by simp [M,Nat.Ioc_filter_dvd_card_eq_div]

/-- An integer equal to either endpoint is included here. Fix its value
first, and then count complete products, with the original multiplicities. -/
private theorem count_slot_strip {r N : ℕ} (S : Finset (Fin r → Fin (N+1)))
    (hS : S ⊆ Part3.labelledPrimeTuples r N) (l : Fin r) {V w : ℝ}
    (hV : 0 < V) (hw : 0 ≤ w)
    (hcap : ∀ u ∈ S, Part3.labelledProduct u ≤ N)
    (hstrip : ∀ u ∈ S, V ≤ ((u l).val : ℝ) ∧ ((u l).val : ℝ) ≤ V*(1+w)) :
    (S.card : ℝ) ≤ ((r^r : ℕ) : ℝ) * ((V*w+1) * ((N : ℝ)/V)) := by
  let I := realClosedNatInterval V (V*(1+w))
  have hVV : V ≤ V*(1+w) := by nlinarith only [mul_nonneg hV.le hw]
  have hhi := hV.le.trans hVV
  have hmap : (S : Set (Fin r → Fin (N+1))).MapsTo (fun u => (u l).val) I :=
    fun u hu => (mem_realClosedNatInterval hhi).mpr (hstrip u hu)
  have hcard : (I.card : ℝ) ≤ V*w+1 := by
    have hc := card_nat_ceiling_floor_le_length_add_one hV.le hVV
    change ((Icc ⌈V⌉₊ ⌊V*(1+w)⌋₊).card : ℝ) ≤ _
    exact hc.trans_eq (by ring)
  calc
    (S.card : ℝ) = ∑ p ∈ I, ((S.filter (fun u => (u l).val = p)).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _p ∈ I, ((r^r : ℕ) : ℝ) * ((N : ℝ)/V) := by
      apply sum_le_sum
      intro p hp
      let F := S.filter (fun u => (u l).val = p)
      have hf := count_fixed_slot F (by
        intro u hu
        exact hS (mem_filter.mp hu).1) l p
        (fun u hu => hcap u (mem_filter.mp hu).1) (fun u hu => (mem_filter.mp hu).2)
      have hpV := ((mem_realClosedNatInterval hhi).mp hp).1
      have hd : ((N/p : ℕ) : ℝ) ≤ (N : ℝ)/V :=
        (Nat.cast_div_le : ((N/p : ℕ) : ℝ) ≤ (N : ℝ)/(p : ℝ)).trans
          (div_le_div_of_nonneg_left (Nat.cast_nonneg N) hV hpV)
      calc
        (F.card : ℝ) ≤ ((N/p : ℕ) : ℝ) * ((r^r : ℕ) : ℝ) := by exact_mod_cast hf
        _ ≤ ((N : ℝ)/V) * ((r^r : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
        _ = _ := mul_comm _ _
    _ = ((r^r : ℕ) : ℝ) * ((I.card : ℝ) * ((N : ℝ)/V)) := by simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcard (div_nonneg (Nat.cast_nonneg _) hV.le))
      (Nat.cast_nonneg _)

private theorem eventually_one_le_window_width (B : ℕ) {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ V : ℝ, (N : ℝ)^α ≤ V → 1 ≤ V * logWidth B N := by
  have hc : 0 < ((2 : ℝ)/Real.log 2)^B :=
    pow_pos (div_pos (by norm_num) (Real.log_pos (by norm_num))) _
  filter_upwards [box_eventually_log_power_budget B hc hα, eventually_ge_atTop (2 : ℕ)]
    with N hbudget hN
  intro V hV
  have htwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnext : (N : ℝ)+2 ≤ (N : ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr htwo)
      (show 0 ≤ (N : ℝ)+1 by positivity)]
  have hl := Real.log_le_log (show 0 < (N : ℝ)+2 by positivity) hnext
  rw [Real.log_pow] at hl
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hL : 0 < Real.log ((N : ℝ)+2) := Real.log_pos (by linarith only [htwo])
  have hd : Real.log ((N : ℝ)+2)/Real.log 2 ≤ (2/Real.log 2)*Real.log (N : ℝ) := by
    calc
      _ ≤ (2*Real.log (N : ℝ))/Real.log 2 :=
        div_le_div_of_nonneg_right (by simpa only [Nat.cast_ofNat] using hl) h2.le
      _ = _ := by ring
  have hpow : (Real.log ((N : ℝ)+2)/Real.log 2)^B ≤ V := by
    calc
      _ ≤ ((2/Real.log 2)*Real.log (N : ℝ))^B :=
        pow_le_pow_left₀ (div_nonneg hL.le h2.le) hd _
      _ = (2/Real.log 2)^B * Real.log (N : ℝ)^B := mul_pow _ _ _
      _ ≤ V := hbudget.trans hV
  have hcancel : (Real.log ((N : ℝ)+2)/Real.log 2)^B * logWidth B N = 1 := by
    rw [logWidth, ← mul_pow]
    have he : Real.log ((N : ℝ)+2)/Real.log 2 *
        (Real.log 2/Real.log ((N : ℝ)+2)) = 1 := by
      field_simp [h2.ne',hL.ne'] <;> ring
    rw [he,one_pow]
  calc
    1 = (Real.log ((N : ℝ)+2)/Real.log 2)^B * logWidth B N := hcancel.symm
    _ ≤ V * logWidth B N := mul_le_mul_of_nonneg_right hpow (logWidth_bounds B hN).1.le

theorem inside_attenuation_zero {k r N B : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (j : Fin b.1)
    (hV : 0 < b.2.2 j) (hw : 0 < w) :
    (∑ u ∈ indexedFamily k δ r N b,
      innerWeight B N u * (1 - wallWeight δ w r N b j u)) = 0 := by
  apply sum_eq_zero
  intro u hu
  rw [wallWeight_one hb j hV hw hu,sub_self,mul_zero]

private theorem finite_outside {k r N B : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (j : Fin b.1)
    (hV : 0 < b.2.2 j) (hw : 0 < w) (hround : 1 ≤ b.2.2 j*w) :
    (∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
      innerWeight B N u * wallWeight δ w r N b j u) ≤
      2 * (((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) := by
  let A := Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b
  let F := A.filter (fun u => wallWeight δ w r N b j u ≠ 0)
  have hcount : (∑ u ∈ A, innerWeight B N u * wallWeight δ w r N b j u) ≤ (F.card : ℝ) := by
    calc
      _ ≤ ∑ u ∈ A, if wallWeight δ w r N b j u ≠ 0 then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro u _
        by_cases hz : wallWeight δ w r N b j u = 0
        · simp [hz]
        · rw [if_pos hz]
          calc
            _ ≤ innerWeight B N u * 1 := mul_le_mul_of_nonneg_left
              (wallWeight_bounds δ w r N b j u).2 (innerWeight_bounds B N u).1
            _ ≤ 1 := by simpa only [mul_one] using (innerWeight_bounds B N u).2
      _ = _ := by rw [← sum_filter]; simp [F]
  have hF (u) (hu : u ∈ F) :=
    outside_nonzero hb j hV hw (mem_sdiff.mp (mem_filter.mp hu).1).2 (mem_filter.mp hu).2
  by_cases hr : j.val < r
  · let V := b.2.2 j
    let l : Fin r := ⟨j.val,hr⟩
    have hs : F ⊆ Part3.labelledPrimeTuples r N := by
      intro u hu
      exact (mem_sdiff.mp (mem_filter.mp hu).1).1
    have hraw := count_slot_strip F hs l hV hw.le (fun u hu => (hF u hu).1)
      (by
        intro u hu
        obtain ⟨_,hlo,hhi⟩ := (hF u hu).2
        exact ⟨hlo,hhi.le⟩)
    have hlin : (V*w+1)*((N : ℝ)/V) ≤ 2*(w*(N : ℝ)) := by
      calc
        _ ≤ (V*w+V*w)*((N : ℝ)/V) :=
          mul_le_mul_of_nonneg_right (add_le_add_left hround _)
            (div_nonneg (Nat.cast_nonneg N) hV.le)
        _ = _ := by field_simp [show V ≠ 0 from hV.ne'] <;> ring
    calc
      _ ≤ (F.card : ℝ) := hcount
      _ ≤ ((r^r : ℕ) : ℝ) * ((V*w+1)*((N : ℝ)/V)) := hraw
      _ ≤ ((r^r : ℕ) : ℝ) * (2*(Nat.ceil (w*(N : ℝ)) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hlin.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  · have hempty : F = ∅ := eq_empty_iff_forall_notMem.mpr (fun u hu => by
      obtain ⟨h,_⟩ := (hF u hu).2
      exact hr h)
    apply hcount.trans
    rw [hempty,card_empty,Nat.cast_zero]
    positivity

/-- A single threshold pays both the original complete-product cap and
one selected moving strict upper wall. It precedes the whole sigma box,
the choice of old slot, and every original multiplicity. The remaining
walls have their exact sharp masks in wallWeight. -/
theorem uniform_indexed_upper_wall_error (k R : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 → ∀ j : Fin b.1,
      let B := collarExponent k
      let w := logWidth B N
      let X := boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
      (∀ r : ℕ, (∑ u ∈ indexedFamily k δ r N b,
        innerWeight B N u * (1 - wallWeight δ w r N b j u)) = 0) ∧
      (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
        innerWeight B N u * wallWeight δ w r N b j u) ≤ (ε/2)*X ∧
      (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
        |innerWeight B N u * wallWeight δ w r N b j u - indexedWeight k δ r N b u|) ≤ ε*X := by
  obtain ⟨T₁,h₁,hwall⟩ := uniform_indexed_wall_error k R hδ hδhi (half_pos hε)
  obtain ⟨T₂,_,hscale⟩ := uniform_collar_scale k R hδ hδhi (show 0 < ε/4 by linarith)
  obtain ⟨T₃,hwidth⟩ := eventually_atTop.mp
    (eventually_one_le_window_width (collarExponent k) (pow_pos hδ (k+1)))
  refine ⟨max (max T₁ T₂) T₃,h₁.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro N hN b hb j
  dsimp only
  let B := collarExponent k
  let w := logWidth B N
  let X := boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
  have hN12 := (le_max_left (max T₁ T₂) T₃).trans hN
  have hN1 := (le_max_left T₁ T₂).trans hN12
  have hN2 := (le_max_right T₁ T₂).trans hN12
  have hN3 := (le_max_right (max T₁ T₂) T₃).trans hN
  have hN4 := h₁.trans hN1
  have hw : 0 < w := (logWidth_bounds B (by omega : 2 ≤ N)).1
  have hVlo := hb.2.2.2.2.1 j
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV : 0 < b.2.2 j :=
    (Real.rpow_pos_of_pos hNr _).trans_le hVlo
  have hround := hwidth N hN3 (b.2.2 j) hVlo
  have hin (r : ℕ) := inside_attenuation_zero (r:=r) (B:=B) hb j hV hw
  have hsum := sum_le_sum (fun r (_ : r ∈ range (R+1)) =>
    finite_outside (r:=r) (B:=B) hb j hV hw hround)
  have hcost : (∑ r ∈ range (R+1),
      2 * (((r^r : ℕ) : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ))) =
      2 * ((rankMultiplicity R : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ)) := by
    rw [← mul_sum, ← sum_mul]
    simp only [rankMultiplicity,Nat.cast_sum,Nat.cast_pow]
  rw [hcost] at hsum
  have hscaled := hscale N hN2 b.1 b.2.1 b.2.2 hb
  change (rankMultiplicity R : ℝ) * (Nat.ceil (w*(N : ℝ)) : ℝ) ≤ (ε/4)*X at hscaled
  have hout : (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
      innerWeight B N u * wallWeight δ w r N b j u) ≤ (ε/2)*X := by
    linarith only [hsum,hscaled]
  refine ⟨hin,hout,?_⟩
  have hall := hwall N hN1 b hb (fun r => wallWeight δ w r N b j)
    (fun r _ u _ => wallWeight_bounds δ w r N b j u)
  have heq (r : ℕ) : otherWallLoss B (indexedFamily k δ r N b) (wallWeight δ w r N b j) =
      ∑ u ∈ Part3.labelledPrimeTuples r N \ indexedFamily k δ r N b,
        innerWeight B N u * wallWeight δ w r N b j u := by
    rw [otherWallLoss,hin r,add_zero]
  change (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
    |innerWeight B N u * wallWeight δ w r N b j u - indexedWeight k δ r N b u|) ≤
      (∑ r ∈ range (R+1), otherWallLoss B (indexedFamily k δ r N b) (wallWeight δ w r N b j)) +
      (ε/2)*X at hall
  simp_rw [heq] at hall
  change (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
    |innerWeight B N u * wallWeight δ w r N b j u - indexedWeight k δ r N b u|) ≤ ε*X
  linarith only [hall,hout]

end
end ImbalancedChen.P2WuOriginalWindowUpperTheta
