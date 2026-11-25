import ImbalancedChen.P5ActualHBDyadicOccurrenceFamily

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual nonzero HB dyadic coefficients expose their literal ordered factor
tuples. Thus their raw product window is DERIVED, not a hypothesis of a
putative HB chart: prod(lower blocks)<=n<=2^r*prod(lower blocks), r<=6.
Actual role positions, strict-left/closed-right interval ownership, and
REAL Mobius cutoffs are all retained. No long-slot or SW oracle appears.
-/
namespace ImbalancedChen.P5Z.ActualHBDyadicProductWindow
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily

def lower : Block → ℕ
  | .unit => 1
  | .dyadic k => 2^k

theorem lower_pos (b : Block) : 0<lower b := by
  cases b with
  | unit => decide
  | dyadic k => exact Nat.pow_pos (by omega)

theorem owns_bounds {b : Block} {p : ℕ} (h : Owns b p) :
    lower b≤p ∧ p≤2*lower b := by
  cases b with
  | unit =>
    change p=1 at h
    simp [lower,h]
  | dyadic k =>
    change 2^k<p ∧ p≤2^(k+1) at h
    exact ⟨h.1.le,by simpa only [lower,pow_succ,mul_comm] using h.2⟩

theorem assigned_nonzero_owns : ∀rs : List Role, ∀bs : List Block, ∀ps : List ℕ,
    assignedWeight z y rs bs ps≠0 → List.Forall₂ Owns bs ps := by
  intro rs
  induction rs with
  | nil =>
    intro bs ps hn
    cases bs with
    | nil =>
      cases ps with
      | nil => exact List.Forall₂.nil
      | cons p ps => simp [assignedWeight] at hn
    | cons b bs => simp [assignedWeight] at hn
  | cons r rs ih =>
    intro bs ps hn
    cases bs with
    | nil => simp [assignedWeight] at hn
    | cons b bs =>
      cases ps with
      | nil => simp [assignedWeight] at hn
      | cons p ps =>
        have hp := mul_ne_zero_iff.mp hn
        have hb : Owns b p := by
          by_contra hh
          exact hp.1 (by simp only [blockValue,if_neg hh])
        exact List.Forall₂.cons hb (ih bs ps hp.2)

theorem assigned_eq_rough_of_owns {bs : List Block} {ps : List ℕ}
    (h : List.Forall₂ Owns bs ps) : ∀rs : List Role,
      assignedWeight z y rs bs ps=roughTupleWeight z y rs ps := by
  induction h with
  | nil => intro rs; cases rs <;> rfl
  | cons hbp htail ih =>
    intro rs
    cases rs with
    | nil => rfl
    | cons r rs => simp only [assignedWeight,roughTupleWeight,blockValue,if_pos hbp,ih]

theorem owns_product_window {bs : List Block} {ps : List ℕ}
    (h : List.Forall₂ Owns bs ps) :
    (bs.map lower).prod≤ps.prod ∧ ps.prod≤2^bs.length*(bs.map lower).prod := by
  induction h with
  | nil => simp
  | @cons b p bs ps hbp htail ih =>
    have hh := owns_bounds hbp
    refine ⟨?_,?_⟩
    · simpa only [List.map_cons,List.prod_cons] using Nat.mul_le_mul hh.1 ih.1
    · calc
        _ = p*ps.prod := rfl
        _ ≤ (2*lower b)*(2^bs.length*(bs.map lower).prod) := Nat.mul_le_mul hh.2 ih.2
        _ = _ := by simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]; ring

private theorem owns_mem_witness {bs : List Block} {ps : List ℕ}
    (h : List.Forall₂ Owns bs ps) : ∀b∈bs,∃p∈ps,Owns b p := by
  induction h with
  | nil => intro b hb; simp at hb
  | @cons b p bs ps hbp htail ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨p,by simp,hbp⟩
    · obtain ⟨q,hq,haq⟩ := ih a ha
      exact ⟨q,List.mem_cons_of_mem p hq,haq⟩

theorem active_coefficient_tuple {z y : ℝ} (hz : 0≤z) {j n : ℕ} {bs : List Block}
    (hn : blockCoefficient z y j n bs≠0) :
    ∃ps∈factorTuples (2*(j+1)) n,
      assignedWeight z y (roles j) bs ps≠0 ∧ List.Forall₂ Owns bs ps ∧
      (∀p∈ps,0<p ∧ p≤n) ∧ (∀p∈ps.take (j+1),(p : ℝ)≤y) := by
  have hex : ∃ps∈factorTuples (2*(j+1)) n,assignedWeight z y (roles j) bs ps≠0 := by
    by_contra hnot
    apply hn
    unfold blockCoefficient
    apply Finset.sum_eq_zero
    intro ps hps
    by_contra hw
    exact hnot ⟨ps,hps,hw⟩
  obtain ⟨ps,hps,ha⟩ := hex
  have ho := assigned_nonzero_owns (roles j) bs ps ha
  have hrough : roughTupleWeight z y (roles j) ps≠0 := by
    rw [← assigned_eq_rough_of_owns ho (roles j)]
    exact ha
  exact ⟨ps,hps,ha,ho,(fun p hp => actual_factor_bound hps hp),
    actual_word_nonzero_cutoff hz y j n ps hps hrough⟩

/-- Every raw window and endpoint cap follows from ACTUAL activity.
There is no hHBlo/hHBhi, factor-size or chosen-slot premise. -/
theorem actual_block_product_window {z y : ℝ} (hz : 0≤z) {j n : ℕ} {bs : List Block}
    (hn : blockCoefficient z y j n bs≠0) :
    bs.length=2*(j+1) ∧ (bs.map lower).prod≤n ∧
      n≤2^(2*(j+1))*(bs.map lower).prod ∧ ∀b∈bs,lower b≤n := by
  obtain ⟨ps,hps,ha,ho,hbounds,hcut⟩ := active_coefficient_tuple hz hn
  have hspec := factorTuples_spec (2*(j+1)) n ps hps
  have hlen : bs.length=2*(j+1) := ho.length_eq.trans hspec.1
  have hw := owns_product_window ho
  refine ⟨hlen,?_,?_,?_⟩
  · simpa only [hspec.2.1] using hw.1
  · simpa only [hspec.2.1,hlen] using hw.2
  · intro b hb
    obtain ⟨p,hp,hbp⟩ := owns_mem_witness ho b hb
    exact (owns_bounds hbp).1.trans (hbounds p hp).2

theorem actual_block_six_slot_window {z y : ℝ} (hz : 0≤z) {j n : ℕ} {bs : List Block}
    (hj : j∈Finset.range 3) (hn : blockCoefficient z y j n bs≠0) :
    bs.length≤6 ∧ (bs.map lower).prod≤n ∧ n≤64*(bs.map lower).prod := by
  obtain ⟨hlen,hlo,hhi,hcaps⟩ := actual_block_product_window hz hn
  have he : 2*(j+1)≤6 := by have := Finset.mem_range.mp hj; omega
  have hp : 2^(2*(j+1))≤64 := by
    have h := Nat.pow_le_pow_right (by omega : 0<(2 : ℕ)) he
    norm_num only [show (2 : ℕ)^6=64 by decide] at h
    exact h
  exact ⟨by omega,hlo,hhi.trans (Nat.mul_le_mul_right _ hp)⟩

end
end ImbalancedChen.P5Z.ActualHBDyadicProductWindow
