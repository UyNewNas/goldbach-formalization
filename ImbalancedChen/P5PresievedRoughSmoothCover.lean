import ImbalancedChen.P5PresievedRoughSmoothBoxAtoms

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite separated smooth covers of the ORIGINAL upper/order rough region
at every fixed residual rank. Pointwise error is charged to actual proper
affine walls or actual coordinate faces. The cover is attached to literal
canonical rough-slot vectors of the new coefficient, with the complete
original N-scale prime ceilings and strict endpoints retained.
-/
namespace ImbalancedChen.P5Z.PresievedRoughSmoothCover
noncomputable section
open Classical Set
open scoped BigOperators
open PresievedRoughGateMeshReserve PresievedRoughSmoothBoxAtoms
open OriginalOrdinaryCommonBetaModel OriginalPresievedRoughPrimeSlots
open JointPresievedSlotAffineRealization

def roughIndicator {r : ℕ} (ell : ℝ) (v : Fin r → ℝ) : ℝ :=
  if v ∈ roughRegion r ell then 1 else 0

def roughCover (inner : Bool) (r : ℕ) (a b ell : ℝ) (n : ℕ) (δ : ℝ) (v : Fin r → ℝ) : ℝ :=
  cover inner δ a b (if inner then innerCells r a b ell n else outerCells r a b ell n) v

def reserve (inner : Bool) (r : ℕ) (a b ell : ℝ) (n : ℕ) (δ : ℝ) (v : Fin r → ℝ) : Prop :=
  faceReserve inner δ a b (if inner then innerCells r a b ell n else outerCells r a b ell n) v ∨
    wallReserve r a b ell n v

theorem literalCover_at_cell {r n : ℕ} {a b : ℝ} (hab : a < b) (J : Finset (Grid r n))
    {j : Grid r n} {v : Fin r → ℝ} (hv : v ∈ cell a b n j) :
    literalCover a b J v = if j ∈ J then 1 else 0 := by
  unfold literalCover
  by_cases hj : j ∈ J
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [literalAtom_eq_indicator, if_pos hv]
    · intro k hk hne
      rw [literalAtom_eq_indicator, if_neg]
      exact fun hkv => hne (logPrimeMeshCell_unique hab.le hkv hv)
    · exact fun hn => (hn hj).elim
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    rw [literalAtom_eq_indicator, if_neg]
    intro hkv
    exact hj ((logPrimeMeshCell_unique hab.le hkv hv) ▸ hk)

theorem literal_sandwich {r : ℕ} {a b : ℝ} (hab : a < b) (ell : ℝ) (n : ℕ)
    {v : Fin r → ℝ} (hbox : v ∈ logPrimeBox (fun _ => a) (fun _ => b)) :
    literalCover a b (innerCells r a b ell n) v ≤ roughIndicator ell v ∧
      roughIndicator ell v ≤ literalCover a b (outerCells r a b ell n) v := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell a b n hbox
  rw [literalCover_at_cell hab _ hj, literalCover_at_cell hab _ hj]
  by_cases hr : v ∈ roughRegion r ell
  · have ho : j ∈ outerCells r a b ell n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hj, hr⟩
    simp only [roughIndicator, if_pos hr, if_pos ho]
    constructor
    · split_ifs <;> norm_num
    · exact le_rfl
  · have hi : j ∉ innerCells r a b ell n := fun hi => hr ((Finset.mem_filter.mp hi).2 v hj)
    simp only [roughIndicator, if_neg hr, if_neg hi]
    constructor
    · exact le_rfl
    · split_ifs <;> norm_num

/-- Actual arithmetic pointwise sandwich, valid before any prime sum or
limiting measure. Every summand is a separated compact smooth box. -/
theorem smooth_sandwich {r : ℕ} {a b : ℝ} (hab : a < b) (ell : ℝ) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : Fin r → ℝ}
    (hbox : v ∈ logPrimeBox (fun _ => a) (fun _ => b)) :
    roughCover true r a b ell n δ v ≤ roughIndicator ell v ∧
      roughIndicator ell v ≤ roughCover false r a b ell n δ v := by
  have hl := literal_sandwich hab ell n hbox
  exact ⟨(cover_sandwich hδ a b _ v).1.trans hl.1,
    hl.2.trans (cover_sandwich hδ a b _ v).2⟩

private theorem literal_error_wall {r : ℕ} {a b : ℝ} (hab : a < b) (ell : ℝ) (n : ℕ)
    (inner : Bool) {v : Fin r → ℝ} (hbox : v ∈ logPrimeBox (fun _ => a) (fun _ => b))
    (he : literalCover a b (if inner then innerCells r a b ell n else outerCells r a b ell n) v -
      roughIndicator ell v ≠ 0) : wallReserve r a b ell n v := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell a b n hbox
  have hout : j ∈ outerCells r a b ell n := by
    by_contra ho
    have hr : v ∉ roughRegion r ell := fun hr => ho
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hj, hr⟩)
    have hi : j ∉ innerCells r a b ell n := fun hi => hr ((Finset.mem_filter.mp hi).2 v hj)
    apply he
    cases inner <;> simp [literalCover_at_cell hab _ hj, roughIndicator, ho, hi, hr]
  have hnot : j ∉ innerCells r a b ell n := by
    intro hi
    have hr : v ∈ roughRegion r ell := (Finset.mem_filter.mp hi).2 v hj
    apply he
    cases inner <;> simp [literalCover_at_cell hab _ hj, roughIndicator, hout, hi, hr]
  exact crossing_cell_wall hab hout hnot hj

/-- No prime atom on an order, cube, total-product or fine-grid face is
discarded. Each actual error point is in the displayed reserve. -/
theorem smooth_error_supported {r : ℕ} {a b : ℝ} (hab : a < b) (ell : ℝ) (n : ℕ)
    (inner : Bool) {δ : ℝ} (hδ : 0 < δ) {v : Fin r → ℝ}
    (hbox : v ∈ logPrimeBox (fun _ => a) (fun _ => b))
    (he : roughCover inner r a b ell n δ v - roughIndicator ell v ≠ 0) :
    reserve inner r a b ell n δ v := by
  by_cases hf : roughCover inner r a b ell n δ v -
      literalCover a b (if inner then innerCells r a b ell n else outerCells r a b ell n) v ≠ 0
  · exact Or.inl (cover_error_face hδ inner a b _ v hf)
  · right
    apply literal_error_wall hab ell n inner hbox
    have heq := sub_eq_zero.mp (not_ne_iff.mp hf)
    rwa [← heq]

/-- The actual original retained rough divisor supplies its OWN literal
slot vector in this original rough region and original power box. -/
theorem retained_rough_point {N cap d : ℕ} (hN : 1 < N) (rho zeta ell : ℝ)
    (hL : 1 < (N : ℝ) ^ ell)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap
      ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta)) :
    let ps := canonicalSlots N cap ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta) d
    let p := slotVector ps
    actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => rho) (fun _ => zeta) ∩ roughRegion ps.length ell := by
  let ps := canonicalSlots N cap ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta) d
  let p := slotVector ps
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hp (i : Fin ps.length) := canonicalSlots_prime_data (N := N) (cap := cap)
    (d := d) (List.getElem_mem i.isLt)
  have hpos : ∀ i, 0 < p i := fun i => (hp i).1.pos
  have hdesc : StrictAnti p := by
    apply List.pairwise_ofFn.mp
    rw [ofFn_slotVector]
    exact canonicalSlots_descending N cap _ _ d
  refine ⟨mem_logPrimeBox.mpr (fun i => ?_), (roughRegion_dictionary ell _).mpr ⟨?_, ?_⟩⟩
  · have hpow := actualPrimeTupleLog_rpow hN p hpos i
    constructor
    · apply (Real.rpow_le_rpow_left_iff hn).mp
      simpa only [hpow] using (hp i).2.2.1
    · apply (Real.rpow_lt_rpow_left_iff hn).mp
      simpa only [hpow] using (hp i).2.2.2
  · exact retained_slots_log_region hN hL hd
  · exact (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hdesc

theorem actual_rough_smooth_sandwich {N cap d : ℕ} (hN : 1 < N) (rho zeta ell : ℝ)
    (hcut : rho < zeta) (hL : 1 < (N : ℝ) ^ ell)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap
      ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta)) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let ps := canonicalSlots N cap ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta) d
    let v := actualPrimeTupleLog N (slotVector ps)
    roughCover true ps.length rho zeta ell n δ v ≤ 1 ∧
      1 ≤ roughCover false ps.length rho zeta ell n δ v := by
  have hp := retained_rough_point hN rho zeta ell hL hd
  have h := smooth_sandwich hcut ell n hδ hp.1
  simpa only [roughIndicator, if_pos hp.2] using h

end
end ImbalancedChen.P5Z.PresievedRoughSmoothCover
