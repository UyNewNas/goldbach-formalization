import ImbalancedChen.Part5OriginalH430AllLaneMemberQuery
import ImbalancedChen.Part5OriginalH430RequestedAdmission

/-! Structural cutoff equality on the actual moving children. Padded comparisons
keep the original read, owner, modulus, path marks and additive-prime test. The
last finite identity records the arithmetic price of this comparison in either
direction, with no assumed upper bound for its size. -/
namespace ImbalancedChen.Part5OriginalH430StrictCutoffTransfer

noncomputable section
open scoped Classical BigOperators
open Set P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab)
open Wu2008DoubleSieve (primeWindow)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedMemberBox Part5OriginalH430SelectedMemberFixedQuery
open Part5OriginalH430AllEmittedReceiptLanes Part5OriginalH430AllLaneMemberQuery

private theorem one_contact (p : PhysicalNode) (z : Point) (hx : 0 < z 0)
    (hr : 0 < residual (appendOne p (z 0) (buchstabArgument p z))) :
    let v := appendOne p (z 0) (buchstabArgument p z)
    residual v / v.argument = v.ceiling := by
  dsimp only
  rw [residual_appendOne] at hr ⊢
  change (residual p-z 0)/(residual p/z 0-1) = z 0
  have hs : 0 < residual p/z 0-1 := by
    have h := (lt_div_iff₀ hx).mpr (by linarith only [hr] : 1*z 0 < residual p)
    linarith only [h]
  apply (div_eq_iff hs.ne').mpr
  field_simp [hx.ne'] <;> ring

/-- Both signs of the genuine single-prime Buchstab edge have this equality,
including children in the strict interior of the parent integration domain. -/
theorem actual_buchstab_contact {N g : ℕ} {Q : ℝ} {r : Request} {b : Bool}
    {q : Fin (N+1)} (hr : Coherent N Q r) (he : .buchstab b q ∈ children N Q g r) :
    let v := (nextRequest r (.buchstab b q)).node.physical
    residual v / v.argument = v.ceiling ∧ v.ceiling = physicalPrime N q.val := by
  have h := (child_admission hr he).2.1
  cases b
  · exact ⟨one_contact _ _ h.2.2.1.1 (perform_residual_pos h),rfl⟩
  · exact ⟨one_contact _ _ h.2.1.1 (perform_residual_pos h),rfl⟩

/-- On D7 and D8 the moving query uses the small appended prime. The same
identity holds on the entire pair domain and each genuine integer child. -/
theorem actual_moving_pair_contact {N g : ℕ} {Q : ℝ} {r : Request} {j : Fin 36}
    {k : Fin 4} {q : Fin (N+1) × Fin (N+1)} (hr : Coherent N Q r)
    (hk : 2 ≤ k.val) (he : .w2Pair j k q ∈ children N Q g r) :
    let v := (nextRequest r (.w2Pair j k q)).node.physical
    residual v / v.argument = v.ceiling ∧ v.ceiling = physicalPrime N q.1.val := by
  have h := (child_admission hr he).2.1
  let p := r.node.physical
  let z := edgeCoordinates (.w2Pair j k q)
  have hd : LocalDomain p (.w2Pair j k) z := h
  have hL := hd.1
  have hx := hd.2.1.1
  have hs := (W2PairDomain_profile_bounds
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k hd.2.2.1).1
  have hp : 0 < pairProfile (originalW2At j) k (normalized p z) := zero_lt_one.trans hs
  refine ⟨?_,rfl⟩
  change residual (appendPair p (z 0) (z 1) _) /
    pairProfile (originalW2At j) k (normalized p z) = z 0
  rw [residual_appendPair]
  apply (div_eq_iff hp.ne').mpr
  rw [pairProfile,if_neg (not_lt.mpr hk)]
  dsimp only [movingPairProfile,normalized]
  field_simp [hL.ne',hx.ne'] <;> ring

/-- An open rectangle of normalized seed coordinates in each moving region.
Its positive width is independent of the prime grid and all square gates have
slack throughout. This asserts domain membership, not selection of bank 0. -/
theorem seed_moving_rectangles {u v : ℝ} (hu : u ∈ Ioo (23/100:ℝ) (24/100))
    (hv : v ∈ Ioo (25/100:ℝ) (26/100) ∨ v ∈ Ioo (30/100:ℝ) (31/100)) :
    ((![u,v] : Point) ∈ W2PairDomain (originalW2At 0) 2 ∨
     (![u,v] : Point) ∈ W2PairDomain (originalW2At 0) 3) ∧
    2*v < (62/100:ℝ) ∧ v+2*u < (79/100:ℝ) := by
  have h0 : a0 (originalW2At 0) = (50/227:ℝ) := by
    norm_num [a0,originalW2At,originalRepairedW2Bank]
  have h1 : a1 (originalW2At 0) = (100/353:ℝ) := by
    norm_num [a1,originalW2At,originalRepairedW2Bank]
  have h2 : a2 (originalW2At 0) = (10/29:ℝ) := by
    norm_num [a2,originalW2At,originalRepairedW2Bank]
  rcases hu with ⟨ul,ur⟩
  rcases hv with ⟨vl,vr⟩ | ⟨vl,vr⟩
  · refine ⟨Or.inl ?_,by linarith,by linarith⟩
    change a0 _ < u ∧ u < v ∧ v < a1 _
    rw [h0,h1]
    exact ⟨by linarith,by linarith,by linarith⟩
  · refine ⟨Or.inr ?_,by linarith,by linarith⟩
    change a0 _ < u ∧ u < a1 _ ∧ a1 _ < v ∧ v < a2 _
    rw [h0,h1,h2]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

private theorem query_upper {mesh fine : ℕ} (u : Key mesh fine) : query u ≤ 6 := by
  have hf (b : Box mesh) : fixedQuery b ≤ 6 := by
    unfold fixedQuery
    split_ifs
    · norm_num
    · cases hc : b.2.2 with
      | none => norm_num
      | some i =>
        change gridArgument i ≤ 6
        have hi : (i.val:ℝ) < 200 := by exact_mod_cast i.isLt
        dsimp only [gridArgument]
        linarith
  unfold query
  split_ifs
  · norm_num
  · exact (min_le_left _ _).trans (hf _)

def margin (eta : ℝ) : ℝ := frozenResidualFloor*eta/96

private theorem padded_gap {L s w chi eta : ℝ}
    (hL : frozenResidualFloor ≤ L) (hs : s ∈ Icc (1:ℝ) 6)
    (hw : s ≤ w) (hw6 : w ≤ 6) (hc : L ≤ s*chi)
    (he : 0 < eta) (he1 : eta ≤ 1) :
    L/(w+eta) + margin eta ≤ chi - margin eta := by
  have hs0 := zero_lt_one.trans_le hs.1
  have ht : 0 < w+eta := by linarith
  have ht7 : w+eta ≤ 7 := by linarith
  have hden : s*(w+eta) ≤ 48 :=
    (mul_le_mul hs.2 ht7 ht.le (by norm_num : (0:ℝ)≤6)).trans (by norm_num)
  have hnum := mul_le_mul hL (by linarith only [hw] : eta ≤ w+eta-s)
    he.le (frozenResidualFloor_pos.trans_le hL).le
  have hid : L/s - L/(w+eta) = L*(w+eta-s)/(s*(w+eta)) := by
    field_simp [hs0.ne',ht.ne'] <;> ring
  have hratio : frozenResidualFloor*eta/48 ≤ L/s-L/(w+eta) := by
    rw [hid]
    apply (le_div_iff₀ (mul_pos hs0 ht)).mpr
    calc
      _ ≤ (frozenResidualFloor*eta/48)*48 :=
        mul_le_mul_of_nonneg_left hden (div_nonneg (mul_nonneg frozenResidualFloor_pos.le he.le)
          (by norm_num))
      _ = frozenResidualFloor*eta := by ring
      _ ≤ _ := hnum
  have h0 : L/s ≤ chi := (div_le_iff₀ hs0).mpr (hc.trans_eq (mul_comm _ _))
  dsimp only [margin]
  linarith only [h0,hratio]

/-- A fixed η and finite owner-preserving query mesh give a single geometric
margin for all occupied occurrences, even the clamp or an exterior read.
Only the analysis comparison is shifted. The stored original query remains s. -/
theorem actual_padded_comparison {N n m mesh fine : ℕ} {k : Root} {t : ℝ}
    {G : Fin 431} {c : RootKey n m} {u : Key mesh fine} {a : Position N n k t G}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (ha : a ∈ atKey k t G c u) {eta : ℝ} (he : 0<eta) (he1 : eta≤1) :
    let v := (levelOccurrence a.2).current.node.physical
    0 < margin eta ∧ 0 < v.ceiling - margin eta ∧
      residual v/(query u + eta) + margin eta ≤ v.ceiling-margin eta ∧
      u.1.1.2.2 = resolve G.val (levelOccurrence a.2).current := by
  have hp := (Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_filter.mp ha).1).1).1
  have hb := original_band_geometry hN hp
  have ho := (levelOccurrence_source a.2).1
  have hg := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp) hb ho
  have hc := rootHistory_coherent (by omega : 1<N) ht hu hn (original_band_prime hp) hb ho
  have hq := owned_query hN ht hu hn ha
  let v := (levelOccurrence a.2).current.node.physical
  have hf : frozenResidualFloor ≤ residual v := hg.2.2.1.trans_eq hg.2.1.symm
  have hfit : residual v ≤ v.argument*v.ceiling := hc.cutoff_fits
  have hh := padded_gap hf hg.2.2.2.1 hq.2.2.2.1 (query_upper u) hfit he he1
  have hm : 0 < margin eta := div_pos (mul_pos frozenResidualFloor_pos he) (by norm_num)
  have hs : 0 < query u + eta := by
    have := (zero_lt_one.trans_le hg.2.2.2.1.1).trans_le hq.2.2.2.1
    linarith
  have hpos := div_pos (frozenResidualFloor_pos.trans_le hf) hs
  exact ⟨hm,by linarith only [hh,hm,hpos],hh,hq.1⟩

/-- The actual extra least-prime window for the padded comparison. E can be
the original masked receipt, its true complement, or the ordinary receiver. -/
def paddedShell {N : ℕ} (Q : ℝ) (o : Occurrence N) (w : ℝ) (E : ℕ → Prop) : ℤ :=
  let B := parentProduct o.current.old
  ∑ q ∈ primeWindow (B*N) (cutoff Q B w) (memberCutoff Q o), frozenCount N (B*q) E (q:ℝ)

theorem actual_padded_count {N n m mesh fine : ℕ} {k : Root} {t : ℝ}
    {G : Fin 431} {c : RootKey n m} {u : Key mesh fine} {a : Position N n k t G}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (ha : a ∈ atKey k t G c u) {eta : ℝ} (he : 0≤eta) (E : ℕ → Prop) :
    let o := levelOccurrence a.2
    let Q := cellQ N n c.1
    let B := parentProduct o.current.old
    frozenCount N B E (cutoff Q B (query u+eta)) =
      frozenCount N B E (memberCutoff Q o) + paddedShell Q o (query u+eta) E := by
  have hp := (Finset.mem_sigma.mp (Finset.mem_filter.mp ha).1).1
  have hb := (Finset.mem_filter.mp hp).1
  have ho := (levelOccurrence_source a.2).1
  have hh := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hb)
    (original_band_geometry hN hb) ho
  have hQ := (original_fibre_geometry hN ht hu hn hp).1
  have hR := (parentWindow_logs hh.1).2.1
  rw [← hQ] at hR
  have hw := (owned_query hN ht hu hn ha).2.2.2.1
  have hcut := Real.rpow_le_rpow_of_exponent_le hR.le
    (one_div_le_one_div_of_le (zero_lt_one.trans_le hh.2.2.2.1.1)
      (hw.trans (le_add_of_nonneg_right he)))
  exact frozen_selected_buchstab N _ E hcut

/-- For all positive, negative or zero multipliers, with any label-dependent
test on the original additive prime, the compensation has exactly the old
label weight and the old owner. -/
theorem signed_padded_count {N n m mesh fine : ℕ} (k : Root) {t : ℝ}
    (G : Fin 431) (c : RootKey n m) (u : Key mesh fine)
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    {eta : ℝ} (he : 0≤eta) (f : Position N n k t G → ℝ)
    (E : Position N n k t G → ℕ → Prop) :
    let Q := cellQ N n c.1
    (∑ a ∈ atKey k t G c u, f a*levelMark a.2*
      (frozenCount N (parentProduct (levelOccurrence a.2).current.old) (E a)
        (memberCutoff Q (levelOccurrence a.2)) : ℝ)) =
    ∑ a ∈ atKey k t G c u, f a*levelMark a.2*
      ((frozenCount N (parentProduct (levelOccurrence a.2).current.old) (E a)
         (cutoff Q (parentProduct (levelOccurrence a.2).current.old) (query u+eta)) : ℝ) -
        (paddedShell Q (levelOccurrence a.2) (query u+eta) (E a) : ℝ)) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro a ha
  rw [actual_padded_count hN ht hu hn ha he (E a),Int.cast_add]
  ring

end
end ImbalancedChen.Part5OriginalH430StrictCutoffTransfer
