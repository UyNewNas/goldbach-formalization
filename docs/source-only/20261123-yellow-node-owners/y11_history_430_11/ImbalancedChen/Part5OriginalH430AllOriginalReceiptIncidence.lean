import ImbalancedChen.P5OriginalCoprimeRationalEndpoint
import ImbalancedChen.Part5OriginalH430MonotoneSieveHeight
import ImbalancedChen.Part5OriginalH430CompatibleHistoryPayment
import ImbalancedChen.Part5OriginalH430ZeroFreshReceiverPayment

/-! Every original rough quotient, including those with a post-root factor, in the
actual U3 and U4 histories. The moving Buchstab boundary can touch the original
sieve height in physical coordinates. An integer prime coprime to N cannot equal
the manuscript's rational power at that boundary. -/
namespace ImbalancedChen.Part5OriginalH430AllOriginalReceiptIncidence

noncomputable section
open scoped Classical BigOperators Topology
open Finset Filter
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2FrozenReceiverCountActions (frozenCount)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430IntegerItineraries Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430CompatibleHistoryPayment
open Part5OriginalH430ZeroFreshReceiverPayment Part5OriginalH430MonotoneSieveHeight
open Part5OriginalH430ClassicalReceiverSubfamily Part5OriginalH430ClassicalRootThetaPayment

private theorem first_coordinate_le {N : ℕ} {r : Request} {Q : ℝ} {e : Edge N}
    (hc : Coherent N Q r) (ad : EdgeAdmitted N r e) (hf : zeroFreshEdge e ≠ true) :
    physicalPrime N (edgePrimes e 0) ≤ height r.node.physical := by
  let P := r.node.physical
  let x := edgeCoordinates e 0
  have hfit := hc.cutoff_fits
  change residual P ≤ P.argument*P.ceiling at hfit
  have hs : 0 < P.argument := by
    by_contra! h
    exact hc.residual_pos.not_ge (hfit.trans (mul_nonpos_of_nonpos_of_nonneg h hc.ceiling_pos.le))
  have hL := hc.residual_pos
  have moving (hx : 0<x) (hh : P.argument-1 ≤ residual P/x-1) : x ≤ height P := by
    apply (le_div_iff₀ hs).mpr
    have hh' := (le_div_iff₀ hx).mp (show P.argument ≤ residual P/x by linarith only [hh])
    simpa only [mul_comm] using hh'
  have fixed {v : ℝ} (hv : P.argument ≤ v) (hh : x/residual P < 1/v) : x ≤ height P := by
    have hv0 := hs.trans_le hv
    have hcross := (div_lt_div_iff₀ hL hv0).mp hh
    have hxv := (lt_div_iff₀ hv0).mpr (by simpa only [one_mul] using hcross)
    exact hxv.le.trans (div_le_div_of_nonneg_left hL.le hs hv)
  have hd := ad.2.1
  change x ≤ height P
  cases e with
  | retained i => exact False.elim (hf rfl)
  | w1Fixed i j => exact False.elim (hf rfl)
  | w2Fixed j b => exact False.elim (hf rfl)
  | buchstab up q =>
      cases up with
      | false => exact moving hd.2.2.1.1 hd.2.2.2.1
      | true => exact moving hd.2.1.1 ((le_max_right 2 _).trans hd.2.2.1)
  | w1Prime i j q => exact fixed hd.2.2.2.1 hd.2.2.1.2
  | w2Prime j l q => exact fixed hd.2.2.2.1 (singleton_below_target j l hd.2.2.1)
  | w2Pair j l q => exact fixed hd.2.2.2.1 (pair_below_target j l hd.2.2.1)

private theorem fresh_edge_small {N g : ℕ} {r : Request} {Q : ℝ} {e : Edge N}
    (hc : Coherent N Q r) (hh : height r.node.physical ≤ a)
    (he : e ∈ children N Q g r) (hf : zeroFreshEdge e ≠ true) :
    ∃ q ∈ appendedWord (edgeShape e) (edgePrimes e), q.Prime ∧ (q:ℝ)<(N:ℝ)^a := by
  let q := edgePrimes e 0
  have hm : q ∈ appendedWord (edgeShape e) (edgePrimes e) := by
    cases e with
    | buchstab u p => cases u <;> simp [q,appendedWord,edgeShape,edgePrimes]
    | _ => simp_all [q,appendedWord,edgeShape,edgePrimes,zeroFreshEdge]
  have ad := child_admission hc he
  obtain ⟨hq,hcop⟩ := ad.2.2 q hm
  have hpow : (N:ℝ)^physicalPrime N q = q :=
    actualPrimeTupleLog_rpow hc.target_gt_one (fun _ : Fin 1 => q) (fun _ => hq.pos) 0
  have hle : (q:ℝ) ≤ (N:ℝ)^a := by
    rw [←hpow]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hc.target_gt_one.le : (1:ℝ) ≤ N) ((first_coordinate_le hc ad hf).trans hh)
  exact ⟨q,hm,hq,P5OriginalCoprimeRationalEndpoint.original_cutoff_strict hq hcop hle⟩

private theorem letter_dvd {q : ℕ} {xs : List ℕ} (h : q∈xs) : q∣xs.prod := by
  induction xs with
  | nil => cases h
  | cons u xs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact dvd_mul_right _ _
      · exact (ih h).trans (dvd_mul_left _ _)

private theorem fresh_path_small {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (hc : Coherent N Q r) (hh : height r.node.physical ≤ a)
    (hs : ChosenPath N Q g r es) (hf : es.all zeroFreshEdge ≠ true) :
    ∃ q, q.Prime ∧ q ∣ (freshWord es).prod ∧ (q:ℝ)<(N:ℝ)^a := by
  induction es generalizing r g with
  | nil => exact False.elim (hf rfl)
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hs
      | succ g =>
          rw [freshWord,List.prod_append]
          by_cases he : zeroFreshEdge e = true
          · have hh' : height (nextRequest r e).node.physical ≤ a :=
              (perform_height_le hc.ceiling_pos hc.cutoff_fits (child_admission hc hs.1).2.1).trans hh
            have hf' : es.all zeroFreshEdge ≠ true := fun h => hf (by simp [he,h])
            obtain ⟨q,hq,hd,ha⟩ := ih (child_coherent hc hs.1) hh' hs.2 hf'
            exact ⟨q,hq,hd.trans (dvd_mul_left _ _),ha⟩
          · obtain ⟨q,hq,hp,ha⟩ := fresh_edge_small hc hh hs.1 he
            exact ⟨q,hp,(letter_dvd hq).trans (dvd_mul_right _ _),ha⟩

/-- Every post-fresh position of either actual root carries a strict small
prime in D, including all descendants after the first such edge. -/
theorem fresh_tail_small {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (ho : o∈rootHistory N n k t p) (hf : o.path.all zeroFreshEdge ≠ true) :
    ∃ q, q.Prime ∧ q ∣ tailProduct o ∧ (q:ℝ)<(N:ℝ)^a := by
  have hc := root_coherent (by omega : 1<N) ht hu hn (original_band_prime hp) (original_band_geometry hN hp)
  have hroot : origin 430 (rootRequest N n k t p) ∈ rootHistory N n k t p := List.mem_cons_self
  have hh := rootHistory_height_le hN ht hu hn hp hroot
  have hword : o.current.old = [p] ++ freshWord o.path := by
    rw [(history_facts ho).2.2,replay_old_word]; rfl
  have hf' := fresh_path_small hc hh (history_facts ho).1 hf
  simpa only [tailProduct,hword,List.singleton_append,List.tail_cons] using hf'

/-- The original root population is either passed in its entirety or absent.
The complementary unrestricted rough count at a fresh vertex is the entire
rejected population, at every cutoff z; it need not be small. -/
theorem fresh_rejection_exact {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (ho : o∈rootHistory N n k t p)
    (hf : o.path.all zeroFreshEdge ≠ true) (z : ℝ) :
    originalReceiptLane N p (tailProduct o) z = ∅ ∧
    inheritedChild N (parentProduct o.current.old) (tailProduct o) z = ∅ ∧
    rejectedChild N (parentProduct o.current.old) (tailProduct o) z =
      chenSiftedQuotientPrimeSource N (parentProduct o.current.old) z := by
  obtain ⟨q,hq,hd,ha⟩ := fresh_tail_small hN ht hu hn hp ho hf
  have hi : inheritedChild N (parentProduct o.current.old) (tailProduct o) z = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_le_of_gt ha) ((mem_filter.mp hx).2.1 q hq hd)
  exact ⟨originalReceiptLane_empty_of_small z hq hd ha,hi,by simp [rejectedChild,hi]⟩

/-- A theorem for each ORIGINAL q, with no test on its next prime factor.
The first two physical cutoffs may coincide; both are retained by the
root roughness in the fixed/retained case. -/
theorem all_receipt_at_position {N n m p q : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) (hq : q∈originalReceiver N p) (ho : o∈rootHistory N n k t p) :
    receiptPoint (cellQ N n c.1) q o = occurrenceBudget o := by
  have hb := (mem_filter.mp hp).1
  have hrough := (mem_filter.mp hq).2
  have hz := member_cutoff_le_original hN ht hu hn hb ho
  rw [←(original_fibre_geometry hN ht hu hn hp).1] at hz
  have hi : (tailProduct o ∣ q ∧ ChenPrimeRough (memberCutoff (cellQ N n c.1) o) (q/tailProduct o)) ↔
      o.path.all zeroFreshEdge = true := by
    constructor
    · intro h
      by_contra hf
      obtain ⟨u,hu',hd,ha⟩ := fresh_tail_small hN ht hu hn hb ho hf
      exact (not_le_of_gt ha) (hrough u hu' (hd.trans h.1))
    · intro hf
      have hD : tailProduct o = 1 := by simp [tailProduct,zeroFresh_original_word ho hf]
      rw [hD,Nat.div_one]
      exact ⟨one_dvd _,fun v hv hd => hz.trans (hrough v hv hd)⟩
  unfold receiptPoint occurrenceBudget
  rw [hi]

private theorem occurrence_sum {N : ℕ} (xs : List (Occurrence N)) :
    (xs.map occurrenceBudget).sum = listBudget xs := by
  induction xs with
  | nil => rfl
  | cons o os ih => simp only [List.map_cons,List.sum_cons,listBudget,ih]

theorem all_receipt_incidence {N n m p q : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) (hq : q∈originalReceiver N p) :
    receiptIncidence (cellQ N n c.1) q (rootHistory N n k t p) =
      listBudget (rootHistory N n k t p) := by
  unfold receiptIncidence
  rw [←occurrence_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  exact fun o ho => all_receipt_at_position hN ht hu hn hp hq ho

/-- Exact marked list sum on the pre-existing compatibleTotal, with all
overlapping roots and repeated positions interpreted inside their own key. -/
theorem compatibleTotal_exact {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) :
    compatibleTotal N n m k t c p =
      listBudget (rootHistory N n k t p) * ((originalReceiver N p).card:ℝ) := by
  rw [compatibleTotal_on_receipts hN ht hu hn hp]
  calc
    _ = ∑ _q ∈ originalReceiver N p, listBudget (rootHistory N n k t p) := by
      apply sum_congr rfl
      exact fun q hq => all_receipt_incidence hN ht hu hn hp hq
    _ = _ := by simp [mul_comm]

theorem root_listBudget_pos (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) :
    0 < listBudget (rootHistory N n k t p) := by
  change 0 < occurrenceBudget (origin (N:=N) 430 (rootRequest N n k t p)) + listBudget _
  rw [occurrenceBudget_origin]
  have H (xs : List (Occurrence N)) : 0 ≤ listBudget xs := by
    induction xs with
    | nil => exact le_rfl
    | cons o os ih => exact add_nonneg (occurrenceBudget_nonneg o) ih
  exact add_pos_of_pos_of_nonneg zero_lt_one (H _)

/-- This simultaneous bound improves the old 105-branch coarse factor
on the COMPLETE compatible population of the classical U3 root. -/
theorem classical_all_receipts_paid {t ε : ℝ} (ht : 0<t) (hu : t≤1/12) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1)≤11/384 →
      (∑ c : RootKey n m, ∑ p∈classicalFibre N n m t c, compatibleTotal N n m .U3 t c p)
      ≤ 431*(1+ε)*classicalOwnTheta N n m t := by
  filter_upwards [classical_original_card_bound ht hu he,eventually_ge_atTop (2:ℕ)] with N H hN
  intro hev n m hn
  calc
    _ ≤ ∑ c : RootKey n m, ∑ p∈classicalFibre N n m t c, 431*((originalReceiver N p).card:ℝ) := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro p hp
      rw [compatibleTotal_exact hN ht.le hu hn (classicalFibre_subset_rootFibre c hp)]
      exact mul_le_mul_of_nonneg_right (zeroFresh_rootHistory_budget N n .U3 t p) (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [sum_classicalFibre,←mul_sum,classicalOwnTheta_eq hN ht.le hu hn,mul_assoc]
      exact mul_le_mul_of_nonneg_left (H hev n hn) (by positivity)

end
end ImbalancedChen.Part5OriginalH430AllOriginalReceiptIncidence
