import ImbalancedChen.Part5OriginalH430ReceiptDirections
import ImbalancedChen.Part5OriginalH430StrictPhysicalOccurrences

/-! The actual U3/U4 resolver, including generation zero and unresolved exterior
requests, on one positive family. The auxiliary query mesh only partitions original
list positions. Its right endpoint has a preassigned error at every position. -/
namespace ImbalancedChen.Part5OriginalH430AllLaneMemberQuery

noncomputable section
open scoped Classical BigOperators
open Set
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2Selected430CausalOccurrenceExporter (queryCell)
open Wu2008DoubleSieve AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedMemberBox Part5OriginalH430SelectedMemberFixedQuery
open Part5OriginalH430AllEmittedReceiptLanes Part5OriginalH430ReceiptDirections
open Part5OriginalH430RootSourceDictionary Part5OriginalH430ActualMemberStrictCover
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430StrictPhysicalOccurrences

abbrev Key (mesh fine : ℕ) := (Box mesh × Lane) × CellCode fine

def requestKey {N n p G : ℕ} {k : Root} {t : ℝ} (mesh fine : ℕ)
    (l : LevelIndex N n k t p G) : Key mesh fine :=
  let r := (levelOccurrence l).current
  ((atBox mesh l, laneAt G r), exponentCode 1 6 fine r.node.physical.argument)

abbrev Position (N n : ℕ) (k : Root) (t : ℝ) (G : Fin 431) :=
  (p : ℕ) × LevelIndex N n k t p G.val

def allAt {N n m : ℕ} (k : Root) (t : ℝ) (G : Fin 431) (c : RootKey n m) :
    Finset (Position N n k t G) :=
  (rootFibre N n m k t c).sigma (fun _ => Finset.univ)

def atKey {N n m mesh fine : ℕ} (k : Root) (t : ℝ) (G : Fin 431) (c : RootKey n m)
    (u : Key mesh fine) :=
  (allAt (N:=N) k t G c).filter (fun a => requestKey mesh fine a.2 = u)

theorem key_partition {N n m : ℕ} (mesh fine : ℕ) (k : Root) (t : ℝ) (G : Fin 431)
    (c : RootKey n m) (f : Position N n k t G → ℝ) :
    (∑ u : Key mesh fine, ∑ a ∈ atKey k t G c u, f a) =
      ∑ p ∈ rootFibre N n m k t c, ∑ l : LevelIndex N n k t p G.val, f ⟨p,l⟩ := by
  calc
    _ = ∑ a ∈ allAt k t G c, f a :=
      Finset.sum_fiberwise_of_maps_to (s := allAt k t G c) (t := Finset.univ)
        (g := fun a => requestKey mesh fine a.2) (fun _ _ => Finset.mem_univ _) f
    _ = _ := by rw [allAt,Finset.sum_sigma]

def meshRight (m : ℕ) : CellCode m → ℝ
  | none => 6
  | some j => logPrimeMeshPoint 1 6 m (j.val+1)

def query {mesh fine : ℕ} (u : Key mesh fine) : ℝ :=
  if u.1.1.1.2 then 2 else min (fixedQuery u.1.1) (meshRight fine u.2)

private theorem mesh_bracket {s : ℝ} (hs : s ∈ Icc (1:ℝ) 6) (m : ℕ) :
    s ≤ meshRight m (exponentCode 1 6 m s) ∧
      meshRight m (exponentCode 1 6 m s) ≤ s + logPrimeMeshStep 1 6 m := by
  have hm := exponentCode_membership (m:=m) hs
  cases hc : exponentCode 1 6 m s with
  | none =>
    rw [hc] at hm
    have he : s = 6 := hm
    change s ≤ 6 ∧ 6 ≤ s + _
    rw [he]
    exact ⟨le_rfl,le_add_of_nonneg_right (logPrimeMeshStep_pos (by norm_num) m).le⟩
  | some i =>
    rw [hc] at hm
    change s ∈ Ico (logPrimeMeshPoint 1 6 m i.val) (logPrimeMeshPoint 1 6 m (i.val+1)) at hm
    exact ⟨hm.2.le,(logPrimeMeshPoint_succ 1 6 m i.val).le.trans (add_le_add_right hm.1 _)⟩

/-- A specified-cell request keeps its resolver owner even at a shared endpoint.
The undefined owner is allowed. Its preselected fine cell still controls movement. -/
theorem owned_query {N n m mesh fine : ℕ} {k : Root} {t : ℝ} {G : Fin 431}
    {c : RootKey n m} {u : Key mesh fine} {a : Position N n k t G}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (ha : a ∈ atKey k t G c u) :
    let r := (levelOccurrence a.2).current
    u.1.1.2.2 = resolve G.val r ∧ u.1.2 = laneAt G.val r ∧
    (∀ i, u.1.1.2.2 = some i → r.node.physical.argument ∈ queryCell i) ∧
    r.node.physical.argument ≤ query u ∧
    query u ≤ r.node.physical.argument + logPrimeMeshStep 1 6 fine ∧
    (r.node.physical.argument = 2 → query u = 2) := by
  obtain ⟨hm,hkey⟩ := Finset.mem_filter.mp ha
  subst u
  have hp := (Finset.mem_filter.mp (Finset.mem_sigma.mp hm).1).1
  have ho := (levelOccurrence_source a.2).1
  have hs := (rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) ho).2.2.2.1
  have hv := (rootHistory_computed_data ho).2.2.1
  let r := (levelOccurrence a.2).current
  let s := r.node.physical.argument
  have hm' := mesh_bracket (s:=s) hs fine
  refine ⟨rfl,rfl,fun i hi => resolve_contains hv hi,?_⟩
  by_cases h : s = 2
  · have hq : query (requestKey mesh fine a.2) = 2 := by
      change (if decide (s=2) then (2:ℝ) else _) = 2
      simp [h]
    exact ⟨h.le.trans_eq hq.symm,
      hq.le.trans (by rw [show (levelOccurrence a.2).current.node.physical.argument = 2 from h]
                       exact le_add_of_nonneg_right (logPrimeMeshStep_pos (by norm_num) fine).le),
      fun _ => hq⟩
  · have hq : query (requestKey mesh fine a.2) =
        min (fixedQuery (atBox mesh a.2)) (meshRight fine (exponentCode 1 6 fine s)) := by
      change (if decide (s = 2) then (2:ℝ) else _) = _
      simp [h]
    have hc : s ≤ fixedQuery (atBox mesh a.2) := by
      change s ≤ if decide (s=2) then 2 else
        match resolve G.val r with | none => 6 | some i => gridArgument i
      simp only [h,decide_false,Bool.false_eq_true,if_false]
      cases hi : resolve G.val r with
      | none => exact hs.2
      | some i => exact (resolve_contains hv hi).2
    rw [hq]
    exact ⟨le_min hc hm'.1,(min_le_right _ _).trans hm'.2,fun he => (h he).elim⟩

private theorem replay_append {N : ℕ} (r : Request) (xs ys : List (Edge N)) :
    replay r (xs ++ ys) = replay (replay r xs) ys := by
  induction xs generalizing r with
  | nil => rfl
  | cons e xs ih => exact ih (nextRequest r e)

/-- Every actual earlier marked prefix survives both full and selected filtering.
The selected integer at the real U3/U4 root stays in its original slot. -/
theorem inherited_prefix {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (ho : o ∈ rootHistory N n k t p) (xs ys : List (Edge N)) (hpath : o.path = xs ++ ys) :
    let v := (replay (rootRequest N n k t p) xs).node.physical
    let w := o.current.node.physical
    w.slots.take v.slots.length = v.slots ∧
    selectedWord (w.slots.take v.slots.length) = selectedWord v.slots ∧
    remainingWord (w.slots.take v.slots.length) = remainingWord v.slots ∧
    selectedWord w.slots = [physicalPrime N p] := by
  refine ⟨?_,?_,?_,rootHistory_selected_root ho⟩
  all_goals
    rw [(history_facts ho).2.2,hpath,replay_append]
    obtain ⟨z,hz⟩ := replay_slots_prefix (replay (rootRequest N n k t p) xs) ys
    simp [hz]

/-- The original finite atom is strictly positive at each occupied position.
Repeated occurrences with the same product each retain their own mark. -/
theorem occupied_atom_pos {N n m : ℕ} {k : Root} {t : ℝ} {G : Fin 431}
    {c : RootKey n m} {a : Position N n k t G} (hN : 4 ≤ N) (ht : 0 ≤ t)
    (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) (ha : a ∈ allAt k t G c) :
    0 < levelMark a.2 * thetaAtom N (cellQ N n c.1) (parentProduct (levelOccurrence a.2).current.old) := by
  have hp := (Finset.mem_sigma.mp ha).1
  have hb := (Finset.mem_filter.mp hp).1
  have geo := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hb)
    (original_band_geometry (by omega) hb) (levelOccurrence_source a.2).1
  rw [(original_fibre_geometry (by omega : 2≤N) ht hu hn hp).1]
  apply mul_pos (mark_pos _)
  let B := parentProduct (levelOccurrence a.2).current.old
  have hB : 0 < B := geo.1.2.1
  have hQ : 1 < rootQ N n k t a.1 / (B:ℝ) := (parentWindow_logs geo.1).2.1
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hNp : 0 < N := by omega
  have hli : 0 < logarithmicIntegral N :=
    (div_pos (Nat.cast_pos.mpr hNp) (mul_pos (by norm_num) (Real.log_pos hNr))).trans_le (box_trueLi_lower hN)
  have hden := mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hB)) (Real.log_pos hQ)
  have hser := wuSingularSeries_pos (B*N) (Nat.mul_pos hB hNp)
  change 0 < 4 * logarithmicIntegral N *
    (wuSingularSeries (B*N) / ((Nat.totient B:ℝ)*Real.log (rootQ N n k t a.1 / (B:ℝ))))
  exact mul_pos (mul_pos (by norm_num) hli) (div_pos hser hden)

def mass {N n m mesh fine : ℕ} (k : Root) (t : ℝ) (G : Fin 431) (c : RootKey n m)
    (u : Key mesh fine) : ℝ :=
  ∑ a ∈ atKey (N:=N) k t G c u, levelMark a.2 *
    thetaAtom N (cellQ N n c.1) (parentProduct (levelOccurrence a.2).current.old)

theorem mass_pos_iff {N n m mesh fine : ℕ} (k : Root) {t : ℝ} (G : Fin 431)
    (c : RootKey n m) (u : Key mesh fine) (hN : 4≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    0 < mass (N:=N) k t G c u ↔ (atKey (N:=N) k t G c u).Nonempty := by
  classical
  constructor
  · intro h
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    simp [mass,he] at h
  · intro he
    exact Finset.sum_pos (fun a ha =>
      occupied_atom_pos hN ht hu hn (Finset.mem_filter.mp ha).1) he

/-- Exact ordinary, selected and outside counts for one point of every lane,
with the original mask at both cutoffs. The two physical levels in the
statement coincide by root ownership. The additive prime never changes. -/
theorem all_lane_fixed_count {N n m mesh fine : ℕ} {k : Root} {t : ℝ} {G : Fin 431}
    {c : RootKey n m} {u : Key mesh fine} {a : Position N n k t G} (hN : 2≤N)
    (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) (ha : a ∈ atKey k t G c u) :
    let o := levelOccurrence a.2
    let Q := cellQ N n c.1
    let B := parentProduct o.current.old
    let z := cutoff Q B (query u)
    (frozenCount N B (receiver N) z : ℝ) =
      ((originalReceiptLane N a.1 (tailProduct o) (memberCutoff Q o)).card : ℝ) +
      queryShell Q a.1 o (query u) + (frozenCount N B (outsideReceipt N a.1) z : ℝ) := by
  dsimp only
  let o := levelOccurrence a.2
  let B := parentProduct o.current.old
  let Q := cellQ N n c.1
  have hp := (Finset.mem_sigma.mp (Finset.mem_filter.mp ha).1).1
  have hb := (Finset.mem_filter.mp hp).1
  have ho := (levelOccurrence_source a.2).1
  have hh := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hb)
    (original_band_geometry hN hb) ho
  have hQ : Q = rootQ N n k t a.1 := (original_fibre_geometry hN ht hu hn hp).1
  have hR : 1 < Q/(B:ℝ) := by rw [hQ]; exact (parentWindow_logs hh.1).2.1
  have hsw := (owned_query hN ht hu hn ha).2.2.2.1
  have hcut : cutoff Q B (query u) ≤ memberCutoff Q o :=
    Real.rpow_le_rpow_of_exponent_le hR.le
      (one_div_le_one_div_of_le (zero_lt_one.trans_le hh.2.2.2.1.1) hsw)
  have hs : (frozenCount N B (rootMask N a.1) (cutoff Q B (query u)) : ℝ) =
      (frozenCount N B (rootMask N a.1) (memberCutoff Q o) : ℝ) +
        queryShell Q a.1 o (query u) := by
    unfold queryShell
    exact_mod_cast frozen_selected_buchstab N B (rootMask N a.1) hcut
  have hfull := receiver_count_split N a.1 B (cutoff Q B (query u))
  change (frozenCount N B (receiver N) (cutoff Q B (query u)) : ℝ) = _
  rw [show (frozenCount N B (receiver N) (cutoff Q B (query u)) : ℝ) =
        (frozenCount N B (rootMask N a.1) (cutoff Q B (query u)) : ℝ) +
        (frozenCount N B (outsideReceipt N a.1) (cutoff Q B (query u)) : ℝ) from hfull,
    hs,owned_member_masked_count hN ht hu hn hp ho]

/-- All original marks are retained even when many positions have the same old product.
The identity also applies to a signed test of the history; in particular the
two compensating terms have the necessary direction for a lower child read. -/
theorem marked_fixed_count {N n m mesh fine : ℕ} (k : Root) {t : ℝ} (G : Fin 431)
    (c : RootKey n m) (u : Key mesh fine) (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (f : Position N n k t G → ℝ) :
    let Q := cellQ N n c.1
    (∑ a ∈ atKey (N:=N) k t G c u, f a * levelMark a.2 *
      (frozenCount N (parentProduct (levelOccurrence a.2).current.old) (receiver N)
        (cutoff Q (parentProduct (levelOccurrence a.2).current.old) (query u)) : ℝ)) =
    ∑ a ∈ atKey (N:=N) k t G c u, f a * levelMark a.2 *
      (((originalReceiptLane N a.1 (tailProduct (levelOccurrence a.2))
        (memberCutoff Q (levelOccurrence a.2))).card : ℝ) +
       queryShell Q a.1 (levelOccurrence a.2) (query u) +
       (frozenCount N (parentProduct (levelOccurrence a.2).current.old) (outsideReceipt N a.1)
        (cutoff Q (parentProduct (levelOccurrence a.2).current.old) (query u)) : ℝ)) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro a ha
  rw [all_lane_fixed_count hN ht hu hn ha]

/-- Geometric, arithmetic and immutable owner statements refer to the same
root and list position; the tester in the pullback can distinguish every q. -/
theorem occupied_member_source {N n m mesh fine : ℕ} {k : Root} {t : ℝ} {G : Fin 431}
    {c : RootKey n m} {u : Key mesh fine} {a : Position N n k t G}
    (hn : 111≤n) (hN : 4≤N) (ht : 0≤t) (hu : t≤1/12) (ha : a ∈ atKey k t G c u) :
    let o := levelOccurrence a.2
    let v := o.current.node.physical
    let Q := cellQ N n c.1
    Member 0 1 o.path.length (frozenRoot n k t (physicalPrime N a.1))
      (pathCode mesh o.path) (physicalCoordinates N (pathPrimes o.path)) ∧
    u.1.1.2.2 = resolve G.val o.current ∧ u.1.2 = laneAt G.val o.current ∧
    Q = rootQ N n k t a.1 ∧ parentProduct o.current.old = a.1 * tailProduct o ∧
    0 < levelMark a.2 * thetaAtom N Q (parentProduct o.current.old) ∧
    (rootSource k (physicalPrime N a.1) = .enhanced →
       strictSquares v.total 0 (word v) ∧
       strictSquares v.total (selectedWord v.slots).sum (remainingWord v.slots)) ∧
    (∀ f : ℕ → ℝ, (∑ q ∈ originalReceiptLane N a.1 (tailProduct o) (memberCutoff Q o), f q) =
       ∑ x ∈ inheritedChild N (parentProduct o.current.old) (tailProduct o)
         (memberCutoff (rootQ N n k t a.1) o), f (tailProduct o*x)) := by
  have hp := (Finset.mem_sigma.mp (Finset.mem_filter.mp ha).1).1
  have hb := (Finset.mem_filter.mp hp).1
  have h2 : 2≤N := by omega
  have hd := precision_error hn
  have ho := (levelOccurrence_source a.2).1
  have hq := owned_query h2 ht hu hd ha
  exact ⟨rootHistory_member mesh (by omega) ht hu hd (original_band_prime hb)
      (original_band_geometry h2 hb) ho,hq.1,hq.2.1,
    (original_fibre_geometry h2 ht hu hd hp).1,member_product ho,
    occupied_atom_pos hN ht hu hd (Finset.mem_filter.mp ha).1,
    fun he => enhanced_history_strict_physical hn h2 ht hu hb he ho,
    fun f => owned_member_receipt_pullback h2 ht hu hd hp ho f⟩

end
end ImbalancedChen.Part5OriginalH430AllLaneMemberQuery
