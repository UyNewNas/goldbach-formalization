import ImbalancedChen.Part5OriginalH430HistoryQuotientCounts

/-! Original U3/U4 root counts on finite, labelled, common-Q families.
A query mesh refines the actual 430 owner. The right query stays inside
its specified closed cell, fixes a structural clamp at two and keeps the
exterior fibre. Buchstab's exact least-prime shell accounts for the
difference between the original and frozen, common-query cutoffs. -/

namespace ImbalancedChen.Part5OriginalH430OwnedRootCounts

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells
open P2Selected430CausalOccurrenceExporter (iterate queryCell)
open P2EnhancedLowerPhysicalTransition (gridArgument)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentProduct residualLevel)
open P2EnhancedLowerPrimeChildGeometry (parentWindow_logs)
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab markedPhi)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedOriginalRowFreeze Part5OriginalH430TaggedArithmeticReceivers
open Wu2008DoubleSieve (primeWindow)

/-- Both coordinates are finite. The first code fixes Q, the optional
index is the literal scalar owner at generation 430, and the boolean
records the actual structural clamp. The last code keeps every earlier
auxiliary precision as well as its current interval. -/
abbrev RootKey (n m : ℕ) := RootCode n × Option (Fin 200) × Bool × RootCode m

def keyAt (N n m : ℕ) (k : Root) (t : ℝ) (p : ℕ) : RootKey n m :=
  let r := rootRequest N n k t p
  let s := r.node.physical.argument
  (rootCode n (sourceRoot k t (physicalPrime N p)).physical.total,
    resolve 430 r, if s = 2 then true else false,
    fun j => exponentCode 1 6 j.val s)

def rootFibre (N n m : ℕ) (k : Root) (t : ℝ) (c : RootKey n m) : Finset ℕ :=
  (originalBand N k).filter (fun p => keyAt N n m k t p = c)

/-- At fixed frozen root level, increasing the auxiliary query precision
keeps the old label, root Q, generation-430 owner and structural clamp. -/
theorem root_fibre_query_refines {N n m M : ℕ} {k : Root} {t : ℝ}
    (hm : m ≤ M) (c : RootKey n M) :
    rootFibre N n M k t c ⊆
      rootFibre N n m k t (c.1, c.2.1, c.2.2.1, restrictRootCode hm c.2.2.2) := by
  intro p hp
  obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hb, ?_⟩
  rw [← hc]
  rfl

private def ownerRight : Option (Fin 200) → ℝ
  | none => 6
  | some i => gridArgument i

private def meshRight (m : ℕ) : CellCode m → ℝ
  | none => 6
  | some i => logPrimeMeshPoint 1 6 m (i.val + 1)

def queryAt {n m : ℕ} (c : RootKey n m) : ℝ :=
  if c.2.2.1 then 2 else
    min (ownerRight c.2.1) (meshRight m (c.2.2.2 (Fin.last m)))

private theorem mesh_endpoint {m : ℕ} {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 6) :
    s ≤ meshRight m (exponentCode 1 6 m s) ∧
      meshRight m (exponentCode 1 6 m s) ≤ s + logPrimeMeshStep 1 6 m := by
  have h := exponentCode_membership (m := m) hs
  cases he : exponentCode 1 6 m s with
  | none =>
      rw [he] at h
      have hs6 : s = 6 := h
      rw [hs6]
      exact ⟨le_rfl, le_add_of_nonneg_right (logPrimeMeshStep_pos (by norm_num) m).le⟩
  | some j =>
      rw [he] at h
      change s ≤ logPrimeMeshPoint 1 6 m (j.val + 1) ∧
        logPrimeMeshPoint 1 6 m (j.val + 1) ≤ s + logPrimeMeshStep 1 6 m
      exact ⟨h.2.le, (logPrimeMeshPoint_succ 1 6 m j.val).le.trans
        (add_le_add_right h.1 _)⟩

/-- The generation-430 scalar resolver selects the original closed cell.
The source argument and the one-sided comparison endpoint both belong
to that cell. The lookup in the conclusion is at the source argument. -/
theorem original_fibre_geometry {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p ∈ rootFibre N n m k t c) :
    let r := rootRequest N n k t p
    let s := r.node.physical.argument
    cellQ N n c.1 = rootQ N n k t p ∧
      s ≤ queryAt c ∧ queryAt c ≤ s + logPrimeMeshStep 1 6 m ∧
      (s = 2 → queryAt c = 2) ∧
      (∀ i, c.2.1 = some i → s ∈ queryCell i ∧ queryAt c ∈ queryCell i ∧
        requestValue (iterate 430) r = Part5OriginalUpsilon5CausalDictionary.floorValue
          (iterate 430 true) i) ∧
      (c.2.1 = none → requestValue (iterate 430) r = 0) := by
  obtain ⟨hband, hkey⟩ := Finset.mem_filter.mp hp
  subst c
  let r := rootRequest N n k t p
  let s := r.node.physical.argument
  have hb := original_band_geometry hN hband
  have hs : s ∈ Set.Icc (1 : ℝ) 6 := frozenRoot_argument_bounds ht ht' hb hn
  have hm := mesh_endpoint (m := m) hs
  have hnum : s ≤ ownerRight (resolve 430 r) := by
    cases ho : resolve 430 r with
    | none => exact hs.2
    | some i =>
        have hi := resolve_contains (r := r) (show ReadValid r from trivial) ho
        exact hi.2
  have hQ : cellQ N n (rootCode n (sourceRoot k t (physicalPrime N p)).physical.total) =
      rootQ N n k t p := by
    rw [cellQ, codeLevel_rootCode]
    rfl
  have hquery : queryAt (keyAt N n m k t p) =
      if s = 2 then 2 else min (ownerRight (resolve 430 r))
        (meshRight m (exponentCode 1 6 m s)) := by
    change (if (if s = 2 then true else false) then 2 else _) = _
    by_cases h : s = 2 <;> simp [h]
  have hleft : s ≤ queryAt (keyAt N n m k t p) := by
    rw [hquery]
    split_ifs with h
    · exact h.le
    · exact le_min hnum hm.1
  have hright : queryAt (keyAt N n m k t p) ≤ s + logPrimeMeshStep 1 6 m := by
    rw [hquery]
    split_ifs with h
    · rw [h]
      exact le_add_of_nonneg_right (logPrimeMeshStep_pos (by norm_num) m).le
    · exact (min_le_right _ _).trans hm.2
  dsimp only
  refine ⟨hQ, hleft, hright, ?_, ?_, ?_⟩
  · intro h2
    rw [hquery, if_pos h2]
  · intro i hi
    change resolve 430 r = some i at hi
    have hsCell := resolve_contains (r := r) (show ReadValid r from trivial) hi
    refine ⟨hsCell, ?_, resolve_value hi⟩
    refine ⟨hsCell.1.trans hleft, ?_⟩
    rw [hquery]
    split_ifs with h
    · rw [← h]
      exact hsCell.2
    · rw [hi]
      exact min_le_left _ _
  · intro hnone
    exact resolve_none_value hnone

private theorem original_prefix_rough {N p : ℕ} {k : Root} (hp : p ∈ originalBand N k) :
    ChenPrimeRough ((N : ℝ) ^ a) p := by
  have hpr := (original_band_prime hp).1
  have hl : (N : ℝ) ^ a ≤ (p : ℝ) := by
    cases k <;> exact (Finset.mem_filter.mp hp).2.1
  intro q hq hqp
  rwa [(Nat.prime_dvd_prime_iff_eq hq hpr).mp hqp]

/-- Actual extra least prime from making the common physical cutoff
smaller. Finite prime windows keep the original strict endpoint rule. -/
def firstPrimeMass (N : ℕ) (Q w : ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ primeWindow (p * N) (cutoff Q p w) ((N : ℝ) ^ a),
    (frozenCount N (p * q) (receiver N) (q : ℝ) : ℝ)

theorem firstPrimeMass_nonneg (N : ℕ) (Q w : ℝ) (p : ℕ) :
    0 ≤ firstPrimeMass N Q w p := by
  unfold firstPrimeMass
  apply Finset.sum_nonneg
  intro q _
  unfold frozenCount
  positivity

/-- At one preassigned finite root class a genuine common-Q marked
source counts the selected quotients and its positive first-prime shell.
No map from q to a bank edge, choice of depth, seed gain or defect bound
enters the equality. -/
theorem owned_root_marked_count_exact {N n m : ℕ} (k : Root) (t : ℝ)
    (c : RootKey n m) (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) :
    markedPhi N (cellQ N n c.1) (rootFibre N n m k t c) id (fun _ => 1)
        (fun _ => receiver N) (queryAt c) =
      (∑ p ∈ rootFibre N n m k t c, ((originalReceiver N p).card : ℝ)) +
      ∑ p ∈ rootFibre N n m k t c, firstPrimeMass N (cellQ N n c.1) (queryAt c) p := by
  rw [markedPhi, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hb := (Finset.mem_filter.mp hp).1
  have hgeo := original_fibre_geometry hN ht ht' hn hp
  let s := (rootRequest N n k t p).node.physical.argument
  have hs : s ∈ Set.Icc (1 : ℝ) 6 :=
    frozenRoot_argument_bounds ht ht' (original_band_geometry hN hb) hn
  have hR : 1 < rootQ N n k t p / (p : ℝ) := by
    have hw := coherent_window (root_coherent (by omega : 1 < N) ht ht' hn
      (original_band_prime hb) (original_band_geometry hN hb))
    simpa only [residualLevel, rootRequest, parentProduct, List.prod_cons,
      List.prod_nil, mul_one] using (parentWindow_logs hw).2.1
  have hcut : cutoff (cellQ N n c.1) p (queryAt c) ≤ (N : ℝ) ^ a := by
    rw [hgeo.1]
    calc
      cutoff (rootQ N n k t p) p (queryAt c) ≤ cutoff (rootQ N n k t p) p s :=
        Real.rpow_le_rpow_of_exponent_le hR.le
          (one_div_le_one_div_of_le (zero_lt_one.trans_le hs.1) hgeo.2.1)
      _ ≤ (N : ℝ) ^ a := by
        unfold cutoff
        rw [frozen_root_sameQ_cutoff_power N n p k t hN (original_band_prime hb).1.pos
          ht ht' (original_band_geometry hN hb) hn]
        exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (min_le_left _ _)
  have hh := frozen_selected_buchstab N p (receiver N) hcut
  have hRhs :
      (frozenCount N p (receiver N) (cutoff (cellQ N n c.1) p (queryAt c)) : ℝ) =
      (frozenCount N p (receiver N) ((N : ℝ) ^ a) : ℝ) +
        firstPrimeMass N (cellQ N n c.1) (queryAt c) p := by
    unfold firstPrimeMass
    exact_mod_cast hh
  rw [frozenCount_eq_original_count N p ((N : ℝ) ^ a) (original_prefix_rough hb)] at hRhs
  simpa only [id_eq, one_mul, originalReceiver] using hRhs

/-- Removing the nonnegative first-prime shell gives the one-sided
original-count entrance on each same-Q, same-owner finite root family. -/
theorem owned_original_count_le_marked {N n m : ℕ} (k : Root) (t : ℝ)
    (c : RootKey n m) (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) :
    (∑ p ∈ rootFibre N n m k t c, ((originalReceiver N p).card : ℝ)) ≤
      markedPhi N (cellQ N n c.1) (rootFibre N n m k t c) id (fun _ => 1)
        (fun _ => receiver N) (queryAt c) := by
  rw [owned_root_marked_count_exact k t c hN ht ht' hn]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun p _ => firstPrimeMass_nonneg _ _ _ p))

/-- The selected cell's actual generation-430 numerator. A nonempty
exterior class has zero table read and still contributes its full count. -/
def ownerFloor {n m : ℕ} (c : RootKey n m) : ℝ :=
  match c.2.1 with
  | some i => Part5OriginalUpsilon5CausalDictionary.floorValue (iterate 430 true) i
  | none => 0

/-- On the actual marked root family the coefficient of the 430 floor
is precisely the physical Theta of its prefix primes. Each p carries
weight one in the family and its own singular, totient and logarithmic
factors in Theta. -/
theorem owned_root_theta_floor_exact {N n m : ℕ} (k : Root) (t : ℝ)
    (c : RootKey n m) (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) :
    P2EnhancedTwentyOneSameQWeighted.Theta N (cellQ N n c.1) (rootFibre N n m k t c)
        (fun _ => 1) * ownerFloor c =
      ∑ p ∈ rootFibre N n m k t c, P2OriginalChildPhysicalNormalization.thetaAtom N
        (rootQ N n k t p) p * requestValue (iterate 430) (rootRequest N n k t p) := by
  rw [P2OriginalChildPhysicalNormalization.Theta_eq_sum_atoms, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have h := original_fibre_geometry hN ht ht' hn hp
  have hread : requestValue (iterate 430) (rootRequest N n k t p) = ownerFloor c := by
    cases hi : c.2.1 with
    | none => simpa only [ownerFloor, hi] using h.2.2.2.2.2 hi
    | some i => simpa only [ownerFloor, hi] using (h.2.2.2.2.1 i hi).2.2
  rw [h.1, hread, one_mul]

def ownedRootCount (N n m : ℕ) (k : Root) (t : ℝ) : ℝ :=
  ∑ c : RootKey n m,
    (markedPhi N (cellQ N n c.1) (rootFibre N n m k t c) id (fun _ => 1)
      (fun _ => receiver N) (queryAt c) -
     ∑ p ∈ rootFibre N n m k t c, firstPrimeMass N (cellQ N n c.1) (queryAt c) p)

/-- The two original overlapping labels retain their separate full source
weights. The same fixed finite set of keys works before the prime target. -/
theorem original_U34_eq_owned_root_counts (N n m : ℕ) (t : ℝ) (hN : 2 ≤ N)
    (ht : 0 ≤ t) (ht' : t ≤ 1/12) (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      ownedRootCount N n m .U3 t + ownedRootCount N n m .U4 t := by
  have h (k : Root) : ownedRootCount N n m k t =
      ∑ p ∈ originalBand N k, ((originalReceiver N p).card : ℝ) := by
    unfold ownedRootCount
    simp_rw [owned_root_marked_count_exact k t _ hN ht ht' hn, add_sub_cancel_right]
    exact Finset.sum_fiberwise_of_maps_to (s := originalBand N k)
      (t := Finset.univ) (g := keyAt N n m k t) (fun _ _ => Finset.mem_univ _)
      (fun p => ((originalReceiver N p).card : ℝ))
  rw [h, h, original_U34_eq_tagged_card, original_tagged_card]
  simp only [Nat.cast_add, Nat.cast_sum]

end
end ImbalancedChen.Part5OriginalH430OwnedRootCounts

