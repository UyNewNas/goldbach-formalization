import ImbalancedChen.Part5OriginalH430RetainedRejectedPayment
import ImbalancedChen.Part5OriginalH430ClassicalRootPriceGeometry
import ImbalancedChen.Part5OriginalH430PresieveOutsideFin
import ImbalancedChen.Part5OriginalH430SignedOriginalFinCapacityGap

/-! Rejected quotients at the actual classical U3 fixed reads.  The
common root shell stays at its own physical level.  The change of
cutoff has its actual finite Buchstab count in both directions.
Source only. -/
namespace ImbalancedChen.Part5OriginalH430FixedRejectedWindows
noncomputable section
open Finset Filter
open scoped Classical BigOperators Topology
open Wu2008DoubleSieve (primeWindow)
open P5OriginalActionMassBound
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPhysicalTransition
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430IntegerItineraries
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalRootThetaPayment Part5OriginalH430ClassicalRootCredits
open Part5OriginalH430ClassicalRootPriceGeometry (actual_classical_queries)
open Part5OriginalH430RootRosserSurplus (surplus)
open Part5OriginalH430ClassicalReceiverSubfamily
open Part5OriginalH430ZeroFreshReceiverPayment
open Part5OriginalH430ClassicalRejectedShell
open Part5OriginalH430RetainedRejectedPayment
open Part5OriginalH430PresieveOutsideFin

private theorem w2_fixed_three (j : Fin 36) (b : Bool) :
    3 ≤ (if b then (originalW2At j).s0 else (originalW2At j).phi1) := by
  obtain ⟨h0,h01,_,_,_,_,_,h3,_⟩ :=
    originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have bound (u : ℝ) (hu : 1/5 ≤ 1/u) (hv : 3*(1/u) ≤ 1) : 3 ≤ u := by
    have hpos : 0 < u := one_div_pos.mp ((by norm_num : (0:ℝ) < 1/5).trans_le hu)
    have hdiv : 3/u ≤ 1 := by simpa only [div_eq_mul_inv,one_mul] using hv
    simpa only [one_mul] using (div_le_iff₀ hpos).mp hdiv
  cases b with
  | false => exact bound _ (h0.trans h01) h3
  | true => exact bound _ h0 (by
      change 3 * a0 (originalW2At j) ≤ 1
      linarith only [h01,h3])

/-- A genuine fixed read sets its argument to at least three. Subsequent
retentions keep that physical node, including its argument. -/
private theorem after_fixed_three {N : ℕ} (r : Request) (es : List (Edge N))
    (hz : es.all zeroFreshEdge = true) (hr : es.all retainedEdge ≠ true) :
    3 ≤ (replay r es).node.physical.argument := by
  induction es generalizing r with
  | nil => exact False.elim (hr rfl)
  | cons e es ih =>
      have he : zeroFreshEdge e = true ∧ es.all zeroFreshEdge = true := by
        simpa only [List.all_cons,Bool.and_eq_true] using hz
      by_cases ht : es.all retainedEdge = true
      · have hne : retainedEdge e ≠ true := by
          intro h
          exact hr (by simp only [List.all_cons,h,ht,Bool.and_self])
        change 3 ≤ (replay (nextRequest r e) es).node.physical.argument
        rw [(retained_replay_state (nextRequest r e) es ht).2]
        cases e with
        | w1Fixed i j =>
            change (3:ℝ) ≤ 16/5+(j.val:ℝ)/5
            linarith only [Nat.cast_nonneg (α := ℝ) j.val]
        | w2Fixed j b => exact w2_fixed_three j b
        | _ => simp_all [retainedEdge,zeroFreshEdge]
      · exact ih (nextRequest r e) he.2 ht

/-- One finite half-open window, indexed by the actual first divisor
and counted on the original additive-prime population at modulus p*r. -/
def firstWindow (N p : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ r ∈ primeWindow (p*N) lo hi, (frozenCount N (p*r) (receiver N) (r:ℝ) : ℝ)

private theorem buchstab_window (N p : ℕ) {lo hi : ℝ} (h : lo ≤ hi) :
    (frozenCount N p (receiver N) lo : ℝ) =
      (frozenCount N p (receiver N) hi : ℝ) + firstWindow N p lo hi := by
  unfold firstWindow
  exact_mod_cast frozen_selected_buchstab N p (receiver N) h

/-- A retained-only position has the origin's cutoff. Every other
zero-fresh position has actually taken a fixed W1 or W2 read. -/
theorem fixed_cutoff_order {N n m p : ℕ} {τ : ℝ} {c : RootKey n m} {o : Occurrence N}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c)
    (ho : o ∈ rootHistory N n .U3 τ p) (hz : o.path.all zeroFreshEdge = true) :
    let z := memberCutoff (cellQ N n c.1) o
    let v := cutoffAt N n m p τ
    (o.path.all retainedEdge = true → v ≤ z ∧ z ≤ (N:ℝ)^a) ∧
    (o.path.all retainedEdge ≠ true → z ≤ v) := by
  dsimp only
  have hb := (Finset.mem_filter.mp hp).1
  have hb' := (Finset.mem_filter.mp hb).1
  have hQ := (original_fibre_geometry hN hτ hτ' hn (classicalFibre_subset_rootFibre c hp)).1
  have hw := zeroFresh_original_word ho hz
  have hcut : memberCutoff (cellQ N n c.1) o =
      cutoff (rootQ N n .U3 τ p) p o.current.node.physical.argument := by
    simp only [memberCutoff,hQ,hw,parentProduct,List.prod_cons,List.prod_nil,mul_one]
  constructor
  · intro hr
    have hs := (retained_replay_state (rootRequest N n .U3 τ p) o.path hr).2
    rw [← (history_facts ho).2.2] at hs
    rw [hcut,hs]
    exact ⟨common_cutoff_le_origin hN hτ hτ' hn hb,
      presieve_below_frozen_root hN hτ hτ' hn hb' le_rfl⟩
  · intro hr
    have hs := after_fixed_three (rootRequest N n .U3 τ p) o.path hz hr
    rw [← (history_facts ho).2.2] at hs
    obtain ⟨hs2,_,hsw,hw3⟩ := actual_classical_queries (m := m) hN hτ hτ' hn hb
    have hpos : 0 < queryAt (keyAt N n m .U3 τ p) := by linarith only [hs2,hsw]
    rw [hcut]
    unfold cutoffAt cutoff
    exact Real.rpow_le_rpow_of_exponent_le
      (classical_geometry (m := m) hN hτ hτ' hn hb).1.le
      (one_div_le_one_div_of_le hpos (hw3.trans hs))

def windowAt (N n m p : ℕ) (τ : ℝ) (c : RootKey n m) (o : Occurrence N) : ℝ :=
  let z := memberCutoff (cellQ N n c.1) o
  let v := cutoffAt N n m p τ
  if o.path.all retainedEdge then -firstWindow N p v z else firstWindow N p z v

def rootShell (N n m p : ℕ) (τ : ℝ) : ℝ :=
  cubeCredit N n p τ - surplus N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ)

/-- Actual unmasked and rejected counts at the same occurrence. Only the
common root shell consumes cube credit. The signed window is an actual
least-prime count, including the equality endpoint convention. -/
theorem fixed_row_balance {N n m p : ℕ} {τ : ℝ} {c : RootKey n m} {o : Occurrence N}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c)
    (ho : o ∈ rootHistory N n .U3 τ p) (hz : o.path.all zeroFreshEdge = true) :
    (frozenCount N p (receiver N) (memberCutoff (cellQ N n c.1) o) : ℝ) =
        ((originalReceiver N p).card : ℝ) + rejectedAt N (cellQ N n c.1) o ∧
    rejectedAt N (cellQ N n c.1) o = rootShell N n m p τ + windowAt N n m p τ c o := by
  let z := memberCutoff (cellQ N n c.1) o
  let v := cutoffAt N n m p τ
  have hb := (Finset.mem_filter.mp hp).1
  have hb' := (Finset.mem_filter.mp hb).1
  have hpr := (original_band_prime hb').1
  have hpa : (N:ℝ)^a ≤ (p:ℝ) := (Finset.mem_filter.mp hb').2.1
  have hrough {w : ℝ} (hw : w ≤ (N:ℝ)^a) : ChenPrimeRough w p := by
    intro r hr hd
    rw [(Nat.prime_dvd_prime_iff_eq hr hpr).mp hd]
    exact hw.trans hpa
  have hv : v ≤ (N:ℝ)^a := (classical_geometry (m := m) hN hτ hτ' hn hb).2.1
  have horder := fixed_cutoff_order hN hτ hτ' hn hp ho hz
  have hza : z ≤ (N:ℝ)^a := by
    by_cases hr : o.path.all retainedEdge = true
    · exact (horder.1 hr).2
    · exact (horder.2 hr).trans hv
  have hw := zeroFresh_original_word ho hz
  have heq : rejectedAt N (cellQ N n c.1) o = ((rejectedChild N p 1 z).card:ℝ) := by
    simp only [rejectedAt,tailProduct,hw,parentProduct,List.tail_cons,List.prod_nil,
      List.prod_cons,mul_one,z]
  have hchild := unit_frozen_split (hrough hza) hza
  have hroot := unit_frozen_split (hrough hv) hv
  have hbalance := root_query_rejected_balance (m := m) hN hτ hτ' hn hb
  have hs : ((rejectedChild N p 1 v).card:ℝ) = rootShell N n m p τ := by
    unfold rootShell
    linarith only [hbalance]
  rw [heq]
  refine ⟨hchild,?_⟩
  by_cases hr : o.path.all retainedEdge = true
  · change _ = rootShell N n m p τ + (if o.path.all retainedEdge then
      -firstWindow N p v z else firstWindow N p z v)
    rw [if_pos hr]
    have htransfer := buchstab_window N p (show v ≤ z from (horder.1 hr).1)
    linarith only [hchild,hroot,hs,htransfer]
  · change _ = rootShell N n m p τ + (if o.path.all retainedEdge then
      -firstWindow N p v z else firstWindow N p z v)
    rw [if_neg hr]
    have htransfer := buchstab_window N p (show z ≤ v from horder.2 hr)
    linarith only [hchild,hroot,hs,htransfer]

def historyWindow (N n m p : ℕ) (τ : ℝ) (c : RootKey n m) : ℝ :=
  chargedList (windowAt N n m p τ c) (rootHistory N n .U3 τ p)

def freshRejected (N n m p : ℕ) (τ : ℝ) (c : RootKey n m) : ℝ :=
  ((rootHistory N n .U3 τ p).map (fun o => if o.path.all zeroFreshEdge then 0 else
    mark o * rejectedAt N (cellQ N n c.1) o)).sum

private theorem sum_fixed_fresh {N : ℕ} (F : Occurrence N → ℝ) (xs : List (Occurrence N)) :
    (xs.map (fun o => mark o * F o)).sum = chargedList F xs +
      (xs.map (fun o => if o.path.all zeroFreshEdge then 0 else mark o * F o)).sum := by
  induction xs with
  | nil => simp [chargedList]
  | cons o os ih =>
      by_cases h : o.path.all zeroFreshEdge = true <;>
        simp only [List.map_cons,List.sum_cons,chargedList,occurrenceBudget,h,if_true,
          if_false,zero_mul,zero_add,ih] <;> ring

private theorem charged_translate {N : ℕ} (F W : Occurrence N → ℝ) (C : ℝ)
    (xs : List (Occurrence N)) :
    (∀ o ∈ xs, o.path.all zeroFreshEdge = true → F o = C + W o) →
    chargedList F xs = listBudget xs * C + chargedList W xs := by
  induction xs with
  | nil => intro _; simp [chargedList,listBudget]
  | cons o os ih =>
      intro h
      have ht := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
      by_cases hz : o.path.all zeroFreshEdge = true
      · simp only [chargedList,listBudget,ht,occurrenceBudget,hz,if_true,
          h o (List.mem_cons_self ..) hz]
        ring
      · simp only [chargedList,listBudget,ht,occurrenceBudget,hz,if_false,zero_mul,zero_add]

/-- The existing nonretained complement is accounted for together with
its retained part, with a single coefficient budget for both. -/
theorem actual_rejected_history_balance {N n m p : ℕ} {τ : ℝ} {c : RootKey n m}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c) :
    retainedRejected N n m τ c p + nonretainedRejected N n m τ c p =
      listBudget (rootHistory N n .U3 τ p) * rootShell N n m p τ +
        historyWindow N n m p τ c + freshRejected N n m p τ c := by
  rw [← rejectedHistory_split]
  unfold rejectedHistoryTotal historyWindow freshRejected
  rw [sum_fixed_fresh,charged_translate (rejectedAt N (cellQ N n c.1))
    (windowAt N n m p τ c) (rootShell N n m p τ) _ (fun o ho hz =>
      (fixed_row_balance hN hτ hτ' hn hp ho hz).2)]

/-- After the explicit signed windows and actual fresh rejected
receivers have been retained in the account, the remaining classical
charge is paid from the single directed cube-credit pool. -/
theorem actual_rejected_history_credit {τ ε : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1/12)
    (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        (retainedRejected N n m τ c p + nonretainedRejected N n m τ c p -
          historyWindow N n m p τ c - freshRejected N n m p τ c)) ≤
        431*((1+ε)*classicalOwnTheta N n m τ -
          ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c, ((originalReceiver N p).card:ℝ)) := by
  filter_upwards [classical_cubeCredit_pool hτ hτ' he,eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn
  have hrow (c : RootKey n m) (p : ℕ) (hp : p ∈ classicalFibre N n m τ c) :
      retainedRejected N n m τ c p + nonretainedRejected N n m τ c p -
        historyWindow N n m p τ c - freshRejected N n m p τ c ≤ 431*cubeCredit N n p τ := by
    have hb := (Finset.mem_filter.mp hp).1
    have hs := root_query_rejected_balance (m := m) hN hτ.le hτ' hn hb
    have hsc : rootShell N n m p τ =
        ((rejectedChild N p 1 (cutoffAt N n m p τ)).card:ℝ) := by
      unfold rootShell
      linarith only [hs]
    have hnet : retainedRejected N n m τ c p + nonretainedRejected N n m τ c p -
        historyWindow N n m p τ c - freshRejected N n m p τ c =
        listBudget (rootHistory N n .U3 τ p) * rootShell N n m p τ := by
      rw [actual_rejected_history_balance hN hτ.le hτ' hn hp]
      ring
    rw [hnet,hsc]
    exact (mul_le_mul_of_nonneg_right (zeroFresh_rootHistory_budget N n .U3 τ p)
      (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_left
        (root_query_rejected_le_cubeCredit hN hτ.le hτ' hn hb) (by norm_num))
  calc
    _ ≤ ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c, 431*cubeCredit N n p τ :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (hrow c))
    _ ≤ _ := by
      rw [sum_classicalFibre,← Finset.mul_sum,classicalOwnTheta_eq hN hτ.le hτ' hn,
        sum_classicalFibre N n m τ (fun p => ((originalReceiver N p).card:ℝ))]
      exact mul_le_mul_of_nonneg_left (hd hEven n hn) (by norm_num)

private theorem budget_nonneg {N : ℕ} (os : List (Occurrence N)) : 0 ≤ listBudget os := by
  induction os with
  | nil => exact le_rfl
  | cons o os ih => exact add_nonneg (occurrenceBudget_nonneg o) ih

private theorem root_budget_pos (N n p : ℕ) (τ : ℝ) :
    0 < listBudget (rootHistory N n .U3 τ p) := by
  change 0 < occurrenceBudget (origin (N := N) 430 (rootRequest N n .U3 τ p)) + listBudget _
  rw [occurrenceBudget_origin]
  exact add_pos_of_pos_of_nonneg zero_lt_one (budget_nonneg _)

def fixedUnmasked (N n m p : ℕ) (τ : ℝ) (c : RootKey n m) : ℝ :=
  chargedList (fun o => (frozenCount N p (receiver N) (memberCutoff (cellQ N n c.1) o) : ℝ))
    (rootHistory N n .U3 τ p)

/-- Normalize separately at each (tag,p) before using unit receipts in
the Chen root. The denominator includes the origin with weight one. -/
def fixedOriginalUnits (N n m p : ℕ) (τ : ℝ) (c : RootKey n m) : ℝ :=
  (fixedUnmasked N n m p τ c - historyWindow N n m p τ c) /
      listBudget (rootHistory N n .U3 τ p) - rootShell N n m p τ

theorem fixed_original_units_exact {N n m p : ℕ} {τ : ℝ} {c : RootKey n m}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c) :
    fixedOriginalUnits N n m p τ c = ((originalReceiver N p).card : ℝ) ∧
    fixedOriginalUnits N n m p τ c =
      (fixedUnmasked N n m p τ c - (retainedRejected N n m τ c p +
        nonretainedRejected N n m τ c p - freshRejected N n m p τ c)) /
          listBudget (rootHistory N n .U3 τ p) := by
  have hB := (root_budget_pos N n p τ).ne'
  have hf : fixedUnmasked N n m p τ c =
      listBudget (rootHistory N n .U3 τ p) *
        (((originalReceiver N p).card:ℝ) + rootShell N n m p τ) + historyWindow N n m p τ c := by
    unfold fixedUnmasked historyWindow
    apply charged_translate
    intro o ho hz
    obtain ⟨hf,hr⟩ := fixed_row_balance hN hτ hτ' hn hp ho hz
    rw [hf,hr] <;> ring
  constructor
  · unfold fixedOriginalUnits
    rw [hf]
    field_simp [hB] <;> ring
  · unfold fixedOriginalUnits
    rw [actual_rejected_history_balance hN hτ hτ' hn hp]
    field_simp [hB] <;> ring

open Part5OriginalH430SignedOriginalFinCapacityGap
open Part5OriginalH430NegativeQuarterActualPositionDirection
open Part5OriginalH430PhysicalSlotCollisionLedger Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430SequentialTaggedReceiptDebt Part5OriginalH430FullTaggedActualFinPushforward

/-- At the manuscript presieve the cutoff lane is the full original
tagged source. Restore each classical U3 fibre to unit weight before
the signed quarter; keep the other U3 and all U4 fibres at full cost. -/
theorem manuscript_signed_fixed_windows {N cap n m p : ℕ} {k : Root} {τ z0 : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (hz : z0 ≤ cutoff (rootQ N n k τ p) p (frozenRoot n k τ (physicalPrime N p)).physical.argument)
    (hcap : z0 ≤ (cap:ℝ)) (lower : Bool) :
    originalU34SignedQuarter N = -(1/4:ℝ) *
      ((occupiedFinUnits N cap n τ z0 lower + excessFinUnits N cap n τ z0 lower) +
        ((∑ q ∈ originalBand N .U3, if q ∈ classicalBand N then
            fixedOriginalUnits N n m q τ (keyAt N n m .U3 τ q) else
            ((originalReceiver N q).card:ℝ)) +
          ∑ q ∈ originalBand N .U4, ((originalReceiver N q).card:ℝ))) := by
  have hsource := full_tagged_fin_at_manuscript_presieve hN hτ hτ' hn hp hz hcap lower
  have hout : outsideRejectedUnits N cap n τ z0 lower =
      (∑ q ∈ originalBand N .U3, ((originalReceiver N q).card:ℝ)) +
        ∑ q ∈ originalBand N .U4, ((originalReceiver N q).card:ℝ) := by
    calc
      _ = ∑ z ∈ originalTagged N, (1:ℝ) := hsource.2.2 (fun _ => (1:ℝ))
      _ = ((originalTagged N).card:ℝ) := by simp
      _ = _ := by exact_mod_cast original_tagged_card N
  have hclass : (∑ q ∈ originalBand N .U3, if q ∈ classicalBand N then
          fixedOriginalUnits N n m q τ (keyAt N n m .U3 τ q) else
          ((originalReceiver N q).card:ℝ)) =
      ∑ q ∈ originalBand N .U3, ((originalReceiver N q).card:ℝ) := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q ∈ classicalBand N
    · rw [if_pos hq]
      exact (fixed_original_units_exact hN hτ hτ' hn (c := keyAt N n m .U3 τ q)
        (Finset.mem_filter.mpr ⟨hq,rfl⟩)).1
    · rw [if_neg hq]
  rw [hclass,original_signed_quarter_three_way N cap n τ z0 lower hcap,hout]

end
end ImbalancedChen.Part5OriginalH430FixedRejectedWindows
