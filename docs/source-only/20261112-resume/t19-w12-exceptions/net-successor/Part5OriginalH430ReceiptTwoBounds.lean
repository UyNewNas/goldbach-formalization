import ImbalancedChen.Part5OriginalH430ReceiptSignedPredecessors

namespace ImbalancedChen.Part5OriginalH430ReceiptTwoBounds
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound (Original106Action)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430ReceiptFourBand (count count_card)
open Part5OriginalH430ReceiptPairIncidences (labels outputs)
open Part5OriginalH430FreshReceiptCounts (receiptDebt receiptParent owned_fibre_bank_receipt_budget)
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger (selectedBankRoundingLoss)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open P2EnhancedLowerPrimeChildGeometry (parentWindow_logs)
open Part5OriginalH430SelectedFreshWindows (selected_geometry)
open Part5OriginalH430BankSlotTargets (actionTarget)
open Part5OriginalH430OwnedReceiptNet
open scoped Classical BigOperators

/-- Below the original root sieve height A the receipt's own roughness
forces every ordinary root anchor to give the same mass. -/
theorem original_root_plateau (N p : ℕ) {z w : ℝ}
    (hz : z≤(N:ℝ)^a) (hw : w≤(N:ℝ)^a) :
    count N p (rootMask N p) z=count N p (rootMask N p) w := by
  rw [count_card,count_card]
  apply congrArg (fun S : Finset ℕ => (S.card:ℝ))
  have sub (x : ℝ) {y : ℝ} (hy : y≤(N:ℝ)^a) :
      (sieveCarrier N p (p*N) x).filter (rootMask N p) ⊆
      (sieveCarrier N p (p*N) y).filter (rootMask N p) := by
    intro ell he
    obtain ⟨hd,hE⟩ := mem_filter.mp he
    obtain ⟨hr,hpr,hdiv,_⟩ := mem_filter.mp hd
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hr,hpr,hdiv,?_⟩,hE⟩
    intro q hq _ hc hqd
    exact (not_lt_of_ge (hE.2 q hq hqd)) (hc.trans_le hy)
  exact Subset.antisymm (sub z hw) (sub w hz)

theorem original_root_labels_empty (N p ell : ℕ) {z f : ℝ}
    (hf : f≤(N:ℝ)^a) (he : ell∈outputs N p z (rootMask N p)) :
    labels N p z f ell=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hwin,hdiv⟩ := mem_filter.mp hq
  obtain ⟨hpr,_,_,hhi⟩ := mem_primeWindow.mp hwin
  exact (not_lt_of_ge ((mem_filter.mp he).2.2 q hpr hdiv)) (hhi.trans_le hf)

theorem actual_root_height {N n p : ℕ} {k : Root} {t : ℝ} (hN : 2≤N)
    (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) :
    memberCutoff (rootQ N n k t p) (origin (N:=N) 430 (rootRequest N n k t p))≤(N:ℝ)^a := by
  have hB : P2EnhancedLowerPrimeChildCarriers.parentProduct
      (origin (N:=N) 430 (rootRequest N n k t p)).current.old=p := by
    simp [origin,rootRequest,P2EnhancedLowerPrimeChildCarriers.parentProduct]
  rw [memberCutoff,hB, P2EnhancedTwentyOneSameQWeighted.cutoff]
  change (rootQ N n k t p/(p:ℝ))^(1/
    (frozenRoot n k t (P2EnhancedLowerPrimeChildCarriers.physicalPrime N p)).physical.argument) ≤ _
  rw [Part5OriginalH430RequestedOriginalRowFreeze.frozen_root_sameQ_cutoff_power
    N n p k t hN (original_band_prime hp).1.pos ht hu (original_band_geometry hN hp) hn]
  exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (min_le_left _ _)

theorem selected_origin_labels_empty {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (l : Index N n k t p g) (act : Original106Action)
    (hl : l∈selectedLevel N n k t p g act)
    (ho : levelOccurrence l=origin (N:=N) 430 (rootRequest N n k t p))
    (lo : ℝ) (ell : ℕ) (he : ell∈outputs N p lo (rootMask N p)) :
    labels N p lo (P2EnhancedTwentyOneSameQWeighted.cutoff (rootQ N n k t p)
      (wordProduct l) (actionTarget act)) ell=∅ := by
  have h := selected_geometry hN ht hu hn hp act l hl
  have hr := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  have htop : P2EnhancedTwentyOneSameQWeighted.cutoff (rootQ N n k t p) (wordProduct l)
        (actionTarget act) ≤ memberCutoff (rootQ N n k t p) (levelOccurrence l) :=
    rpow_le_rpow_of_exponent_le (parentWindow_logs h.1).2.1.le
      (one_div_le_one_div_of_le (zero_lt_one.trans_le hr.2.2.2.1.1) h.2.1)
  rw [ho] at htop
  exact original_root_labels_empty N p ell (htop.trans (actual_root_height hN ht hu hn hp)) he

def inheritedDefect {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (Q : ℝ) (l : Index N n k t p g) : ℝ :=
  ((originalReceiptLane N p (tailProduct (levelOccurrence l))
    (memberCutoff Q (levelOccurrence l))).card:ℝ)-parentModel l

def parentOutside {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (Q : ℝ) (l : Index N n k t p g) : ℝ :=
  ((rejectedChild N (wordProduct l) (tailProduct (levelOccurrence l))
    (memberCutoff Q (levelOccurrence l))).card:ℝ)

/-- Take the lesser of the two complete fibre budgets. The direct
receipt mother retains its own negative singleton. The independent
full route can use the ordinary predecessor, with the exact favourable
parent shell and its one original rounding loss subtracted. -/
theorem independent_upper_routes {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n m : ℕ) (k : Root) (t : ℝ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → ∀ (c : RootKey n m) (g : Fin 430),
      let P := rootFibre N n m k t c
      let Q := cellQ N n c.1
      let total (f : (p : ℕ) → Index N n k t p g → Original106Action → ℝ) :=
        ∑ p∈P,∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,levelMark l*f p l a
      total (fun _ l _ => inheritedDefect Q l) ≤
        min (total fun _ l a => row l a-parentModel l)
          (total (fun _ l a => receiptDebt l a) - total (fun _ l _ => parentOutside Q l) -
            ∑ p∈P,selectedBankRoundingLoss N n k t p g) +
          ε*(∑ p∈P,actualBankTheta N n k t p g) := by
  obtain ⟨Tu,hu4,hU⟩ := owned_fibre_bank_receipt_budget he
  obtain ⟨Tr,hr4,hR⟩ := owned_106_net he
  refine ⟨max Tu Tr,hu4.trans (le_max_left _ _),?_⟩
  intro N hN hev n m k t ht hu hn c g
  have hNu := (le_max_left Tu Tr).trans hN
  have hNr := (le_max_right Tu Tr).trans hN
  have h2 : 2≤N := by omega
  let P := rootFibre N n m k t c
  let Q := cellQ N n c.1
  have h1 := hR N hNr hev n m k t ht hu hn c g
  have h2' := hU N hNu hev n m k t ht hu hn c g
  dsimp only at h1 h2' ⊢
  apply (sub_le_iff_le_add).mp
  refine le_min ((sub_le_iff_le_add).mpr h1) ?_
  apply (sub_le_iff_le_add).mpr
  have hex : (∑ p∈P,((∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,
        levelMark l*receiptParent Q l)+selectedBankRoundingLoss N n k t p g)) =
      (∑ p∈P,∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,
        levelMark l*inheritedDefect Q l) +
      (∑ p∈P,∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,
        levelMark l*parentOutside Q l)+(∑ p∈P,selectedBankRoundingLoss N n k t p g) := by
    rw [sum_add_distrib]
    congr 1
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have hQ := (original_fibre_geometry h2 ht hu hn hp).1
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro l _
    unfold receiptParent parentOutside inheritedDefect parentModel
    change levelMark l*(_ + _ - _) = levelMark l*(_-_) + levelMark l*_
    dsimp only [Q] at *
    rw [←hQ]
    ring
  change (∑ p∈P,((∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,
        levelMark l*receiptParent Q l)+selectedBankRoundingLoss N n k t p g)) ≤ _ at h2'
  rw [hex] at h2'
  linarith only [h2']

end
end ImbalancedChen.Part5OriginalH430ReceiptTwoBounds
