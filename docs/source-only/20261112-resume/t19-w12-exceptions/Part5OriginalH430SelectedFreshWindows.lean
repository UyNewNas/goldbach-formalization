import ImbalancedChen.P2OriginalPairChildWindowDictionary
import ImbalancedChen.Part5OriginalH430BankOrdinarySingletons
import ImbalancedChen.Part5OriginalH430W2SignedSingletons

/-! Frozen original U3/U4 histories, at the position selecting a particular
bank row. S17 supplies the finite partitions. The rational mesh rules out
their lower walls, and the actual parent's old word is rough at the top of
the selected window. The summands may keep both labels and the receiver. -/
namespace ImbalancedChen.Part5OriginalH430SelectedFreshWindows
noncomputable section
open Finset Set Real Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2OriginalHalfOpenProfileCarrier P2OriginalBankThetaMassLimits
open P2OriginalW2CountTupleReindex P2OriginalPairChildWindowDictionary
open P2OriginalSingleChildWindowDictionary
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430BankSlotTargets Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430OrdinaryPairWalls
open Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430PrimeChildAdmission
open scoped Classical BigOperators

variable {N n p : ℕ} {rt : Root} {t : ℝ} {g : Fin 430}

abbrev oldWord (l : Index N n rt t p g) := (levelOccurrence l).current.old
abbrev ceilingAt (l : Index N n rt t p g) := (levelOccurrence l).current.node.physical.ceiling

theorem selected_geometry (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (a : Original106Action) (l : Index N n rt t p g)
    (hl : l∈selectedLevel N n rt t p g a) :
    let Q := rootQ N n rt t p
    parentWindow N Q (oldWord l) (ceilingAt l) ∧
    (levelOccurrence l).current.node.physical.argument ≤ actionTarget a ∧
    wordLevel l/actionTarget a ≤ ceilingAt l ∧
    ChenPrimeRough (cutoff Q (wordProduct l) (actionTarget a)) (wordProduct l) := by
  have hs := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  have hc := rootHistory_coherent (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) (levelOccurrence_source l).1
  obtain ⟨i,hi⟩ := (mem_filter.mp hl).2
  have hb := (requested_bank_tests hc hi).2
  rw [action_slot] at hb
  have hr := (history_integer_roughness hN ht hu hn hp (levelOccurrence_source l).1).1
  have hw := (parentWindow_logs hs.1).2.1
  have hz : cutoff (rootQ N n rt t p) (wordProduct l) (actionTarget a) ≤
      cutoff (rootQ N n rt t p) (wordProduct l) (levelOccurrence l).current.node.physical.argument :=
    rpow_le_rpow_of_exponent_le hw.le
      (one_div_le_one_div_of_le (zero_lt_one.trans_le hs.2.2.2.1.1) hb.1)
  refine ⟨hs.1,hb.1,?_,fun q hq hd => hz.trans (hr q hq hd)⟩
  simpa only [wordLevel,←hs.2.1] using hb.2

private theorem no_lower_wall {d q : ℕ} {L : ℝ} (hN : 1<N) (hd : 0<d)
    (hL : 0<L) (hQ : rootQ N n rt t p=(d:ℝ)*(N:ℝ)^L) (a : Lane)
    (hq : q.Prime) (hcop : q.Coprime N) :
    (q:ℝ) ≠ cutoff (rootQ N n rt t p) d (anchor a) := by
  let x := fun _ : Fin 1 => q
  have hne := prime_coordinate_ne_rat hN hL hQ x
    (fun _ => ⟨hq,hq.coprime_iff_not_dvd.mp hcop⟩) 0 (leftQ a)
  intro heq
  apply hne
  have hpow := normalizedLog_rpow hN hL x (fun _ => hq.pos) 0
  change (N:ℝ)^(L*normalizedLog N L x 0) = (q:ℝ) at hpow
  rw [heq,cutoff_eq_physical_power hd hQ] at hpow
  have hex := (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hN : 1<(N:ℝ))).injective hpow
  rw [original_left]
  apply (mul_left_cancel₀ hL.ne')
  simpa only [div_eq_mul_inv,one_mul] using hex

theorem restored_zero {d : ℕ} {z top target : ℝ}
    (hfit : top ≤ target) (hr : ChenPrimeRough target d) :
    (primeWindow N z top).filter (fun q => q∣d) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hw,hd⟩ := mem_filter.mp hq
  obtain ⟨hpr,_,_,hhi⟩ := mem_primeWindow.mp hw
  exact (not_lt_of_ge (hr q hpr hd)) (hhi.trans_le hfit)

theorem singleton_W1 (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (i : Fin 7) (j : Fin 10) (l : Index N n rt t p g)
    (hl : l∈selectedLevel N n rt t p g (.inl (i,j))) (F : ℕ → ℝ) :
    let Q := rootQ N n rt t p
    (∑ q∈P2EnhancedActualBuchstabTransfer.childWindow N (wordProduct l) Q
      (W1Target i) (W1Anchor j), F q) =
      ∑ q∈singleChildren (.w1 i j) N Q (oldWord l) (ceilingAt l), F q.val := by
  have h := selected_geometry hN ht hu hn hp _ l hl
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  have hS := W1_childWindow_sum h.1 i j h.2.2.1 F
  have hem : (P2EnhancedActualBuchstabTransfer.childWindow N (wordProduct l)
      (rootQ N n rt t p) (W1Target i) (W1Anchor j)).filter
      (fun q => (q:ℝ)=cutoff (rootQ N n rt t p) (wordProduct l) (W1Anchor j)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨hw,he⟩ := mem_filter.mp hq
    have hh := mem_primeWindow.mp hw
    exact no_lower_wall (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ
      (.inl (i,j)) hh.1 (Nat.coprime_mul_iff_right.mp hh.2.1).2 he
  dsimp only
  change _ = _ + ∑ q ∈ (P2EnhancedActualBuchstabTransfer.childWindow N (wordProduct l)
    (rootQ N n rt t p) (W1Target i) (W1Anchor j)).filter _, F q at hS
  simpa only [hem,sum_empty,add_zero] using hS

theorem singleton_W2 (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (j : Fin 36) (s : Fin 3) (l : Index N n rt t p g)
    (hl : l∈selectedLevel N n rt t p g (.inr j)) (F : ℕ → ℝ) :
    let Q := rootQ N n rt t p
    (∑ q∈primeWindow N (cutoff Q (wordProduct l) (originalW2At j).s0)
      (cutoff Q (wordProduct l) (W2Upper j s)), F q) =
      ∑ q∈singleChildren (.w2 j s) N Q (oldWord l) (ceilingAt l), F q.val := by
  let Q := rootQ N n rt t p
  let d := wordProduct l
  let A := cutoff Q d (originalW2At j).s0
  let U := cutoff Q d (W2Upper j s)
  have h := selected_geometry hN ht hu hn hp _ l hl
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  have hw := W2Upper_order j s
  have hfit : U ≤ cutoff Q d (originalW2At j).s :=
    rpow_le_rpow_of_exponent_le (parentWindow_logs h.1).2.1.le
      (one_div_le_one_div_of_le (by linarith [hw.1]) hw.2)
  have hra := restored_zero (N:=N) (z:=A) hfit h.2.2.2
  have hem : (primeWindow (d*N) A U).filter (fun q => (q:ℝ)=A) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨hw,he⟩ := mem_filter.mp hq
    have hh := mem_primeWindow.mp hw
    exact no_lower_wall (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ
      (.inr (j,s)) hh.1 (Nat.coprime_mul_iff_right.mp hh.2.1).2 he
  have hs := W2_singleton_window_sum h.1 j s h.2.2.1 F
  change _ = _ + (∑ q∈(primeWindow (d*N) A U).filter (fun q => (q:ℝ)=A), F q) +
    ∑ q∈(primeWindow N A U).filter (fun q => q∣d), F q at hs
  simpa only [hra,hem,sum_empty,add_zero] using hs

theorem pair_W2 (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (j : Fin 36) (s : Fin 4) (l : Index N n rt t p g)
    (hl : l∈selectedLevel N n rt t p g (.inr j)) (F : ℕ → ℕ → ℝ) :
    let Q := rootQ N n rt t p
    windowOccurrence N Q (wordLevel l) (wordProduct l) (originalW2At j) s F =
      ∑ v∈pairChildren j s N Q (oldWord l) (ceilingAt l), F v.1.val v.2.val := by
  let L := wordLevel l
  let Q := rootQ N n rt t p
  let d := wordProduct l
  let A := fullPair N L j s
  have h := selected_geometry hN ht hu hn hp _ l hl
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  have hLp := frozenResidualFloor_pos.trans_le hL.1
  have h1 : 1<N := by omega
  have hpr {x : Fin 2 → ℕ} (hx : x∈A) (i : Fin 2) :
      (x i).Prime ∧ ¬x i∣N := by
    have hi := mem_actualPrimeBoxTuples_iff.mp (mem_filter.mp hx).1 i
    exact ⟨hi.1,hi.2.1⟩
  have hwall (x : Fin 2 → ℕ) (hx : x∈A) :
      normalizedLog N L x ∉ pairLowerWall (originalW2At j) s :=
    ((strict_pair_iff_half_not_wall j s _).mp
      ((actual_half_iff_open h1 hLp hQ j s x (hpr hx)).mp (mem_filter.mp hx).2)).2
  have hfresh (x : Fin 2 → ℕ) (hx : x∈A) : fresh d x := by
    have hs := pairHalf_below_target j s (mem_filter.mp hx).2
    have hn' (i : Fin 2) (hi : normalizedLog N L x i < 1/(originalW2At j).s) :
        ¬x i∣d := by
      have hw := ((normalizedLog_window h1 hLp x (fun i => (hpr hx i).1.pos) i
        (normalizedLog N L x i) (1/(originalW2At j).s)).mp ⟨le_rfl,hi⟩).2
      have hz : (x i:ℝ)<cutoff Q d (originalW2At j).s := by
        rw [cutoff_eq_physical_power hd hQ]
        simpa only [div_eq_mul_inv,one_mul] using hw
      exact fun hr => (not_lt_of_ge (h.2.2.2 _ (hpr hx i).1 hr)) hz
    exact ⟨hn' 0 hs.1,hn' 1 hs.2⟩
  have hb : A.filter (fun x => fresh d x ∧ normalizedLog N L x ∈
      pairLowerWall (originalW2At j) s) = ∅ := by
    exact eq_empty_iff_forall_notMem.mpr fun x hx =>
      hwall x (mem_filter.mp hx).1 (mem_filter.mp hx).2.2
  have hr : A.filter (fun x => ¬fresh d x) = ∅ := by
    exact eq_empty_iff_forall_notMem.mpr fun x hx =>
      (mem_filter.mp hx).2 (hfresh x (mem_filter.mp hx).1)
  have hs := W2_pair_window_sum h.1 hLp hQ j s h.2.2.1 F
  change _ = _ + (∑x∈A.filter (fun x => fresh d x ∧ normalizedLog N L x ∈
    pairLowerWall (originalW2At j) s), F (x 0) (x 1)) +
    ∑x∈A.filter (fun x => ¬fresh d x), F (x 0) (x 1) at hs
  simpa only [hb,hr,sum_empty,add_zero] using hs

def owner : Lane → Original106Action
  | .inl ij => .inl ij
  | .inr (j,_) => .inr j

def rule : Lane → SingleRule
  | .inl (i,j) => .w1 i j
  | .inr (j,s) => .w2 j s

theorem selected_single_sum (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (a : Lane) (l : Index N n rt t p g)
    (hl : l∈selectedLevel N n rt t p g (owner a)) (F : ℕ → ℝ) :
    let Q := rootQ N n rt t p
    (∑ q∈window N Q (wordLevel l) (wordProduct l) a,F q) =
      ∑ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),F q.val := by
  rcases a with ⟨i,j⟩ | ⟨j,s⟩
  · rw [←selected_W1_window hN ht hu hn hp i j l hl]
    exact singleton_W1 hN ht hu hn hp i j l hl F
  · obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
    have htop : (N:ℝ)^(wordLevel l*top (.inr (j,s))) =
        cutoff (rootQ N n rt t p) (wordProduct l) (W2Upper j s) := by
      rw [cutoff_eq_physical_power hd hQ,Part5OriginalH430W2SignedSingletons.top_eq]
      change (N:ℝ)^(_*(1/W2Upper j s))=(N:ℝ)^(_/W2Upper j s)
      congr 1
      ring
    simpa only [window,anchor,htop,rule] using singleton_W2 hN ht hu hn hp j s l hl F

/-- New child gates are required only on the enhanced branch with the
two original root gate tests. The classical root has a separate BV route. -/
theorem selected_child_gates (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g)
    (hf : fullGates (frozenRoot n rt t (physicalPrime N p)).physical)
    (hs : selectedGates (frozenRoot n rt t (physicalPrime N p)).physical) :
    let Q := rootQ N n rt t p
    let r := (levelOccurrence l).current.node.physical
    (∀ a : Lane, l∈selectedLevel N n rt t p g (owner a) →
      ∀ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
        let v := perform r (singleShape (rule a)) (singleCoordinates N q.val)
        fullGates v ∧ selectedGates v) ∧
    (∀ j : Fin 36, l∈selectedLevel N n rt t p g (.inr j) →
      ∀ s : Fin 4, ∀ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
        let w := perform r (.w2Pair j s) (pairCoordinates N v.1.val v.2.val)
        fullGates w ∧ selectedGates w) := by
  have hgeom := original_band_geometry hN hp
  have hroot := rootHistory_gates (by omega : 1<N) ht hu hn (original_band_prime hp)
    hgeom (levelOccurrence_source l).1 hf hs
  have hL := (rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    hgeom (levelOccurrence_source l).1).2.1
  constructor
  · intro a hl q hq
    have h := selected_geometry hN ht hu hn hp (owner a) l hl
    apply singleChild_gates hq hL rfl _ hroot.1 hroot.2
    have hfit := h.2.2.1
    unfold wordLevel at hfit
    rw [← hL] at hfit
    rcases a with ⟨i,j⟩ | ⟨j,s⟩ <;> exact ⟨h.2.1,hfit⟩
  · intro j hl s v hv
    have h := selected_geometry hN ht hu hn hp (.inr j) l hl
    have hfit := h.2.2.1
    unfold wordLevel at hfit
    rw [←hL] at hfit
    exact pairChild_gates hv hL rfl ⟨h.2.1,hfit⟩ hroot.1 hroot.2

/-- Positive or inherited receiver cuts commute with this *exact* ordered
count sum. This includes the actual frozen receiver and its intersection
with the original receipt at each parent. No sharp mother estimate is
asserted after restricting a receiver. -/
theorem selected_pair_frozen (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (j : Fin 36) (s : Fin 4) (l : Index N n rt t p g)
    (hl : l∈selectedLevel N n rt t p g (.inr j)) (E : ℕ → Prop) :
    let Q := rootQ N n rt t p
    let d := wordProduct l
    let a := originalW2At j
    let state : P2AllW1SameQRawCountInduction.PhysicalState :=
      ⟨fun D z => (P2FrozenReceiverCountActions.frozenCount N D E z:ℝ),
       fun D z => (P2FrozenReceiverCountActions.frozenCount N D E z:ℝ)⟩
    sourceGoodOccurrence N Q state d a s =
      ∑ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
        (P2FrozenReceiverCountActions.frozenCount N (d*v.1.val*v.2.val) E
          (occurrenceCutoff Q d a s v.1.val v.2.val):ℝ) := by
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  dsimp only
  rw [sourceGoodOccurrence_eq_window hd hQ]
  exact pair_W2 hN ht hu hn hp j s l hl _

end
end ImbalancedChen.Part5OriginalH430SelectedFreshWindows
