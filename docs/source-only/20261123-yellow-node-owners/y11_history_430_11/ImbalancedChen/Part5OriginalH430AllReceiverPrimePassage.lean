import ImbalancedChen.Part5OriginalH430SingleReceiptTheta
import ImbalancedChen.Part5OriginalH430RoughCutoffSelberg

/-! Actual additive-prime counts on complete physical programs. The summation
over all receivers takes place at each emitted position before the prime-box
limit. The sign, occurrence submask and arithmetic target may vary. -/
namespace ImbalancedChen.Part5OriginalH430AllReceiverPrimePassage
noncomputable section
open Set Filter Topology
open Part5OriginalH430FullRootAmplitude (eventually_fine_mesh)
open scoped Classical BigOperators
open P2OriginalChildPhysicalNormalization P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430NativeQueryPaths
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OwnedRootCounts Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenPerturbation
open Part5OriginalH430FixedProgramL1 Part5OriginalH430EmittedWordBox
open Part5OriginalH430FixedPrimeScreen Part5OriginalH430PrimeProgramWord
open Part5OriginalH430SharpPrimeBox Part5OriginalH430DiscreteThetaTransport
open Part5OriginalH430FullPrimeTheta Part5OriginalH430RoughCutoffSelberg
open Part5OriginalH430OwnedMemberMass Part5OriginalH430OwnedThetaWord
open Part5OriginalH430OwnedPrimeBoxWeight Part5OriginalH430AbsoluteWordBox
open Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

variable {mesh d r : ℕ}

def positionCount {N : ℕ} (Q : ℝ) (E : Occurrence N → ℕ → Prop)
    (f : Occurrence N → ℕ → ℝ) (o : Occurrence N) : ℝ :=
  ∑ ell ∈ frozenCarrier N (parentProduct o.current.old) (E o) (memberCutoff Q o), f o ell

def inheritedMask {N : ℕ} (o : Occurrence N) (ell : ℕ) : Prop :=
  rootMask N (o.current.old.headD 1) ell

def rejectedMask {N : ℕ} (o : Occurrence N) (ell : ℕ) : Prop :=
  receiver N ell ∧ ¬inheritedMask o ell

/-- Actual receiver masks are expressible from the retained integer word.
This preserves both populations even when one root prime lies in both tags. -/
theorem true_position_masks {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : meshError n≤11/384)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p) :
    let Q := cellQ N n c.1
    let z := memberCutoff Q o
    let B := parentProduct o.current.old
    positionCount Q inheritedMask (fun _ _ => 1) o=((originalReceiptLane N p (tailProduct o) z).card:ℝ) ∧
    positionCount Q rejectedMask (fun _ _ => 1) o=((rejectedChild N B (tailProduct o) z).card:ℝ) := by
  let Q := cellQ N n c.1
  let z := memberCutoff Q o
  let B := parentProduct o.current.old
  have hroot : inheritedMask o=rootMask N p := by
    funext ell
    simp only [inheritedMask,occurrence_old ho,List.headD_cons]
  have hcount (E : Occurrence N → ℕ → Prop) :
      positionCount Q E (fun _ _=>1) o=(frozenCount N B (E o) z:ℝ) := by
    simp [positionCount,frozenCount,B,z]
  have h1 := owned_member_masked_count hN ht hu hn hp ho
  have inherited : positionCount Q inheritedMask (fun _ _=>1) o=
      ((originalReceiptLane N p (tailProduct o) z).card:ℝ) := by rw [hcount,hroot]; exact h1
  let A := frozenCarrier N B (receiver N) z
  have hpos : A.filter (inheritedMask o)=frozenCarrier N B (inheritedMask o) z := by
    ext ell
    simp only [A,frozenCarrier,Finset.mem_filter,inheritedMask,rootMask]
    tauto
  have hneg : A.filter (fun ell=>¬inheritedMask o ell)=frozenCarrier N B (rejectedMask o) z := by
    ext ell
    simp only [A,frozenCarrier,Finset.mem_filter,rejectedMask]
    tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not A (inheritedMask o) (fun _ => (1:ℝ))
  rw [hpos,hneg] at hsplit
  change positionCount Q inheritedMask (fun _ _=>1) o+
    positionCount Q rejectedMask (fun _ _=>1) o=positionCount Q (fun _=>receiver N) (fun _ _=>1) o at hsplit
  have hall := actual_member_count_split hN ht hu hn hp ho
  dsimp only at hall
  rw [hcount (fun _=>receiver N),inherited] at hsplit
  exact ⟨inherited,by linarith only [hsplit,hall]⟩

def countedList {N : ℕ} (ss : List StepShape) (w : List ℕ) (pay : Occurrence N → ℝ) :
    List (Occurrence N) → ℝ
  | [] => 0
  | o :: os => (if o.path.map edgeShape = ss ∧ o.current.old = w then mark o * pay o else 0) +
      countedList ss w pay os

theorem countedList_empty_of_no_match {N : ℕ} (ss) (w) (pay : Occurrence N → ℝ) (os : List (Occurrence N))
    (h : ¬ ∃ o ∈ os, o.path.map edgeShape=ss ∧ o.current.old=w) :
    countedList ss w pay os = 0 := by
  induction os with
  | nil => rfl
  | cons o os ih =>
      have ha : ¬(o.path.map edgeShape=ss ∧ o.current.old=w) :=
        fun hh => h ⟨o,List.mem_cons_self ..,hh⟩
      have ht := ih (fun ⟨u,hu,hr⟩ => h ⟨u,List.mem_cons_of_mem _ hu,hr⟩)
      simp only [countedList,if_neg ha,ht,zero_add]

private theorem bounded_list {N : ℕ} (ss : List StepShape) (w : List ℕ) (pay : Occurrence N → ℝ)
    (B : ℝ) (os : List (Occurrence N)) (hB : 0≤B)
    (hp : ∀ o∈os, o.path.map edgeShape = ss → o.current.old = w → |pay o|≤B) :
    |countedList ss w pay os| ≤ B*selectedWordMark ss w os := by
  induction os with
  | nil => simp [countedList,selectedWordMark]
  | cons o os ih =>
      have ht := ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))
      by_cases hc : o.path.map edgeShape=ss ∧ o.current.old=w
      · have ho := mul_le_mul_of_nonneg_left (hp o (List.mem_cons_self ..) hc.1 hc.2) (mark_pos o).le
        simp only [countedList,selectedWordMark,if_pos hc,mul_add]
        apply (abs_add_le ..).trans
        rw [abs_mul,abs_of_nonneg (mark_pos o).le,mul_comm B (mark o)]
        exact add_le_add ho ht
      · simpa only [countedList,selectedWordMark,if_neg hc,zero_add] using ht

def ownerQ (N n m : ℕ) (k : Root) (p : ℕ) := cellQ N n (keyAt N n m k (finiteTau n) p).1

def observed (N n m : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) (E : Occurrence N → ℕ → Prop)
    (f : Occurrence N → ℕ → ℝ) : ℝ :=
  let rootP := p (e.symm (.inl ()))
  if rootP ∈ originalBand N k then
    countedList (List.ofFn (shapes code)) (originalWord code e p)
      (positionCount (ownerQ N n m k rootP) E f) (rootHistory N n k (finiteTau n) rootP)
  else 0

def ownAtom (N n m : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) :=
  thetaAtom N (ownerQ N n m k (p (e.symm (.inl ())))) (originalWord code e p).prod

private theorem position_abs {N : ℕ} (Q : ℝ) (E : Occurrence N → ℕ → Prop)
    (f : Occurrence N → ℕ → ℝ) (hf : ∀ o ell, |f o ell|≤1) (o : Occurrence N) :
    |positionCount Q E f o| ≤ (frozenCount N (parentProduct o.current.old) (E o) (memberCutoff Q o):ℝ) := by
  unfold positionCount
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _ell ∈ frozenCarrier N (parentProduct o.current.old) (E o) (memberCutoff Q o), (1:ℝ) :=
      Finset.sum_le_sum (fun ell _ => hf o ell)
    _ = _ := by simp [frozenCount]

/-- One absolute Selberg constant for every actual prime label together,
with actual list marks and multiplicity. No upper bound on the number of
receivers attached to an integer word is assumed. -/
theorem all_receiver_domination :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, Even N → ∀ (n m : ℕ),
      meshError n ≤ 11/384 → ∀ (k : Root) (code : Program mesh d)
      (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) (E : Occurrence N → ℕ → Prop)
      (f : Occurrence N → ℕ → ℝ), (∀ o ell, E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      |observed N n m k code e p E f| ≤ C*|ownAtom N n m k code e p| := by
  obtain ⟨C,hC,hrows⟩ := actual_member_count_dominated
  refine ⟨C,hC,?_⟩
  filter_upwards [hrows,eventually_ge_atTop (2:ℕ)] with N hrows hN
  intro hev n m hn k code e p E f hE hf
  let rootP := p (e.symm (.inl ()))
  let w := originalWord code e p
  let ss := List.ofFn (shapes code)
  let Q := ownerQ N n m k rootP
  let A := ownAtom N n m k code e p
  let os := rootHistory N n k (finiteTau n) rootP
  have hCA : 0 ≤ C*|A| := mul_nonneg hC.le (abs_nonneg _)
  by_cases hroot : rootP ∈ originalBand N k
  · have hkey : rootP ∈ rootFibre N n m k (finiteTau n) (keyAt N n m k (finiteTau n) rootP) :=
      Finset.mem_filter.mpr ⟨hroot,rfl⟩
    have hQ := (original_fibre_geometry hN (finiteTau_pos n).le (finiteTau_le n) hn hkey).1
    have bound (o) (ho : o∈os) (_ : o.path.map edgeShape=ss) (hw : o.current.old=w) :
        |positionCount Q E f o| ≤ C*|A| := by
      have h := hrows hev n rootP k (finiteTau n) o (E o) (finiteTau_pos n).le
        (finiteTau_le n) hn hroot ho (hE o)
      dsimp only at h
      rw [←hQ] at h
      apply (position_abs Q E f hf o).trans
      apply h.trans
      simpa only [A,ownAtom,rootP,Q,ownerQ,w,hw,parentProduct] using
        (mul_le_mul_of_nonneg_left (le_abs_self (thetaAtom N Q w.prod)) hC.le)
    have hmult : selectedWordMark ss w os ≤ 1 :=
      (le_abs_self _).trans (actual_shape_word_mark k (finiteTau n) rootP ss w)
    simpa only [observed,rootP,if_pos hroot,mul_one] using
      (bounded_list ss w _ _ os hCA bound).trans (mul_le_mul_of_nonneg_left hmult hCA)
  · simpa only [observed,rootP,if_neg hroot,abs_zero] using hCA

/-- Recover the entire observed signed count, including when its own theta is zero. -/
theorem ratio_recovers {x T C : ℝ} (h : |x|≤C*|T|) : (x/T)*T=x := by
  by_cases ht : T=0
  · rw [ht,abs_zero,mul_zero] at h
    rw [abs_nonpos_iff.mp h]
    simp
  · exact div_mul_cancel₀ x ht

/-- Both sides of the transport use the same legitimately valued frozen
count per word. On the frozen accepted set the product is the actual sum
of receiver labels divided by the manuscript H(N). -/
theorem frozen_count_value {N n m : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (p : Fin r → ℕ) (E : Occurrence N → ℕ → Prop)
    (f : Occurrence N → ℕ → ℝ) (l : Bool) (a : FloorAtom) (hN : 2≤N)
    (hn : meshError n≤11/384) (hp : p (e.symm (.inl ()))∈originalBand N k)
    (hs : view e (actualPrimeTupleLog N p)∈fixedSet k code l a (some n))
    {C : ℝ} (hc : |observed N n m k code e p E f|≤C*|ownAtom N n m k code e p|) :
    (observed N n m k code e p E f / ownAtom N n m k code e p) *
      charged N k code e l a (some n) p = observed N n m k code e p E f / singularNormalization N := by
  have hQ := frozenQ_is_original_fibre (m:=m) hN hn hp
  simp only [charged,hp,hs,and_self,if_true]
  change _ * (thetaAtom N (Part5OriginalH430PrimeProgramWord.actualQ N k (some n)
    (physicalPrime N (p (e.symm (.inl ()))))) (originalWord code e p).prod / _) = _
  rw [hQ]
  change _ * (ownAtom N n m k code e p / _) = _
  rw [←mul_div_assoc,ratio_recovers hc]

private theorem scale_error (N n : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (l : Bool) (a : FloorAtom)
    (f : (Fin r → ℕ) → ℝ) {C : ℝ} (hC : 0<C) :
    markedError N n 0 k code e l a f = C*markedError N n 0 k code e l a (fun p => f p/C) := by
  unfold markedError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [abs_div,abs_of_pos hC]
  field_simp [hC.ne']

/-- One precision and then one arithmetic threshold for ALL actual recipients,
two roots, all complete programs and atoms. The weighted quotient is
specified in terms of the finite actual frozenCarrier itself. -/
theorem all_receiver_theta_threshold (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N → ∀ (v : Programs mesh) (k : Root)
      (l : Bool) (a : FloorAtom) (m : ℕ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell, E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      markedError N n 0 k v.2 (order v.2) l a
        (fun p => observed N n m k v.2 (order v.2) p E f / ownAtom N n m k v.2 (order v.2) p) < eps := by
  have one (v : Programs mesh) : ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (k : Root) (l : Bool) (a : FloorAtom) (m : ℕ) (E : Occurrence N → ℕ → Prop)
        (f : Occurrence N → ℕ → ℝ), (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
        markedError N n 0 k v.2 (order v.2) l a
          (fun p => observed N n m k v.2 (order v.2) p E f / ownAtom N n m k v.2 (order v.2) p) < eps := by
    obtain ⟨C,hC,hdom⟩ := all_receiver_domination (mesh:=mesh) (d:=v.1.val)
      (r:=Fintype.card (NativeSlot (shapes v.2)))
    obtain ⟨T,hT⟩ := all_program_arithmetic_threshold mesh (div_pos he hC)
    filter_upwards [eventually_ge_atTop T,eventually_fine_mesh] with n hn hmesh
    obtain ⟨N₀,hN₀⟩ := hT n hn
    filter_upwards [eventually_ge_atTop N₀,hdom] with N hN hrow
    intro hev k l a m E f hE hf
    let u := fun p => observed N n m k v.2 (order v.2) p E f / ownAtom N n m k v.2 (order v.2) p
    have hb (p) : |u p|≤C := by
      have hh := hrow hev n m hmesh k v.2 (order v.2) p E f hE hf
      by_cases hz : ownAtom N n m k v.2 (order v.2) p=0
      · simp [u,hz,hC.le]
      · exact (abs_div ..).trans_le ((div_le_iff₀ (abs_pos.mpr hz)).mpr hh)
    have hh := hN₀ N hN v k l a (fun p => u p/C) (fun p _ => by
      rw [abs_div,abs_of_pos hC]; exact (div_le_one hC).mpr (hb p))
    rw [scale_error N n k v.2 (order v.2) l a u hC]
    exact (mul_lt_mul_of_pos_left hh hC).trans_eq (by field_simp [hC.ne'])
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr one] with n hn
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr hn] with N hN
  exact fun hev v => hN v hev

end
end ImbalancedChen.Part5OriginalH430AllReceiverPrimePassage
