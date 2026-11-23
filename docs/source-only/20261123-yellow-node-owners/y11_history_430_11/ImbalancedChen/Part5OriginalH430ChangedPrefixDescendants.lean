import ImbalancedChen.Part5OriginalH430ReselectedReceivers

/-! The first changed full-program screen can lie at a strict prefix of
a counted occurrence. Sum every later actual prime coordinate at its true
reciprocal-prime price, including repeated primes and inactive integers. -/
namespace ImbalancedChen.Part5OriginalH430ChangedPrefixDescendants
noncomputable section
open Set Filter Topology
open Part5OriginalH430FullRootAmplitude (eventually_fine_mesh)
open scoped Classical BigOperators
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPhysicalTransition
open Part5OriginalH430NativeQueryPaths Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedBranches Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430OwnedPrimeBoxWeight
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenPerturbation
open Part5OriginalH430NativeMovingDensity Part5OriginalH430FixedProgramL1
open Part5OriginalH430FixedPrimeScreen Part5OriginalH430SharpPrimeBox
open Part5OriginalH430PrimeProgramWord Part5OriginalH430FullPrimeTheta
open Part5OriginalH430EmittedWordBox Part5OriginalH430AllReceiverPrimePassage
open Part5OriginalH430DisagreementCounts Part5OriginalUpsilon5CausalDictionary (FloorAtom)
open P5OriginalU5FrozenSource (receiver)

variable {mesh d depth r s : ℕ}

private theorem coordinate_in_word (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (p : Fin r → ℕ) (i : Fin r) : p i ∈ originalWord code e p := by
  by_contra h
  let g := fun q : ℕ => if q=p i then (0:ℕ) else 1
  have h1 : ((originalWord code e p).map g).prod=1 := by
    apply List.prod_eq_one
    intro z hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
    exact if_neg (fun he => h (he ▸ hq))
  have h0 : (∏ j,g (p j))=0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g])
  rw [word_product g code e p,h0] at h1
  exact Nat.zero_ne_one h1

/-- No dependent tail count is cut off at the positive common cube. This
support statement uses its actual history code even when the tested prefix
screen is different from the terminal code of the counted position. -/
theorem observed_support {N n m : ℕ} (hN : 2≤N) (hn : meshError n≤11/384)
    (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (p : Fin r → ℕ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ)
    (hp : p∈actualPrimeBoxTuples N (fun _ => 0) (fun _ => 1))
    (hv : observed N n m k code e p E f ≠0) :
    p∈actualPrimeBoxTuples N (fun _ => bottom) (fun _ => 1) := by
  let rootP := p (e.symm (.inl ()))
  let ss := List.ofFn (shapes code)
  let w := originalWord code e p
  let os := rootHistory N n k (finiteTau n) rootP
  have hb : rootP∈originalBand N k := by
    by_contra hh
    exact hv (by simp only [observed,rootP,if_neg hh])
  have ho : ∃ o∈os, o.path.map edgeShape=ss ∧ o.current.old=w := by
    by_contra hh
    have h0 := countedList_empty_of_no_match ss w (positionCount (ownerQ N n m k rootP) E f) os hh
    exact hv (by simpa only [observed,rootP,if_pos hb] using h0)
  obtain ⟨o,ho,_,hw⟩ := ho
  obtain ⟨u,hu,heq⟩ := emitted_owned_word (m:=m) 0 hN (finiteTau_pos n).le
    (finiteTau_le n) hn hb ho
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hi := mem_actualPrimeBoxTuples_iff.mp hp i
  have hbot : bottom≤frozenResidualFloor/6 := by
    have h1 : slotFloor≤frozenResidualFloor/6 := (min_le_right ..).trans (min_le_right ..)
    dsimp only [bottom]; linarith only [slotFloor_pos,h1]
  have hle : (N:ℝ)^bottom≤primeFloor N := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1≤N by omega)) hbot
  have hword : p i∈labelWord u := by rw [heq,hw]; exact coordinate_in_word code e p i
  exact ⟨hi.1,hi.2.1,hle.trans (owned_letter_floor hN (finiteTau_pos n).le (finiteTau_le n) hn hu hword),
    hi.2.2.2⟩

abbrev cube (N r : ℕ) (lo : ℝ) := actualPrimeBoxTuples N (fun _ : Fin r => lo) (fun _ => 1)

private theorem append_cube {N r s : ℕ} {lo : ℝ} (p : Fin r → ℕ) (q : Fin s → ℕ) :
    Fin.append p q∈cube N (r+s) lo ↔ p∈cube N r lo ∧ q∈cube N s lo := by
  simp only [cube,mem_actualPrimeBoxTuples_iff]
  constructor
  · intro hh
    exact ⟨fun i => by simpa only [Fin.append_left] using hh (Fin.castAdd s i),
      fun i => by simpa only [Fin.append_right] using hh (Fin.natAdd r i)⟩
  · rintro ⟨h1,h2⟩
    exact Fin.addCases (fun i => by simpa only [Fin.append_left] using h1 i)
      (fun i => by simpa only [Fin.append_right] using h2 i)

private theorem append_weight (p : Fin r → ℕ) (q : Fin s → ℕ) :
    atomWeight (Fin.append p q)=atomWeight p*atomWeight q := by
  simp only [atomWeight,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

def descendants (N n m : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin (r+s) ≃ NativeSlot (shapes code)) (P : (Fin r → ℕ) → Prop)
    (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ) (lo : ℝ) : ℝ :=
  ∑ p∈cube N r lo, ∑ q∈cube N s lo, if P p then
    |observed N n m k code e (Fin.append p q) E f / singularNormalization N| else 0

private theorem reduce_cube {N n : ℕ} (hN : 2≤N) (hn : meshError n≤11/384)
    (m : ℕ) (k : Root) (code : Program mesh d) (e : Fin (r+s) ≃ NativeSlot (shapes code))
    (P) (E) (f) : descendants N n m k code e P E f 0 = descendants N n m k code e P E f bottom := by
  let term := fun p q => if P p then |observed N n m k code e (Fin.append p q) E f / singularNormalization N| else 0
  have sub (b : ℕ) : cube N b bottom ⊆ cube N b 0 := by
    intro p hp
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    have hr := mem_actualPrimeBoxTuples_iff.mp hp i
    exact ⟨hr.1,hr.2.1,(Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1≤N by omega)) bottom_pos.le).trans hr.2.2.1,hr.2.2.2⟩
  have vanishes {p q} (hp : p∈cube N r 0) (hq : q∈cube N s 0)
      (hbad : ¬(p∈cube N r bottom ∧ q∈cube N s bottom)) : term p q=0 := by
    have hzero : observed N n m k code e (Fin.append p q) E f=0 := by
      by_contra hh
      exact hbad ((append_cube p q).mp (observed_support hN hn k code e _ E f
        ((append_cube p q).mpr ⟨hp,hq⟩) hh))
    simp only [term,hzero,zero_div,abs_zero,ite_self]
  change (∑ p∈cube N r 0,∑ q∈cube N s 0,term p q) = ∑ p∈cube N r bottom,∑ q∈cube N s bottom,term p q
  calc
    _ = ∑ p∈cube N r bottom,∑ q∈cube N s 0,term p q := by
      symm
      apply Finset.sum_subset (sub r)
      intro p hp hb
      exact Finset.sum_eq_zero (fun q hq => vanishes hp hq (fun h => hb h.1))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      symm
      apply Finset.sum_subset (sub s)
      intro q hq hb
      exact vanishes (sub r hp) hq (fun h => hb h.2)

/-- The two true prime cubes are summed separately only to display the
projection. The integer word is the full original physical word under e,
and all suffix prime choices have been summed at their genuine weights. -/
theorem descendants_of_small_screen {eps : ℝ} (he : 0<eps)
    (code : Program mesh d) (orderFull : Fin (r+s) ≃ NativeSlot (shapes code))
    (k : Root) (screenAt : ℕ → Set (Fin r → ℝ))
    (hsmall : ∀ e : ℝ, 0<e → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      badMass N bottom (screenAt n)<e) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N → ∀ (m : ℕ)
      (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      descendants N n m k code orderFull
        (fun p => actualPrimeTupleLog N p∈screenAt n) E f 0 < eps := by
  obtain ⟨K,hK,hrows⟩ := observed_box_majorant (mesh:=mesh) (d:=d) (r:=r+s)
  let M := (Real.log (1/bottom))^s+1
  have hnlog := Real.log_nonneg ((one_le_div bottom_pos).mpr bottom_lt_one.le)
  have hM : 0<M := by dsimp [M]; positivity
  have hm : ∀ᶠ N : ℕ in atTop, actualPrimeBoxMass N (fun _ : Fin s => bottom) (fun _ => 1)≤M := by
    have hh := tendsto_actualPrimeBoxMass (fun _ : Fin s => bottom) (fun _ => 1)
      (fun _=>bottom_pos) (fun _=>bottom_lt_one)
    simpa only [M,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      hh.eventually_le_const (lt_add_one _)
  filter_upwards [hsmall _ (div_pos he (mul_pos hK hM)),eventually_fine_mesh] with n hsmall hn
  filter_upwards [hsmall,hrows,hm,eventually_ge_atTop (2:ℕ)] with N hmass hrows htail hN
  intro hev m E f hE hf
  let S := screenAt n
  let A := fun p : Fin r → ℕ => S.indicator (fun _ => (1:ℝ)) (actualPrimeTupleLog N p)
  have hA (p : Fin r → ℕ) : 0≤A p := by by_cases h : actualPrimeTupleLog N p∈S <;> simp [A,h]
  have hrow (p) (hp : p∈cube N r bottom) : (∑ q∈cube N s bottom, if actualPrimeTupleLog N p∈S then
      |observed N n m k code orderFull (Fin.append p q) E f / singularNormalization N| else 0)
      ≤ (K*M)*(atomWeight p*A p) := by
    have hpos := actualPrimeBoxWeight_nonneg hp
    calc
      _ ≤ ∑ q∈cube N s bottom, K*(atomWeight p*A p)*atomWeight q := by
        apply Finset.sum_le_sum
        intro q hq
        by_cases h : actualPrimeTupleLog N p∈S
        · have hpr := mem_actualPrimeBoxTuples_iff.mp ((append_cube p q).mpr ⟨hp,hq⟩)
          have hh := hrows hev n m hn k code orderFull (Fin.append p q) E f (fun i=>(hpr i).1) hE hf
          simpa only [if_pos h,A,indicator_of_mem h,mul_one,append_weight,mul_assoc] using hh
        · simp only [if_neg h,A,indicator_of_notMem h,mul_zero,zero_mul,le_refl]
      _ ≤ K*(atomWeight p*A p)*M := by
        rw [←Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left htail (mul_nonneg hK.le (mul_nonneg hpos (hA p)))
      _ = _ := by ring
  rw [reduce_cube hN hn]
  apply (Finset.sum_le_sum hrow).trans_lt
  rw [←Finset.mul_sum]
  exact (mul_lt_mul_of_pos_left hmass (mul_pos hK hM)).trans_eq
    (by field_simp [(mul_pos hK hM).ne'])

theorem full_descendants_of_changed_prefix {eps : ℝ} (he : 0<eps) (hd : depth≤440)
    (short : Program mesh depth) (orderShort : Fin r ≃ NativeSlot (shapes short))
    (code : Program mesh d) (orderFull : Fin (r+s) ≃ NativeSlot (shapes code))
    (k : Root) (l : Bool) (a : FloorAtom) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N → ∀ (m : ℕ)
      (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      descendants N n m k code orderFull
        (fun p => actualPrimeTupleLog N p∈screen k short orderShort l a n) E f 0 < eps :=
  descendants_of_small_screen he code orderFull k (screen k short orderShort l a)
    (fun _ h => fixed_screen_primebox hd k short orderShort l a bottom_pos bottom_lt_one h)

def prefixCode {i j : ℕ} (code : Program mesh (i+j)) : Program mesh i :=
  fun h => code (Fin.castAdd j h)

abbrev SuffixSlots {i j mesh : ℕ} (code : Program mesh (i+j)) :=
  (v : Fin j) × Fin (arity (shapes code (Fin.natAdd i v)))

/-- Keep the root on the prefix side, followed by the actual coordinates of
the prefix and then the actual coordinates of its continuation. -/
def chronologicalSlots {i j : ℕ} (code : Program mesh (i+j)) :
    NativeSlot (shapes (prefixCode code)) ⊕ SuffixSlots code ≃ NativeSlot (shapes code) := by
  let t := fun x : Fin i ⊕ Fin j => Fin (arity (shapes code (finSumFinEquiv x)))
  let h := (Equiv.sumSigmaDistrib t).symm.trans (Equiv.sigmaCongrLeft
    (β:=fun x : Fin (i+j) => Fin (arity (shapes code x))) finSumFinEquiv)
  exact (Equiv.sumAssoc Unit _ _).trans ((Equiv.refl Unit).sumCongr h)

def chronologicalOrder {i j : ℕ} (code : Program mesh (i+j)) :
    Fin (Fintype.card (NativeSlot (shapes (prefixCode code)))+Fintype.card (SuffixSlots code)) ≃
      NativeSlot (shapes code) :=
  finSumFinEquiv.symm.trans (((order (prefixCode code)).sumCongr
    (Fintype.equivFin (SuffixSlots code)).symm).trans (chronologicalSlots code))

abbrev SplitPrograms (mesh : ℕ) := (i : Fin 441) × (j : Fin 441) × Program mesh (i.val+j.val)

/-- Literal chronological cut of every program through depth 440, with a
common precision and then common target threshold over all such cuts.
Every extension is charged on the original integer carrier at its terminal
cutoff. Both categories of chart discrepancy use these same atom screens. -/
theorem all_chronological_prefix_threshold (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N → ∀ (v : SplitPrograms mesh)
      (k : Root) (l : Bool) (a : FloorAtom) (m : ℕ)
      (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      descendants N n m k v.2.2 (chronologicalOrder v.2.2)
        (fun p => actualPrimeTupleLog N p∈screen k (prefixCode v.2.2)
          (order (prefixCode v.2.2)) l a n) E f 0 < eps := by
  have each (v : SplitPrograms mesh) (k : Root) (l : Bool) (a : FloorAtom) :=
    full_descendants_of_changed_prefix he (by have h := v.1.isLt; omega : v.1.val≤440)
      (prefixCode v.2.2) (order (prefixCode v.2.2)) v.2.2 (chronologicalOrder v.2.2) k l a
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : SplitPrograms mesh => Filter.eventually_all.mpr
    (fun k : Root => Filter.eventually_all.mpr (fun l : Bool => Filter.eventually_all.mpr (each v k l))))] with n hn
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : SplitPrograms mesh => Filter.eventually_all.mpr
    (fun k : Root => Filter.eventually_all.mpr (fun l : Bool => Filter.eventually_all.mpr (hn v k l))))] with N hN
  exact fun hev v k l a => hN v k l a hev

end
end ImbalancedChen.Part5OriginalH430ChangedPrefixDescendants
