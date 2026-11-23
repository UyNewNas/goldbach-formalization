import ImbalancedChen.Part5OriginalH430AllReceiverPrimePassage

/-! The full, unscaled, counted population on a changing Program screen. -/
namespace ImbalancedChen.Part5OriginalH430DisagreementCounts
noncomputable section
open Set Filter Topology
open Part5OriginalH430FullRootAmplitude (eventually_fine_mesh)
open scoped Classical BigOperators
open P2OriginalChildPhysicalNormalization P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430NativeQueryPaths Part5OriginalH430OwnedRootCounts
open Part5OriginalH430SameQHistoryCells Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430FrozenRootMass
open Part5OriginalH430FrozenPerturbation Part5OriginalH430FixedProgramL1
open Part5OriginalH430EmittedWordBox Part5OriginalH430FixedPrimeScreen
open Part5OriginalH430SharpPrimeBox Part5OriginalH430PrimeProgramWord
open Part5OriginalH430DiscreteThetaTransport Part5OriginalH430FullPrimeTheta
open Part5OriginalH430OwnedMemberMass Part5OriginalH430OwnedThetaWord
open Part5OriginalH430OwnedPrimeBoxWeight Part5OriginalH430AbsoluteWordBox
open Part5OriginalH430SelectedBankCarrierSupply Part5OriginalH430AllReceiverPrimePassage
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

variable {r mesh d : ℕ}

/-- No theta lower bound is imposed on an unoccupied word. A genuinely
emitted word has the original positive residual and reciprocal-prime
majorant on the same RootKey, uniformly even on sparse owner fibres. -/
theorem observed_box_majorant :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop, Even N → ∀ n m, meshError n≤11/384 →
      ∀ (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
        (p : Fin r → ℕ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ i,(p i).Prime) → (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      |observed N n m k code e p E f / singularNormalization N| ≤ K*atomWeight p := by
  obtain ⟨C,hC,rows⟩ := all_receiver_domination (mesh:=mesh) (d:=d) (r:=r)
  let K := C*(1+4/frozenResidualFloor)
  have hK : 0<K := mul_pos hC (add_pos zero_lt_one (div_pos (by norm_num) frozenResidualFloor_pos))
  refine ⟨K,hK,?_⟩
  have hprice := price_tendsto.eventually_le_const (by norm_num : (0:ℝ)<1)
  filter_upwards [rows,eventually_ge_atTop (2:ℕ),primeFloor_tendsto.eventually_ge_atTop 4,hprice]
    with N hrows hN hA hcost
  intro hev n m hn k code e p E f hp hE hf
  let rootP := p (e.symm (.inl ()))
  let w := originalWord code e p
  let ss := List.ofFn (shapes code)
  let os := rootHistory N n k (finiteTau n) rootP
  let c := keyAt N n m k (finiteTau n) rootP
  have hw0 : 0≤atomWeight p := Finset.prod_nonneg (fun i _ => by
    have h : (1:ℝ)<p i := by exact_mod_cast (hp i).one_lt
    positivity)
  have hnon := mul_nonneg hK.le hw0
  by_cases hb : rootP∈originalBand N k
  · by_cases hocc : ∃ o∈os, o.path.map edgeShape=ss ∧ o.current.old=w
    · obtain ⟨o,ho,_,hw⟩ := hocc
      obtain ⟨u,hu,huw⟩ := emitted_owned_word (m:=m) 0 hN (finiteTau_pos n).le
        (finiteTau_le n) hn hb ho
      have hL : frozenResidualFloor ≤ Lkey c u :=
        (owned_support hN (finiteTau_pos n).le (finiteTau_le n) hn hu).2.2.1.1
      have hL0 := frozenResidualFloor_pos.trans_le hL
      have hfactor := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) frozenResidualFloor_pos hL
      have hbprod : primeBoxWord (labelWord u) = atomWeight p := by
        rw [huw,hw]
        exact word_product (fun q => 1/((q:ℝ)-1)) code e p
      have hterm := owned_primeBox_price hN hev (finiteTau_pos n).le (finiteTau_le n) hn hA hu
      change |thetaAtom N (cellQ N n c.1) (labelWord u).prod / singularNormalization N -
        (4/Lkey c u)*primeBoxWord (labelWord u)| ≤ price N*primeBoxWord (labelWord u) at hterm
      rw [hbprod,huw,hw] at hterm
      let T := ownAtom N n m k code e p / singularNormalization N
      have hT : |T|≤(1+4/frozenResidualFloor)*atomWeight p := by
        have hr : |T-(4/Lkey c u)*atomWeight p|≤price N*atomWeight p := hterm
        have hsum : T=(T-(4/Lkey c u)*atomWeight p)+(4/Lkey c u)*atomWeight p := by ring
        calc
          _ ≤ |T-(4/Lkey c u)*atomWeight p| + |(4/Lkey c u)*atomWeight p| :=
            (congrArg abs hsum).le.trans (abs_add_le ..)
          _ ≤ price N*atomWeight p + (4/Lkey c u)*atomWeight p := by
            rw [abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) hL0.le) hw0)]
            exact add_le_add_right hr _
          _ ≤ (1+4/frozenResidualFloor)*atomWeight p := by
            rw [←add_mul]
            exact mul_le_mul_of_nonneg_right (add_le_add hcost hfactor) hw0
      have hbound := div_le_div_of_nonneg_right
        (hrows hev n m hn k code e p E f hE hf) (abs_nonneg (singularNormalization N))
      calc
        _ ≤ C*|T| := by simpa only [abs_div,mul_div_assoc,T] using hbound
        _ ≤ K*atomWeight p := (mul_le_mul_of_nonneg_left hT hC.le).trans_eq (by dsimp [K]; ring)
    · have h0 := countedList_empty_of_no_match ss w (positionCount (ownerQ N n m k rootP) E f) os hocc
      simpa only [observed,rootP,if_pos hb,h0,zero_div,abs_zero] using hnon
  · simpa only [observed,rootP,if_neg hb,zero_div,abs_zero] using hnon

def screenCount (N n m : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (l : Bool) (a : FloorAtom)
    (lo : ℝ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ => lo) (fun _ => 1),
    if actualPrimeTupleLog N p ∈ screen k code e l a n then
      |observed N n m k code e p E f / singularNormalization N| else 0

private theorem full_screen_count {N n : ℕ} (hN : 1<N) (hn : meshError n≤11/384) (hd : d≤440)
    (m : ℕ) (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (l : Bool) (a : FloorAtom) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ) :
    screenCount N n m k code e l a 0 E f = screenCount N n m k code e l a bottom E f := by
  symm
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨h,hb⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
    exact (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr ⟨h,mem_logPrimeBox.mpr
      (fun i => ⟨bottom_pos.le.trans (mem_logPrimeBox.mp hb i).1,(mem_logPrimeBox.mp hb i).2⟩)⟩
  · intro p hp hout
    split_ifs with hcut
    · by_cases hroot : p (e.symm (.inl ()))∈originalBand N k
      · have hP := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).1
        rcases hcut.2 with hi | hs
        · exact False.elim (hout (accepted_in_positive_box hN hd k code e l a none (by simp) p hP hroot hi.1))
        · exact False.elim (hout (accepted_in_positive_box hN hd k code e l a (some n)
            (by intro j h; cases h; exact hn) p hP hroot hs.1))
      · simp [observed,hroot]
    · rfl

/-- Genuine integer counts on EITHER side of every full Program disagreement.
Take f=1 for positive mass, take an occurrence mask for original/rejected
subfamilies, and use independently changing signs within any such screen. -/
theorem all_program_true_count_threshold (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N → ∀ (v : Programs mesh) (k : Root)
      (l : Bool) (a : FloorAtom) (m : ℕ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      screenCount N n m k v.2 (order v.2) l a 0 E f < eps := by
  have each (v : Programs mesh) (k : Root) (l : Bool) (a : FloorAtom) :
      ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N → ∀ (m : ℕ)
        (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
        (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
        screenCount N n m k v.2 (order v.2) l a 0 E f < eps := by
    have hd : v.1.val ≤ 440 := by have hv := v.1.isLt; omega
    obtain ⟨K,hK,hrows⟩ := observed_box_majorant (mesh:=mesh) (d:=v.1.val)
      (r:=Fintype.card (NativeSlot (shapes v.2)))
    filter_upwards [fixed_screen_primebox hd k v.2 (order v.2) l a bottom_pos bottom_lt_one
      (div_pos he hK),eventually_fine_mesh] with n hmass hn
    filter_upwards [hrows,hmass,eventually_gt_atTop (1:ℕ)] with N hrows hm hN
    intro hev m E f hE hf
    rw [full_screen_count hN hn hd]
    have hbound : screenCount N n m k v.2 (order v.2) l a bottom E f ≤
        K*badMass N bottom (screen k v.2 (order v.2) l a n) := by
      unfold screenCount badMass actualPrimeBoxTestSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      by_cases hx : actualPrimeTupleLog N p∈screen k v.2 (order v.2) l a n
      · have hpr := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).1
        simpa only [if_pos hx,indicator_of_mem hx,mul_one,atomWeight] using
          hrows hev n m hn k v.2 (order v.2) p E f (fun i => (hpr i).1) hE hf
      · simp only [if_neg hx,indicator_of_notMem hx,mul_zero,le_refl]
    exact hbound.trans_lt ((mul_lt_mul_of_pos_left hm hK).trans_eq (by field_simp [hK.ne']))
  have allv := Filter.eventually_all.mpr (fun v : Programs mesh => Filter.eventually_all.mpr
    (fun k : Root => Filter.eventually_all.mpr (fun l : Bool => Filter.eventually_all.mpr (each v k l))))
  apply eventually_atTop.1
  filter_upwards [allv] with n hn
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : Programs mesh => Filter.eventually_all.mpr
    (fun k : Root => Filter.eventually_all.mpr (fun l : Bool => Filter.eventually_all.mpr (hn v k l))))] with N hN
  exact fun hev v k l a => hN v k l a hev

end
end ImbalancedChen.Part5OriginalH430DisagreementCounts
