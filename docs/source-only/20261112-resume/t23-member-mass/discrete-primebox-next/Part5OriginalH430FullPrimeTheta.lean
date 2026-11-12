import ImbalancedChen.Part5OriginalH430DiscreteThetaTransport

namespace ImbalancedChen.Part5OriginalH430FullPrimeTheta
noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical BigOperators
open P5OriginalActionMassBound P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430OwnedMemberMass Part5OriginalH430NativeProperSections
open Part5OriginalH430NativeQueryPaths Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenPerturbation
open Part5OriginalH430FullRootAmplitude Part5OriginalH430NativeMovingDensity
open Part5OriginalH430FixedProgramL1 Part5OriginalH430FixedPrimeScreen Part5OriginalH430PrimeProgramWord
open Part5OriginalH430SharpPrimeBox Part5OriginalH430DiscreteThetaTransport
open Part5OriginalH430OwnedRootCounts Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430EmittedWordBox Part5OriginalH430RequestedHistory
open Part5OriginalUpsilon5CausalDictionary (FloorAtom a)

def bottom := slotFloor / 2
theorem bottom_pos : 0 < bottom := half_pos slotFloor_pos
theorem bottom_lt_one : bottom < 1 := by
  have h : slotFloor ≤ 1 := min_le_left .. 
  dsimp [bottom]; linarith only [h]

private theorem tail_floor {d mesh : ℕ} {p : TypedNode} {code : Program mesh d} {z : Coordinates d}
    (hm : Member 0 1 d p code z) (hF : frozenResidualFloor ≤ residual (realize d p code z).physical) :
    ∀ i j, j.val < arity (code i).1 → frozenResidualFloor/6 ≤ z i j := by
  induction d generalizing p with
  | zero => intro i; exact Fin.elim0 i
  | succ d ih =>
    apply Fin.cases
    · intro j hj
      exact (div_le_div_of_nonneg_right (hF.trans (member_residual_le_root hm)) (by norm_num : (0:ℝ)≤6)).trans
        (fresh_coordinate_floor hm.2.2.1 hj)
    · intro i
      exact ih hm.2.2.2 hF i

private theorem slot_floor {d mesh : ℕ} (hd : d ≤ 440) (k : Root) (code : Program mesh d)
    (lower : Bool) (atom : FloorAtom) (v : Option ℕ) {x : NativeSlot (shapes code) → ℝ}
    (ht : nativeRootCoordinate x ∈ rootBand k) (hx : x ∈ fixedSet k code lower atom v)
    (hf : ∀ n, v = some n → meshError n ≤ 11/384) : ∀ j, bottom ≤ x j := by
  have hm : Member 0 1 d (base k v (nativeRootCoordinate x)) code (nativeCoordinates (shapes code) x) := hx.1
  have hL : frozenResidualFloor ≤ residual (node k code v x) := by
    cases v with
    | none =>
      have h := actual430_residual_floor (by norm_num : (0:ℝ)≤0) (by norm_num) ht hd hm
      apply le_trans _ h
      unfold frozenResidualFloor residualFloor
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    | some n => exact frozen430_residual_floor (finiteTau_pos n).le (finiteTau_le n) ht (hf n rfl) hd hm
  have hbot : bottom ≤ slotFloor := by dsimp [bottom]; linarith only [slotFloor_pos]
  have ha : slotFloor ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have h6 : slotFloor ≤ frozenResidualFloor/6 := (min_le_right _ _).trans (min_le_right _ _)
  intro j
  rcases j with u | ⟨i,j⟩
  · cases u; exact hbot.trans (ha.trans (rootBand_subset k ht).1)
  · let z : Fin 2 := ⟨j.val,j.isLt.trans_le (arity_le_two (shapes code i))⟩
    have h := tail_floor hm hL i z j.isLt
    simpa only [nativeCoordinates,z,dif_pos j.isLt] using hbot.trans (h6.trans h)

/-- Every genuine prime tuple giving an admitted side belongs to the
same fixed positive open-top cube. Each letter is prime and does not
divide N. Equality at the top would force that very prime to be N. -/
theorem accepted_in_positive_box {N r mesh d : ℕ} (hN : 1 < N) (hd : d ≤ 440) (k : Root)
    (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom)
    (v : Option ℕ) (hf : ∀ n, v = some n → meshError n ≤ 11/384) (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime ∧ ¬p i ∣ N) (hroot : p (e.symm (.inl ())) ∈ originalBand N k)
    (hx : view e (actualPrimeTupleLog N p) ∈ fixedSet k code lower atom v) :
    p ∈ actualPrimeBoxTuples N (fun _ => bottom) (fun _ => 1) := by
  let y := actualPrimeTupleLog N p
  let x := view e y
  have ht : nativeRootCoordinate x ∈ rootBand k := original_band_geometry (by omega : 2≤N) hroot
  have hl := slot_floor hd k code lower atom v ht hx hf
  have hm := hx
  rw [fixedSet_eq] at hm
  have hc := nativeSet_in_region ht hm.1
  refine (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr ⟨hp,mem_logPrimeBox.mpr ?_⟩
  intro i
  have hlo : bottom ≤ y i := by simpa only [x,view,e.symm_apply_apply] using hl (e i)
  have hhi : y i ≤ 1 := by simpa only [x,view,e.symm_apply_apply] using hc.1.2 (e i)
  refine ⟨hlo,lt_of_le_of_ne hhi ?_⟩
  intro he
  have hpow := actualPrimeTupleLog_rpow hN p (fun j => (hp j).1.pos) i
  change (N:ℝ)^y i = (p i:ℝ) at hpow
  rw [he,Real.rpow_one] at hpow
  have hEq : N = p i := by exact_mod_cast hpow
  exact (hp i).2 (by rw [hEq])

private theorem positive_subset {r N : ℕ} (hN : 1 < N) :
    actualPrimeBoxTuples N (fun _ : Fin r => bottom) (fun _ => 1) ⊆
      actualPrimeBoxTuples N (fun _ => 0) (fun _ => 1) := by
  intro p hp
  obtain ⟨h,hb⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
  exact (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr ⟨h,mem_logPrimeBox.mpr
    (fun i => ⟨bottom_pos.le.trans (mem_logPrimeBox.mp hb i).1,(mem_logPrimeBox.mp hb i).2⟩)⟩

theorem full_sum_eq {N n r mesh d : ℕ} (hN : 1 < N) (hn : meshError n ≤ 11/384) (hd : d ≤ 440)
    (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool)
    (atom : FloorAtom) (mark : (Fin r → ℕ) → ℝ) :
    markedError N n 0 k code e lower atom mark = markedError N n bottom k code e lower atom mark := by
  symm
  apply Finset.sum_subset (positive_subset hN)
  intro p hp hout
  have hP := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).1
  have zero (v : Option ℕ) (hf : ∀ j, v = some j → meshError j ≤ 11/384) :
      charged N k code e lower atom v p = 0 := by
    unfold charged
    apply if_neg
    rintro ⟨hr,hm⟩
    exact hout (accepted_in_positive_box hN hd k code e lower atom v hf p hP hr hm)
  rw [zero none (by simp),zero (some n) (by intro j h; cases h; exact hn),sub_zero,abs_zero,mul_zero]

/-- Full original prefix prime range, without a user-chosen trim.
The arithmetic threshold is allowed to depend on the frozen precision. -/
theorem full_prime_threshold {r mesh d : ℕ} {eps : ℝ} (he : 0 < eps) (hd : d ≤ 440) (k : Root)
    (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) :
    ∀ᶠ n in atTop, ∀ᶠ N in atTop, ∀ mark : (Fin r → ℕ) → ℝ,
      (∀ p ∈ actualPrimeBoxTuples N (fun _ => 0) (fun _ => 1), |mark p| ≤ 1) →
      markedError N n 0 k code e lower atom mark < eps := by
  have h := eventually_atTop.2 (fixed_program_arithmetic_threshold bottom_pos bottom_lt_one he hd k code e lower atom)
  filter_upwards [h,eventually_fine_mesh] with n hn hf
  filter_upwards [eventually_atTop.2 hn,eventually_gt_atTop (1:ℕ)] with N hN hN1
  intro mark hm
  rw [full_sum_eq hN1 hf hd]
  exact hN mark (fun p hp => hm p (positive_subset hN1 hp))

abbrev Programs (mesh : ℕ) := (d : Fin 441) × Program mesh d.val
def order {mesh d : ℕ} (code : Program mesh d) := (Fintype.equivFin (NativeSlot (shapes code))).symm

/-- A common n and then a common N₀(n) for every literal Program of
all 0..440 depths at this mesh, both roots and all terminal cells.
The summand is the absolute normalized geometric Theta displacement. -/
theorem all_program_arithmetic_threshold (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n ≥ T, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ v : Programs mesh, ∀ k : Root,
      ∀ lower : Bool, ∀ atom : FloorAtom, ∀ mark,
      (∀ p ∈ actualPrimeBoxTuples N (fun _ => 0) (fun _ => 1), |mark p| ≤ 1) →
      markedError N n 0 k v.2 (order v.2) lower atom mark < eps := by
  have h (v : Programs mesh) (k : Root) (l : Bool) (b : FloorAtom) :=
    full_prime_threshold he (by have hv := v.1.isLt; omega : v.1.val ≤ 440) k v.2 (order v.2) l b
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : Programs mesh => Filter.eventually_all.mpr
    (fun k : Root => Filter.eventually_all.mpr (fun l : Bool => Filter.eventually_all.mpr (h v k l))))] with n hn
  exact eventually_atTop.1 (Filter.eventually_all.mpr (fun v : Programs mesh => Filter.eventually_all.mpr
    (fun k : Root => Filter.eventually_all.mpr (fun l : Bool => Filter.eventually_all.mpr (hn v k l)))))

/-- One genuinely emitted root-history coefficient on this exact shape
and word. The same coefficient multiplies the two sides. -/
theorem emitted_prime_threshold {r mesh d : ℕ} {eps : ℝ} (he : 0 < eps) (hd : d ≤ 440)
    (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) :
    ∀ᶠ n in atTop, ∀ᶠ N in atTop, markedError N n 0 k code e lower atom
      (fun p => selectedWordMark (List.ofFn (shapes code)) (originalWord code e p)
        (rootHistory N n k (finiteTau n) (p (e.symm (.inl ()))))) < eps := by
  filter_upwards [full_prime_threshold he hd k code e lower atom] with n hn
  filter_upwards [hn] with N hN
  exact hN _ (fun p _ => actual_shape_word_mark k (finiteTau n) _ _ _)

end
end ImbalancedChen.Part5OriginalH430FullPrimeTheta
