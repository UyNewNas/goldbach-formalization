import ImbalancedChen.P2FiniteMarkedGamma5SeedCellFibre
import ImbalancedChen.P2FiniteMarkedGamma5TargetExclusion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual finite atlas Family mass is compared with its exact arithmetic
seed-cell mask. Complete-product noncoprimality and proper-wall spill are
two positive errors, both paid before the target and all moving tuples.
The right side keeps the original profile and coefficient one.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasOrdinaryExcess
noncomputable section
open Filter Finset Real Set
open Part5OriginalCausalSmoothAtlas (Plan Code atom atom_nonneg atom_total)
open Part5OriginalH430JointQueryEnclosure (Cube hit readout)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open Part5OriginalH430PhysicalRoots (Root)
open Part5OriginalH430FrozenRootRefinement
  (RootCode frozenLeafCutoffFloor frozenLeafCutoffFloor_pos)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand original_band_geometry)
open Part5OriginalH430SmoothPrefixRequests (physicalPrime_unit)
open P2FiniteMarkedGamma5NativeSeedSum (Index fixedWeight)
open P2FiniteMarkedGamma5OrderedOldSlots (oldSlotEquiv)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple weight mark_nonneg)
open P2FiniteMarkedGamma5SeedCellReadout
  (wallTuple wallTuple_numbering nativePoint nativeDomain planAt acceptAt actual_weight)
open P2FiniteMarkedGamma5SeedCellFibre (oldValue exactCell exactCell_native nativePoint_eq)
open P2FiniteMarkedGamma5EulerWordBudget (slotEquiv slotEquiv_old finPhysicalProfile finToPhysical)
open P2FiniteMarkedGamma5PhysicalExtension (physicalProfile_bounds)
open P2FiniteMarkedGamma5IntegerSupport (finPhysicalProfile_nonzero_support)
open P2FiniteMarkedGamma5GateAffine (numbering)
open P2FiniteMarkedGamma5SelectedNativeWallPayment (nativeLog baseTuples)
open P2FiniteMarkedGamma5SelectedCellWallPayment
  (cellOuterTuples exists_all_cells_outer_payment)
open P2FiniteMarkedGamma5RadialProfileCollar
  (radialWidth radialWidth_pos radialWidth_le_one exp_radialWidth_lt_two)
open P2FiniteMarkedGamma5RadialRoughMass (cut norm eventually_cut_le_half_floor)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5TargetExclusion
  (noncoprimeTuples noncoprimeCount rank_card_le_noncoprimeCount absolute_noncoprime_payment)
open scoped Classical BigOperators Topology

private abbrev profile {n N : ℕ} (v : Entry n) (h : ℝ) (u : Tuple N v) : ℝ :=
  finPhysicalProfile (log (cellQ N n v.val.2.1)) (N:ℝ) (radialWidth h)
    ((N:ℝ)^frozenLeafCutoffFloor) (fun i => ((u i).val:ℝ))

private abbrev outer {n : ℕ} (N : ℕ) (v : Entry n) (root : Root) (tau : ℝ)
    (m : Index 430 → ℕ) :=
  cellOuterTuples v.val.1.val.1 (oldSlotEquiv v.val.1.val.1).symm
    N n root tau v.val.1.val.2 v.val.2.1 (tailRank v) (m v.val.1)

private theorem wallTuple_injective {N k r : ℕ} :
    Function.Injective (wallTuple (N:=N) (k:=k) (r:=r)) := by
  intro u v h
  funext j
  have H := congrFun h (numbering k r ((slotEquiv k r).symm j))
  simpa only [wallTuple_numbering,Equiv.apply_symm_apply] using H

private theorem wallTuple_product {N k r : ℕ}
    (u : Fin (k+(2+r)) → Fin (2*N+1)) :
    Part3.labelledProduct (wallTuple u) = Part3.labelledProduct u :=
  ((numbering k r).symm.trans (slotEquiv k r)).prod_comp (fun i => (u i).val)

private theorem profile_bounds {n N : ℕ} (v : Entry n) (h : ℝ) (u : Tuple N v) :
    0 ≤ profile v h u ∧ profile v h u ≤ 1 :=
  physicalProfile_bounds _ _ _ _ (finToPhysical (oldRank v) (tailRank v)
    (fun i => ((u i).val:ℝ)))

/-- The floor and product hypotheses for both old arithmetic payments
come from nonzero original profile support, uniformly in its cell Q. -/
private theorem profile_support {n N : ℕ} (v : Entry n) {h : ℝ}
    (hN : 2 ≤ N) (hh : 0 < h) (h8 : h ≤ 1/8)
    (hcut : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2) {u : Tuple N v}
    (hu : u ∈ Part3.labelledPrimeTuples (rank v) (2*N))
    (hne : profile v h u ≠ 0) :
    (∀ i, cut N ≤ ((u i).val:ℝ)) ∧ Part3.labelledProduct u ≤ 2*N ∧
      Cube (nativePoint v u) := by
  have hN0 : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  obtain ⟨hfloor,hcap⟩ := finPhysicalProfile_nonzero_support
    (rpow_pos_of_pos hN0 frozenLeafCutoffFloor) hN0 (radialWidth_pos hh) hne
  have hcap' : Part3.labelledProduct u ≤ 2*N := by
    have H : (Part3.labelledProduct u:ℝ) < 2*(N:ℝ) := by
      simpa only [Part3.labelledProduct,Nat.cast_prod] using
        hcap.trans (mul_lt_mul_of_pos_right (exp_radialWidth_lt_two hh h8) hN0)
    exact_mod_cast H.le
  have hprime : ∀ i, (u i).val.Prime := (mem_filter.mp hu).2
  refine ⟨fun i => hcut.trans (hfloor i).le,hcap',?_⟩
  rw [nativePoint_eq]
  intro z
  exact physicalPrime_unit (by omega) (hprime _).one_lt.le
    (P2PrimeProductCoordinateCore.coordinate_le_of_prod_le_two_mul (by omega)
      (fun i => (u i).val) (fun i => (hprime i).two_le) hcap' _)

/-- Only here is the complete-product coprime condition used. It implies
the exactCell old-slot conditions; it is not added to exactCell itself. -/
private theorem clean_outer_mem {n N : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (m : Index 430 → ℕ) {h : ℝ} (hN : 2 ≤ N) (hh : 0 < h) (h8 : h ≤ 1/8)
    (hcut : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2) {u : Tuple N v}
    (hu : u ∈ Part3.labelledPrimeTuples (rank v) (2*N))
    (hp : profile v h u ≠ 0) (hc : (Part3.labelledProduct u).Coprime N)
    (hx : ¬exactCell v root tau u)
    (hr : readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau))
      (nativePoint v u) ≠ 0) :
    wallTuple u ∈ outer N v root tau m := by
  obtain ⟨hfloor,hcap,_⟩ := profile_support v hN hh h8 hcut hu hp
  have hprime : ∀ i, (u i).val.Prime := (mem_filter.mp hu).2
  have hold : ∀ z, (oldValue v u z).Coprime N := by
    intro z
    exact hc.of_dvd_left (dvd_prod_of_mem (fun i => (u i).val)
      (mem_univ (Fin.castAdd (2+tailRank v) ((oldSlotEquiv v.val.1.val.1).symm z))))
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,fun _ => hprime _⟩,
    fun _ => hfloor _,by simpa only [wallTuple_product] using hcap,
    by simpa only [wallTuple_product] using hc⟩,hr,?_⟩
  rintro ⟨hp0,hs,hcode⟩
  have hroot : oldValue v u (.inl ()) ∈ originalBand N root := by
    simpa only [wallTuple_numbering,slotEquiv_old,oldValue] using hp0
  apply hx
  apply (exactCell_native v root tau u hN).mpr
  refine ⟨hroot,hold,⟨⟨?_,hs⟩,hcode⟩⟩
  simpa only [nativePoint_eq] using original_band_geometry hN hroot

private theorem noncoprime_mem {n N : ℕ} (v : Entry n) {h : ℝ}
    (hN : 2 ≤ N) (hh : 0 < h) (h8 : h ≤ 1/8)
    (hcut : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2) {u : Tuple N v}
    (hu : u ∈ Part3.labelledPrimeTuples (rank v) (2*N))
    (hp : profile v h u ≠ 0) (hc : ¬(Part3.labelledProduct u).Coprime N) :
    u ∈ noncoprimeTuples N (rank v) := by
  obtain ⟨hfloor,hcap,_⟩ := profile_support v hN hh h8 hcut hu hp
  exact mem_filter.mpr ⟨hu,hfloor,by exact_mod_cast hcap,hc⟩

private theorem indicator_sum_le_card {α β : Type*} (S : Finset α) (T : Finset β)
    (f : α → β) (hf : Function.Injective f) :
    (∑ u ∈ S, if f u ∈ T then (1:ℝ) else 0) ≤ (T.card:ℝ) := by
  let A := S.filter (fun u => f u ∈ T)
  have H : A.card ≤ T.card :=
    card_le_card_of_injOn f (fun _ hu => (mem_filter.mp hu).2) hf.injOn
  have he : (∑ u ∈ S, if f u ∈ T then (1:ℝ) else 0) = (A.card:ℝ) := by
    rw [← sum_filter]
    simp [A]
  rw [he]
  exact_mod_cast H

/-- Positive pointwise decomposition on the original bounded prime
carrier. The main term uses exactCell, with all original old coprimality. -/
private theorem pointwise {n N : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (m : Index 430 → ℕ) {h : ℝ} (hN : 2 ≤ N) (hh : 0 < h) (h8 : h ≤ 1/8)
    (hcut : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2)
    (hscale : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ)) {u : Tuple N v}
    (hu : u ∈ Part3.labelledPrimeTuples (rank v) (2*N)) :
    weight v (planAt m v) (radialWidth h) frozenLeafCutoffFloor_pos
      (radialWidth_pos hh) (radialWidth_le_one hh h8) (acceptAt root tau m v) N u ≤
      (if exactCell v root tau u then profile v h u else 0) +
      (if u ∈ noncoprimeTuples N (rank v) then 1 else 0) +
      (if wallTuple u ∈ outer N v root tau m then 1 else 0) := by
  rw [actual_weight v root tau m u (radialWidth h) (radialWidth_pos hh)
    (radialWidth_le_one hh h8) hscale (by omega)]
  change profile v h u *
      readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau)) (nativePoint v u) ≤ _
  have hNC : (0:ℝ) ≤ if u ∈ noncoprimeTuples N (rank v) then 1 else 0 := by
    split_ifs <;> norm_num
  have hwall : (0:ℝ) ≤ if wallTuple u ∈ outer N v root tau m then 1 else 0 := by
    split_ifs <;> norm_num
  by_cases hp : profile v h u = 0
  · simp only [hp,zero_mul,ite_self,zero_add]
    exact add_nonneg hNC hwall
  have hCube := (profile_support v hN hh h8 hcut hu hp).2.2
  have hR : readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau))
      (nativePoint v u) ≤ 1 := by
    rw [← atom_total (planAt m v) hCube]
    apply sum_le_sum
    intro j _
    split_ifs <;> simp [atom_nonneg]
  have hmul : profile v h u *
      readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau))
        (nativePoint v u) ≤ profile v h u := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hR (profile_bounds v h u).1
  by_cases hx : exactCell v root tau u
  · simp only [if_pos hx]
    linarith
  simp only [if_neg hx,zero_add]
  by_cases hc : (Part3.labelledProduct u).Coprime N
  · by_cases hr : readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau))
        (nativePoint v u) = 0
    · simp only [hr,mul_zero]
      exact add_nonneg hNC hwall
    · have hm := clean_outer_mem v root tau m hN hh h8 hcut hu hp hc hx hr
      rw [if_pos hm]
      linarith [(profile_bounds v h u).2]
  · have hm := noncoprime_mem v hN hh h8 hcut hu hp hc
    rw [if_pos hm]
    linarith [(profile_bounds v h u).2]

/-- This finite inequality contains the actual Family weight. Its two
positive allowances have no arithmetic filter hidden in that weight. -/
private theorem entry_bound {n N : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (m : Index 430 → ℕ) {h : ℝ} (hN : 2 ≤ N) (hh : 0 < h) (h8 : h ≤ 1/8)
    (hcut : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2)
    (hscale : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ)) :
    (∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
      weight v (planAt m v) (radialWidth h) frozenLeafCutoffFloor_pos
        (radialWidth_pos hh) (radialWidth_le_one hh h8) (acceptAt root tau m v) N u) ≤
    (∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
      if exactCell v root tau u then profile v h u else 0) +
      noncoprimeCount N + ((outer N v root tau m).card:ℝ) := by
  have H := sum_le_sum (fun u hu => pointwise v root tau m hN hh h8 hcut hscale hu)
  rw [sum_add_distrib,sum_add_distrib] at H
  apply H.trans
  apply add_le_add
  · apply add_le_add_left
    apply (indicator_sum_le_card _ _ id Function.injective_id).trans
    exact rank_card_le_noncoprimeCount N (rank v) (by
      have hv := v.property
      dsimp only [rank,oldRank,tailRank]
      omega)
  · exact indicator_sum_le_card _ _ wallTuple wallTuple_injective

/-- A single finite coefficient budget is chosen before any target.
The mesh may depend on the fixed Index; the same mesh serves all its
root codes and admissible tail ranks. The profile width h remains free
in (0,1/8] after the threshold. No full-product coprime premise remains. -/
theorem atlas_mass_le_exact_cell_plus_epsilon (n : ℕ) (root : Root)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ m : Index 430 → ℕ, ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      ∀ (h : ℝ) (hh : 0 < h) (h8 : h ≤ 1/8),
      norm N * (∑ v : Entry n, fixedWeight v.val.1 *
        ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
          weight v (planAt m v) (radialWidth h) frozenLeafCutoffFloor_pos
            (radialWidth_pos hh) (radialWidth_le_one hh h8)
            (acceptAt root tau m v) N u) ≤
      norm N * (∑ v : Entry n, fixedWeight v.val.1 *
        ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
          if exactCell v root tau u then
            finPhysicalProfile (log (cellQ N n v.val.2.1)) (N:ℝ) (radialWidth h)
              ((N:ℝ)^frozenLeafCutoffFloor) (fun j => ((u j).val:ℝ))
          else 0) + epsilon := by
  let A : ℝ := ∑ v : Entry n, fixedWeight v.val.1
  have hA : 0 ≤ A := sum_nonneg (fun v _ => mark_nonneg v.val.1)
  let C := A+1
  have hC : 0 < C := by dsimp only [C]; linarith
  let eta := epsilon/(2*C)
  have heta : 0 < eta := div_pos he (mul_pos (by norm_num) hC)
  have Hmesh : ∀ i : Index 430, ∃ m : ℕ, ∀ᶠ N : ℕ in atTop,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      norm N * (∑ c : RootCode n, ∑ r : Fin (frozenSourceRankBound+1),
        ((cellOuterTuples i.val.1 (oldSlotEquiv i.val.1).symm N n root tau
          i.val.2 c r.val m).card:ℝ)) ≤ eta :=
    fun i => exists_all_cells_outer_payment i.val.1 (oldSlotEquiv i.val.1).symm
      n root i.val.2 hn frozenSourceRankBound heta
  choose m Hpaid using Hmesh
  have Hall : ∀ᶠ N : ℕ in atTop, ∀ i : Index 430, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 →
      norm N * (∑ c : RootCode n, ∑ r : Fin (frozenSourceRankBound+1),
        ((cellOuterTuples i.val.1 (oldSlotEquiv i.val.1).symm N n root tau
          i.val.2 c r.val (m i)).card:ℝ)) ≤ eta :=
    eventually_all_finite.mpr Hpaid
  have Hscale : ∀ᶠ N : ℕ in atTop,
      scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine ⟨m,?_⟩
  filter_upwards [Hall,absolute_noncoprime_payment heta,eventually_cut_le_half_floor,
    Hscale,eventually_ge_atTop (2:ℕ)] with N hwall hNC hcut hscale hN
  intro tau ht ht' h hh h8
  have hnrm : 0 ≤ norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
      (Nat.cast_nonneg _)
  have hentry (v : Entry n) :
      norm N * (∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
        weight v (planAt m v) (radialWidth h) frozenLeafCutoffFloor_pos
          (radialWidth_pos hh) (radialWidth_le_one hh h8) (acceptAt root tau m v) N u) ≤
      norm N * (∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
        if exactCell v root tau u then profile v h u else 0) + 2*eta := by
    have hcard : ((outer N v root tau m).card:ℝ) ≤
        ∑ c : RootCode n, ∑ r : Fin (frozenSourceRankBound+1),
          ((cellOuterTuples v.val.1.val.1 (oldSlotEquiv v.val.1.val.1).symm
            N n root tau v.val.1.val.2 c r.val (m v.val.1)).card:ℝ) := by
      apply le_trans (single_le_sum
        (f:=fun r : Fin (frozenSourceRankBound+1) =>
          ((cellOuterTuples v.val.1.val.1 (oldSlotEquiv v.val.1.val.1).symm
            N n root tau v.val.1.val.2 v.val.2.1 r.val (m v.val.1)).card:ℝ))
        (fun _ _ => Nat.cast_nonneg _) (mem_univ v.val.2.2))
      exact single_le_sum
        (f:=fun c : RootCode n => ∑ r : Fin (frozenSourceRankBound+1),
          ((cellOuterTuples v.val.1.val.1 (oldSlotEquiv v.val.1.val.1).symm
            N n root tau v.val.1.val.2 c r.val (m v.val.1)).card:ℝ))
        (fun _ _ => sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (mem_univ v.val.2.1)
    have hc := (mul_le_mul_of_nonneg_left hcard hnrm).trans (hwall v.val.1 tau ht ht')
    have H := mul_le_mul_of_nonneg_left
      (entry_bound v root tau m hN hh h8 hcut hscale) hnrm
    rw [mul_add,mul_add] at H
    linarith
  have H := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Entry n))) =>
    mul_le_mul_of_nonneg_left (hentry v) (mark_nonneg v.val.1))
  have hbudget : A*(2*eta) ≤ epsilon := by
    calc
      _ ≤ C*(2*eta) := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
        (mul_nonneg (by norm_num) heta.le)
      _ = epsilon := by
        dsimp only [eta]
        field_simp [hC.ne']
        <;> ring
  calc
    _ = ∑ v : Entry n, fixedWeight v.val.1 *
        (norm N * ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
          weight v (planAt m v) (radialWidth h) frozenLeafCutoffFloor_pos
            (radialWidth_pos hh) (radialWidth_le_one hh h8) (acceptAt root tau m v) N u) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      ring
    _ ≤ ∑ v : Entry n, fixedWeight v.val.1 *
        (norm N * (∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
          if exactCell v root tau u then profile v h u else 0) + 2*eta) := H
    _ = norm N * (∑ v : Entry n, fixedWeight v.val.1 *
        ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N),
          if exactCell v root tau u then profile v h u else 0) + A*(2*eta) := by
      simp only [mul_add,sum_add_distrib,← sum_mul,mul_sum]
      congr 1
      apply sum_congr rfl
      intro v _
      ring
    _ ≤ _ := add_le_add_left hbudget _

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasOrdinaryExcess
