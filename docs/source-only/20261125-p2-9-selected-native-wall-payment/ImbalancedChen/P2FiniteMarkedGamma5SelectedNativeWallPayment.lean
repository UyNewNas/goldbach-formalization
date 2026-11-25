import ImbalancedChen.P2FiniteMarkedGamma5SelectedAtlasStrips
import ImbalancedChen.P2FiniteMarkedGamma5GateAffine
import ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall
import ImbalancedChen.P2PrimeProductCoordinateCore
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.Finite

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Arithmetic payment for the original finite selected native wall list.
The structural equivalence e is fixed before N. One fresh prime is
reserved, so the same argument includes the empty rough tail.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedNativeWallPayment
noncomputable section
open Filter Finset Real Set
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430NativeQueryPaths
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430SmoothPrefixRequests (physicalPrime_unit)
open Part5OriginalCausalSmoothAtlas Part5OriginalH430JointQueryEnclosure
open Part5OriginalUpsilon5CausalDictionary (a)
open P2FiniteMarkedGamma5FixedNativeItinerary (ReadLabel)
open P2FiniteMarkedGamma5SelectedNativeStrips (Form Space const coordinate)
open P2FiniteMarkedGamma5SelectedRootStrips (bandSelected fullWalls)
open P2FiniteMarkedGamma5SelectedAtlasStrips (fine_outer_strip)
open P2FiniteMarkedGamma5PhysicalExtension (Slot)
open P2FiniteMarkedGamma5GateAffine (numbering)
open P2FiniteMarkedGamma5OmittedPrimeWall
  (BoundedTuple remaining wallTuples exists_wallTuples_payment)
open P2FiniteMarkedGamma5RadialRoughMass (cut norm)
open scoped Classical BigOperators Topology

abbrev Tuple (N k r : ℕ) := BoundedTuple N (k+(1+r))

/-- The first fresh position is independent of every native old row. -/
def reserve (k r : ℕ) : Fin ((k+(1+r))+1) :=
  numbering k r (.inr (.inl 0))

variable {depth k : ℕ} (sh : Fin depth → StepShape) (e : NativeSlot sh ≃ Fin k)

private theorem old_ne_reserve (r : ℕ) (z : NativeSlot sh) :
    numbering k r (.inl (e z)) ≠ reserve k r := by
  intro h
  have h' := (numbering k r).injective h
  cases h'

/-- Inverse of succAbove only on the old labelled positions. This is
a fixed coordinate map; its definition has no arithmetic target. -/
def oldIndex (r : ℕ) (z : NativeSlot sh) : Fin (k+(1+r)) :=
  Classical.choose (Fin.exists_succAbove_eq (old_ne_reserve sh e r z))

theorem succAbove_oldIndex (r : ℕ) (z : NativeSlot sh) :
    (reserve k r).succAbove (oldIndex sh e r z) = numbering k r (.inl (e z)) :=
  Classical.choose_spec (Fin.exists_succAbove_eq (old_ne_reserve sh e r z))

def oldPullback (r : ℕ) : (Fin (k+(1+r)) → ℝ) →L[ℝ] Space sh :=
  ContinuousLinearMap.pi (fun z => ContinuousLinearMap.proj (oldIndex sh e r z))

def oldSection (r : ℕ) (x : Space sh) (j : Fin (k+(1+r))) : ℝ :=
  match (numbering k r).symm ((reserve k r).succAbove j) with
  | .inl i => x (e.symm i)
  | .inr _ => 0

theorem oldPullback_section (r : ℕ) (x : Space sh) :
    oldPullback sh e r (oldSection sh e r x) = x := by
  funext z
  change oldSection sh e r x (oldIndex sh e r z) = x z
  simp only [oldSection,succAbove_oldIndex,Equiv.symm_apply_apply]

def lifted (r : ℕ) (L : Space sh →L[ℝ] ℝ) : (Fin (k+(1+r)) → ℝ) →L[ℝ] ℝ :=
  L.comp (oldPullback sh e r)

/-- Nonzero is proved from a right inverse, not assumed for the lift. -/
theorem lifted_ne_zero (r : ℕ) {L : Space sh →L[ℝ] ℝ} (hL : L ≠ 0) :
    lifted sh e r L ≠ 0 := by
  intro h
  apply hL
  ext x
  have H := congrArg (fun F : (Fin (k+(1+r)) → ℝ) →L[ℝ] ℝ =>
    F (oldSection sh e r x)) h
  simpa only [lifted,ContinuousLinearMap.comp_apply,oldPullback_section,
    ContinuousLinearMap.zero_apply] using H

def nativeLog {N r : ℕ} (u : Tuple N k r) : Space sh :=
  fun z => physicalPrime N (u (numbering k r (.inl (e z)))).val

theorem oldPullback_log {N r : ℕ} (u : Tuple N k r) :
    oldPullback sh e r (actualPrimeTupleLog N (remaining (reserve k r) u)) =
      nativeLog sh e u := by
  funext z
  change physicalPrime N (u ((reserve k r).succAbove (oldIndex sh e r z))).val =
    physicalPrime N (u (numbering k r (.inl (e z)))).val
  rw [succAbove_oldIndex]

theorem lifted_log {N r : ℕ} (u : Tuple N k r) (q : Form (Space sh)) :
    lifted sh e r q.2 (actualPrimeTupleLog N (remaining (reserve k r) u)) - (-q.1) =
      q.1 + q.2 (nativeLog sh e u) := by
  simp only [lifted,ContinuousLinearMap.comp_apply,oldPullback_log,sub_neg_eq_add,add_comm]

def properRows (n : ℕ) (root : Root) (labels : Fin depth → ReadLabel) :
    List (Form (Space sh)) :=
  (fullWalls sh n root labels).filter (fun q => decide (q.2 ≠ 0))

def wallLinear (n : ℕ) (root : Root) (labels : Fin depth → ReadLabel) (r : ℕ) :
    Fin (properRows sh n root labels).length → (Fin (k+(1+r)) → ℝ) →L[ℝ] ℝ :=
  fun j => lifted sh e r ((properRows sh n root labels).get j).2

def wallIntercept (n : ℕ) (root : Root) (labels : Fin depth → ReadLabel) :
    Fin (properRows sh n root labels).length → ℝ :=
  fun j => -((properRows sh n root labels).get j).1

private theorem wallLinear_ne_zero (n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (r : ℕ) (j : Fin (properRows sh n root labels).length) :
    wallLinear sh e n root labels r j ≠ 0 := by
  apply lifted_ne_zero
  have h := List.get_mem (properRows sh n root labels) j
  exact of_decide_eq_true (List.mem_filter.mp h).2

def baseTuples (N k r : ℕ) : Finset (Tuple N k r) :=
  (Part3.labelledPrimeTuples ((k+(1+r))+1) (2*N)).filter fun u =>
    (∀ i, cut N ≤ ((u i).val : ℝ)) ∧ Part3.labelledProduct u ≤ 2*N ∧
      (Part3.labelledProduct u).Coprime N

def nativeWallTuples (N n : ℕ) (root : Root) (labels : Fin depth → ReadLabel)
    (r : ℕ) (delta : ℝ) : Finset (Tuple N k r) :=
  (baseTuples N k r).filter fun u =>
    ∃ q ∈ fullWalls sh n root labels, q.2 ≠ 0 ∧
      |q.1+q.2 (nativeLog sh e u)| ≤ delta

theorem nativeWallTuples_mono (N n : ℕ) (root : Root) (labels : Fin depth → ReadLabel)
    (r : ℕ) {delta delta' : ℝ} (h : delta ≤ delta') :
    nativeWallTuples sh e N n root labels r delta ⊆
      nativeWallTuples sh e N n root labels r delta' := by
  intro u hu
  obtain ⟨hb,q,hq,hnz,hw⟩ := mem_filter.mp hu
  exact mem_filter.mpr ⟨hb,q,hq,hnz,hw.trans h⟩

/-- This is a literal subset of the existing arithmetic wall count. The
intercept has sign -q.1 because its strip is |Lx-c| <= delta. -/
theorem nativeWallTuples_subset (N n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (r : ℕ) (delta : ℝ) :
    nativeWallTuples sh e N n root labels r delta ⊆
      wallTuples N (reserve k r) (wallLinear sh e n root labels r)
        (wallIntercept sh n root labels) delta := by
  intro u hu
  obtain ⟨hb,q,hq,hnz,hw⟩ := mem_filter.mp hu
  obtain ⟨hp,hfloor,hcap,hcop⟩ := mem_filter.mp hb
  have hq' : q ∈ properRows sh n root labels :=
    List.mem_filter.mpr ⟨hq,by simp only [hnz,decide_true]⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hq'
  apply mem_filter.mpr
  refine ⟨hp,hfloor,hcap,hcop,?_⟩
  change ∃ j, |wallLinear sh e n root labels r j
    (actualPrimeTupleLog N (remaining (reserve k r) u)) -
      wallIntercept sh n root labels j| ≤ delta
  refine ⟨j,?_⟩
  simpa only [wallLinear,wallIntercept,hj,lifted_log] using hw

theorem exists_native_wall_payment (n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (r : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ N : ℕ in atTop,
      norm N * ((nativeWallTuples sh e N n root labels r delta).card : ℝ) ≤ epsilon := by
  obtain ⟨delta,hd,H⟩ := exists_wallTuples_payment (by omega : 0 < k+(1+r))
    (reserve k r) (wallLinear sh e n root labels r) (wallIntercept sh n root labels)
    (wallLinear_ne_zero sh e n root labels r) he
  refine ⟨delta,hd,?_⟩
  filter_upwards [H,eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  have hnrm : 0 ≤ norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
      (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (card_le_card (nativeWallTuples_subset sh e N n root labels r delta)))
    hnrm).trans hpaid

/-- The complete product still has cap 2*N. The previously supplied
two-prime coordinate bound puts every native old coordinate in the cube. -/
theorem nativeLog_cube {N r : ℕ} (hN : 2 ≤ N) {u : Tuple N k r}
    (hu : u ∈ baseTuples N k r) : Cube (nativeLog sh e u) := by
  obtain ⟨hp,hfloor,hcap,hcop⟩ := mem_filter.mp hu
  have hprime : ∀ i, (u i).val.Prime := (mem_filter.mp hp).2
  intro z
  exact physicalPrime_unit (by omega) (hprime _).one_lt.le
    (P2PrimeProductCoordinateCore.coordinate_le_of_prod_le_two_mul (by omega)
      (fun i => (u i).val) (fun i => (hprime i).two_le) hcap _)

/-- All forms and ranks in this finite sum are fixed before the width,
and the width is fixed before the target. The r=0 term is included. -/
theorem exists_finite_tail_wall_payment (n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (K : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ N : ℕ in atTop,
      norm N * (∑ r : Fin (K+1),
        ((nativeWallTuples sh e N n root labels r.val delta).card : ℝ)) ≤ epsilon := by
  let eta := epsilon / ((K : ℝ)+1)
  have hden : 0 < (K : ℝ)+1 := by positivity
  have heta : 0 < eta := div_pos he hden
  have H : ∀ r : Fin (K+1), ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ N : ℕ in atTop,
      norm N * ((nativeWallTuples sh e N n root labels r.val delta).card : ℝ) ≤ eta :=
    fun r => exists_native_wall_payment sh e n root labels r.val heta
  choose delta hdelta Hpaid using H
  obtain ⟨r0,_,hmin⟩ := exists_min_image (univ : Finset (Fin (K+1))) delta
    (by exact ⟨0,mem_univ _⟩)
  refine ⟨delta r0,hdelta r0,?_⟩
  have Hall : ∀ᶠ N : ℕ in atTop, ∀ r : Fin (K+1),
      norm N * ((nativeWallTuples sh e N n root labels r.val (delta r)).card : ℝ) ≤ eta :=
    (eventually_all_finite).mpr Hpaid
  filter_upwards [Hall,eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  have hnrm : 0 ≤ norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
      (Nat.cast_nonneg _)
  calc
    _ = ∑ r : Fin (K+1), norm N *
        ((nativeWallTuples sh e N n root labels r.val (delta r0)).card : ℝ) := mul_sum ..
    _ ≤ ∑ _r : Fin (K+1), eta := by
      apply sum_le_sum
      intro r hr
      exact (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (card_le_card (nativeWallTuples_mono sh e N n root labels r.val
          (hmin r (mem_univ r))))) hnrm).trans (hpaid r)
    _ = ((K : ℝ)+1) * eta := by simp
    _ = epsilon := by
      dsimp only [eta]
      rw [mul_comm,div_mul_cancel₀ _ hden.ne']

def upperEndpoint : Root → ℝ
  | .U3 => 1/3
  | .U4 => 59/250

def upperForm (root : Root) : Form (Space sh) :=
  const (upperEndpoint root) - coordinate sh (.inl ())

theorem upperForm_mem (n : ℕ) (root : Root) (labels : Fin depth → ReadLabel) :
    upperForm sh root ∈ fullWalls sh n root labels := by
  unfold fullWalls
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem upperForm_ne_zero (root : Root) : (upperForm sh root).2 ≠ 0 := by
  intro h
  have H := congrArg (fun L : Space sh →L[ℝ] ℝ => L (fun _ => 1)) h
  norm_num [upperForm,const,coordinate] at H

theorem upperForm_zero (root : Root) (x : Space sh)
    (hx : x (.inl ()) = upperEndpoint root) :
    (upperForm sh root).1 + (upperForm sh root).2 x = 0 := by
  simp [upperForm,const,coordinate,hx]

/-- The only closed-band point rejected by the original strict-upper
selector is its upper endpoint. This uses only the original selector
and monotonicity of log, with primality/coprimality explicitly supplied. -/
theorem closed_band_not_original_endpoint {N p : ℕ} (root : Root)
    (hN : 2 ≤ N) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand root) (hnot : p ∉ originalBand N root) :
    physicalPrime N p = upperEndpoint root := by
  have hband : a ≤ physicalPrime N p ∧ physicalPrime N p ≤ upperEndpoint root := by
    cases root <;> exact hb
  by_contra hne
  have hu : physicalPrime N p < upperEndpoint root := by
    rcases lt_or_eq_of_le hband.2 with hu | heq
    · exact hu
    · exact False.elim (hne heq)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  have hU : upperEndpoint root < 1 := by cases root <;> norm_num [upperEndpoint]
  have hpN : p < N := by
    have hh : log (p : ℝ) / log (N : ℝ) < 1 := hu.trans hU
    have hh' : log (p : ℝ) < log (N : ℝ) := by
      simpa only [one_mul] using (div_lt_iff₀ hlog).mp hh
    exact_mod_cast (log_lt_log_iff hpR hNpos).mp hh'
  have hlo : (N : ℝ)^a ≤ p := by
    apply (log_le_log_iff (rpow_pos_of_pos hNpos a) hpR).mp
    rw [log_rpow hNpos]
    exact (le_div_iff₀ hlog).mp hband.1
  have hhi : (p : ℝ) < (N : ℝ)^(upperEndpoint root) := by
    apply (log_lt_log_iff hpR (rpow_pos_of_pos hNpos _)).mp
    rw [log_rpow hNpos]
    exact (div_lt_iff₀ hlog).mp hu
  have hcarrier : p ∈ chenAdditivePrimeCarrier N :=
    mem_chenAdditivePrimeCarrier.mpr ⟨hpN,hp.1,hp.2⟩
  apply hnot
  cases root <;> exact mem_filter.mpr ⟨hcarrier,hlo,hhi⟩

/-- An actual root-band rejection inside the closed selected domain
therefore has an exact proper zero-wall witness in the same full list. -/
theorem original_root_zero_wall {N p : ℕ} (n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (x : Space sh) (hN : 2 ≤ N)
    (hp : p.Prime ∧ p.Coprime N) (hx : x (.inl ()) = physicalPrime N p)
    (hb : x (.inl ()) ∈ rootBand root) (hnot : p ∉ originalBand N root) :
    ∃ q ∈ fullWalls sh n root labels, q.2 ≠ 0 ∧ q.1+q.2 x=0 := by
  refine ⟨upperForm sh root,upperForm_mem sh n root labels,upperForm_ne_zero sh root,?_⟩
  exact upperForm_zero sh root x (hx.trans
    (closed_band_not_original_endpoint root hN hp (by simpa only [hx] using hb) hnot))

def outerTuples (N n : ℕ) (root : Root) (tau : ℝ)
    (labels : Fin depth → ReadLabel) (r m : ℕ) : Finset (Tuple N k r) :=
  (baseTuples N k r).filter fun u =>
    readout (.mesh m) (hit (.mesh m) (bandSelected sh n root tau labels))
      (nativeLog sh e u) ≠ 0 ∧
    ¬ ((u (numbering k r (.inl (e (.inl ()))))).val ∈ originalBand N root ∧
      nativeLog sh e u ∈ P2FiniteMarkedGamma5RealSelectedPrefix.selected n root tau sh labels)

/-- The mesh is common to every later N and every tail rank. The
pointwise inclusion also pays the closed/strict root-endpoint mismatch. -/
theorem exists_outer_cover (n : ℕ) (root : Root) (labels : Fin depth → ReadLabel)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) {delta : ℝ} (hd : 0 < delta) :
    ∃ m : ℕ, ∀ N : ℕ, 2 ≤ N → ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 → ∀ r : ℕ,
      outerTuples sh e N n root tau labels r m ⊆
        nativeWallTuples sh e N n root labels r delta := by
  obtain ⟨m,H⟩ := fine_outer_strip sh n root labels hd hn
  refine ⟨m,?_⟩
  intro N hN tau ht ht' r u hu
  obtain ⟨hb,hout,hfail⟩ := mem_filter.mp hu
  apply mem_filter.mpr
  refine ⟨hb,?_⟩
  by_cases hclosed : nativeLog sh e u ∈ bandSelected sh n root tau labels
  · have hp : ∀ i, (u i).val.Prime := (mem_filter.mp (mem_filter.mp hb).1).2
    have hcop := (mem_filter.mp hb).2.2.2
    let j := numbering k r (.inl (e (.inl ())))
    have hroot : (u j).val.Prime ∧ (u j).val.Coprime N :=
      ⟨hp j,hcop.of_dvd_left (dvd_prod_of_mem (fun i => (u i).val) (mem_univ j))⟩
    have hnot : (u j).val ∉ originalBand N root := fun h => hfail ⟨h,hclosed.2⟩
    obtain ⟨q,hq,hnz,hzero⟩ := original_root_zero_wall sh n root labels
      (nativeLog sh e u) hN hroot rfl hclosed.1 hnot
    exact ⟨q,hq,hnz,by rw [hzero,abs_zero]; exact hd.le⟩
  · exact H tau ht ht' (nativeLog sh e u) (nativeLog_cube sh e hN hb) hclosed hout

/-- One arithmetic epsilon pays the finite sum of all tails 0..K.
The old labelled shape, reads, structural equivalence and precision
precede the mesh; the mesh and threshold precede N and tau. -/
theorem exists_selected_outer_payment (n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (K : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ m : ℕ, ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      norm N * (∑ r : Fin (K+1),
        ((outerTuples sh e N n root tau labels r.val m).card : ℝ)) ≤ epsilon := by
  obtain ⟨delta,hd,Hpaid⟩ := exists_finite_tail_wall_payment sh e n root labels K he
  obtain ⟨m,Hcover⟩ := exists_outer_cover sh e n root labels hn hd
  refine ⟨m,?_⟩
  filter_upwards [Hpaid,eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  intro tau ht ht'
  have hnrm : 0 ≤ norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
      (Nat.cast_nonneg _)
  apply le_trans (mul_le_mul_of_nonneg_left ?_ hnrm) hpaid
  apply sum_le_sum
  intro r hr
  exact Nat.cast_le.mpr (card_le_card (Hcover N hN tau ht ht' r.val))

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedNativeWallPayment
