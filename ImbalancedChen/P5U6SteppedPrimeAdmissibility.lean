import ImbalancedChen.CurrentChenUpsilon6OrdinaryMean
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.P5U6AdoptedH248Binding

/-!
SOURCE_ONLY / UNCOMPILED. Native U6 prime-pair PNT on actual h248 atoms and
fixed half-open logboxes. An eleven-form strict/weak affine sandwich controls
the arithmetic atoms even at exact lookup knots. Null Lebesgue lines are
never used to delete arithmetic prime tuples. No desired harmonic limit is
a premise, and no causal lower-coefficient correctness is asserted here.
-/

namespace ImbalancedChen.P5U6SteppedPrimeAdmissibilitySourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open P5U6AdoptedH248BindingSourceOnly
open Part5OriginalUpsilon5CausalDictionary

abbrev Point := Fin 2 → ℝ

def box (l r : Fin 2 → ℝ) : Set Point :=
  {x | l 0 ≤ x 0 ∧ x 0 < r 0 ∧ l 1 ≤ x 1 ∧ x 1 < r 1}

theorem measurableSet_box (l r : Fin 2 → ℝ) : MeasurableSet (box l r) := by
  exact ((isClosed_le continuous_const (continuous_apply 0)).measurableSet).inter
    (((isOpen_lt (continuous_apply 0) continuous_const).measurableSet).inter
      (((isClosed_le continuous_const (continuous_apply 1)).measurableSet).inter
        (isOpen_lt (continuous_apply 1) continuous_const).measurableSet))

def scalarBox (S : Set ℝ) (l r : Fin 2 → ℝ) : Set Point :=
  {x | currentChenUpsilon6OrdinaryProfile x ∈ S} ∩ box l r

theorem measurableSet_scalarBox {S : Set ℝ} (hS : MeasurableSet S) (l r : Fin 2 → ℝ) :
    MeasurableSet (scalarBox S l r) := by
  have hc : Continuous currentChenUpsilon6OrdinaryProfile := by
    unfold currentChenUpsilon6OrdinaryProfile
    fun_prop
  exact (hS.preimage hc.measurable).inter (measurableSet_box l r)

def region (eta : ℝ) (S : Set ℝ) (l r : Fin 2 → ℝ) : Set Point :=
  currentChenUpsilon6OrdinaryStrictDomain eta ∩ scalarBox S l r

theorem measurableSet_strictDomain (eta : ℝ) :
    MeasurableSet (currentChenUpsilon6OrdinaryStrictDomain eta) :=
  measurableSet_currentChenUpsilon6LogRectangle.inter
    (((isOpen_lt continuous_const (continuous_apply 1)).measurableSet).inter
      (isOpen_lt ((continuous_apply 0).add (continuous_apply 1)) continuous_const).measurableSet)

theorem measurableSet_region (eta : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (l r : Fin 2 → ℝ) :
    MeasurableSet (region eta S l r) :=
  (measurableSet_strictDomain eta).inter (measurableSet_scalarBox hS l r)

private def xForm : Point →L[ℝ] ℝ := ContinuousLinearMap.proj 0
private def yForm : Point →L[ℝ] ℝ := ContinuousLinearMap.proj 1

def forms : Fin 11 → Point →L[ℝ] ℝ :=
  ![-xForm, xForm, -yForm, yForm, xForm + yForm,
    xForm + yForm, -(xForm + yForm), -xForm, xForm, -yForm, yForm]

def caps (eta lo hi : ℝ) (l r : Fin 2 → ℝ) : Fin 11 → ℝ :=
  ![-(417 / 5000 : ℝ), 19 / 125, -(19 / 125), 59 / 250,
    (833 / 2500 : ℝ) - eta, (1 / 2 : ℝ) - (417 / 5000 : ℝ) * lo,
    -((1 / 2 : ℝ) - (417 / 5000 : ℝ) * hi), -l 0, r 0, -l 1, r 1]

theorem forms_ne_zero : ∀ j, forms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (fun _ => 1)) h
  fin_cases j <;> norm_num [forms, xForm, yForm] at hh

private theorem mem_gates (eta lo hi : ℝ) (l r : Fin 2 → ℝ) (x : Point) :
    x ∈ primeAffineGateRegion forms (caps eta lo hi l r) ↔
      (417 / 5000 : ℝ) < x 0 ∧ x 0 < 19 / 125 ∧ (19 / 125 : ℝ) < x 1 ∧ x 1 < 59 / 250 ∧
      x 0 + x 1 < (833 / 2500 : ℝ) - eta ∧
      x 0 + x 1 < (1 / 2 : ℝ) - (417 / 5000 : ℝ) * lo ∧
      (1 / 2 : ℝ) - (417 / 5000 : ℝ) * hi < x 0 + x 1 ∧
      l 0 < x 0 ∧ x 0 < r 0 ∧ l 1 < x 1 ∧ x 1 < r 1 := by
  simp [primeAffineGateRegion, forms, caps, xForm, yForm, Fin.forall_fin_succ,
    neg_lt_neg_iff, and_assoc]

private theorem strict_subset_weak (eta : ℝ) :
    currentChenUpsilon6OrdinaryStrictDomain eta ⊆ currentChenUpsilon6LogDomain eta := by
  intro x hx
  exact ⟨hx.1, hx.2.2.le⟩

/-- Actual scalar atoms may have any boundary ownership sandwiched between
open and closed endpoints. This includes half-open cells AND singletons. -/
theorem region_sandwich {eta lo hi : ℝ} (heta : 0 ≤ eta) {S : Set ℝ}
    (hlo : Ioo lo hi ∩ Icc (2 : ℝ) 5 ⊆ S)
    (hhi : S ∩ Icc (2 : ℝ) 5 ⊆ Icc lo hi) (l r : Fin 2 → ℝ) :
    primeAffineGateRegion forms (caps eta lo hi l r) ⊆ region eta S l r ∧
      ∀ x ∈ region eta S l r, ∀ j, forms j x ≤ caps eta lo hi l r j := by
  constructor
  · intro x hx
    obtain ⟨ha, hh, hv, hd, hp, hslo, hshi, hlu, hru, hlv, hrv⟩ :=
      (mem_gates eta lo hi l r x).mp hx
    have hxstrict : x ∈ currentChenUpsilon6OrdinaryStrictDomain eta :=
      ⟨mem_currentChenUpsilon6LogRectangle.mpr ⟨ha.le, hh, hv.le, hd⟩, hv, hp⟩
    have hpr := profile_range heta (strict_subset_weak eta hxstrict)
    have hrange : currentChenUpsilon6OrdinaryProfile x ∈ Icc (2 : ℝ) 5 :=
      ⟨hpr.1, hpr.2.trans (by norm_num)⟩
    have hprof : currentChenUpsilon6OrdinaryProfile x ∈ Ioo lo hi := by
      unfold currentChenUpsilon6OrdinaryProfile
      constructor <;> norm_num <;> linarith
    exact ⟨hxstrict, hlo ⟨hprof, hrange⟩, hlu.le, hru, hlv.le, hrv⟩
  · intro x hx j
    obtain ⟨hxstrict, hS, hl0, hr0, hl1, hr1⟩ := hx
    obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hxstrict.1
    have hp := hxstrict.2.2
    have hhstrict := hxstrict.2.1
    have hpr := profile_range heta (strict_subset_weak eta hxstrict)
    have hprof := hhi ⟨hS, hpr.1, hpr.2.trans (by norm_num)⟩
    have hslo : x 0 + x 1 ≤ (1 / 2 : ℝ) - (417 / 5000 : ℝ) * lo := by
      have hl := hprof.1
      unfold currentChenUpsilon6OrdinaryProfile at hl
      norm_num at hl
      linarith
    have hshi : (1 / 2 : ℝ) - (417 / 5000 : ℝ) * hi ≤ x 0 + x 1 := by
      have hh' := hprof.2
      unfold currentChenUpsilon6OrdinaryProfile at hh'
      norm_num at hh'
      linarith
    fin_cases j <;> norm_num [forms, caps, xForm, yForm] <;> linarith

private theorem region_subset_cube (eta : ℝ) (S : Set ℝ) (l r : Fin 2 → ℝ) :
    region eta S l r ⊆ logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) := by
  intro x hx
  obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1.1
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  · exact ⟨ha, hh.trans (by norm_num)⟩
  · exact ⟨(by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hv, hd⟩

def nativeTest (N : ℕ) (eta : ℝ) (S : Set ℝ) (l r : Fin 2 → ℝ) (f : Point → ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
    (scalarBox S l r).indicator f (actualPrimeTupleLog N ![t.1, t.2]) /
      (Nat.totient (t.1 * t.2) : ℝ)

/-- Exact original native pair reindexing with the new discontinuous atom
and literal box gates. No prime-pair wall value is deleted. -/
theorem nativeTest_eq_actualPrimeBox {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) (S : Set ℝ) (l r : Fin 2 → ℝ) (f : Point → ℝ) :
    nativeTest N eta S l r f =
      actualPrimeBoxTestSum N (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ((region eta S l r).indicator f) := by
  rw [nativeTest, currentChenUpsilon6Ordinary_harmonic_eq_actualPrimeBox hN]
  unfold actualPrimeBoxTestSum
  apply Finset.sum_congr rfl
  intro p hp
  have hcube := ((mem_actualPrimeBoxTuples_log_iff (show 1 < N by omega) _ _ p).mp hp).2
  have hstrict : actualPrimeTupleLog N p ∈ currentChenUpsilon6OrdinaryStrictDomain eta ↔
      actualPrimeTupleLog N p ∈ primeAffineGateRegion currentChenUpsilon6OrdinaryForms
        (currentChenUpsilon6OrdinaryCaps eta) := by
    rw [← currentChenUpsilon6Ordinary_cube_gates_eq eta]
    simp only [mem_inter_iff, hcube, true_and]
  congr 1
  by_cases hg : actualPrimeTupleLog N p ∈ primeAffineGateRegion currentChenUpsilon6OrdinaryForms
      (currentChenUpsilon6OrdinaryCaps eta)
  · by_cases hm : actualPrimeTupleLog N p ∈ scalarBox S l r
    · have hr : actualPrimeTupleLog N p ∈ region eta S l r := ⟨hstrict.mpr hg, hm⟩
      rw [indicator_of_mem hg, indicator_of_mem hm, indicator_of_mem hr]
    · have hr : actualPrimeTupleLog N p ∉ region eta S l r := fun h => hm h.2
      rw [indicator_of_mem hg, indicator_of_notMem hm, indicator_of_notMem hr]
  · have hr : actualPrimeTupleLog N p ∉ region eta S l r := fun h => hg (hstrict.mp h.1)
    rw [indicator_of_notMem hg, indicator_of_notMem hr]

private theorem strict_mask_integral_eq (eta : ℝ) (A : Set Point) (hA : MeasurableSet A)
    (g : Point → ℝ) :
    (∫ x in currentChenUpsilon6OrdinaryStrictDomain eta ∩ A, g x) =
      ∫ x in currentChenUpsilon6LogDomain eta ∩ A, g x := by
  calc
    _ = ∫ x in currentChenUpsilon6OrdinaryStrictDomain eta, A.indicator g x :=
      (setIntegral_indicator hA).symm
    _ = ∫ x in currentChenUpsilon6LogDomain eta, A.indicator g x :=
      integral_currentChenUpsilon6OrdinaryStrictDomain_eq eta _
    _ = _ := setIntegral_indicator hA

/-- Genuine native prime-pair mean on every admissible slanted cell/box,
from the proved two-dimensional PNT sandwich, with no desired-limit premise. -/
theorem tendsto_nativeTest {eta lo hi : ℝ} (heta : 0 ≤ eta) {S : Set ℝ}
    (hS : MeasurableSet S) (hlo : Ioo lo hi ∩ Icc (2 : ℝ) 5 ⊆ S)
    (hhi : S ∩ Icc (2 : ℝ) 5 ⊆ Icc lo hi) (l r : Fin 2 → ℝ) (f : Point → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250)))) :
    Tendsto (fun N => nativeTest N eta S l r f) atTop
      (𝓝 (∫ x in currentChenUpsilon6LogDomain eta ∩ scalarBox S l r,
        f x * ∏ i, 1 / x i)) := by
  have hsand := region_sandwich heta hlo hhi l r
  have h := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0 : ℝ) < 417 / 5000) (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    forms (caps eta lo hi l r) forms_ne_zero (region eta S l r)
    (measurableSet_region eta hS l r) hsand.1 hsand.2 f hf
  rw [inter_eq_right.mpr (region_subset_cube eta S l r)] at h
  have hI : (∫ x in region eta S l r, f x * ∏ i, 1 / x i) =
      ∫ x in currentChenUpsilon6LogDomain eta ∩ scalarBox S l r, f x * ∏ i, 1 / x i :=
    strict_mask_integral_eq eta _ (measurableSet_scalarBox hS l r) _
  rw [hI] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (nativeTest_eq_actualPrimeBox hN eta S l r f).symm

def atomLo : FloorAtom → ℝ
  | .inl i => floorGrid i.val
  | .inr j => floorGrid j.val

def atomHi : FloorAtom → ℝ
  | .inl i => floorGrid (i.val + 1)
  | .inr j => floorGrid j.val

theorem atom_scalar_sandwich (b : FloorAtom) :
    Ioo (atomLo b) (atomHi b) ∩ Icc (2 : ℝ) 5 ⊆ floorAtomSet b ∧
      floorAtomSet b ∩ Icc (2 : ℝ) 5 ⊆ Icc (atomLo b) (atomHi b) := by
  cases b with
  | inl i =>
    constructor
    · exact fun s h => ⟨h.2, h.1⟩
    · exact fun s h => ⟨h.1.2.1.le, h.1.2.2.le⟩
  | inr j =>
    constructor
    · intro s h
      have hlt := h.1
      exact False.elim (by change floorGrid j.val < s ∧ s < floorGrid j.val at hlt; linarith [hlt.1, hlt.2])
    · intro s h
      have heq : s = floorGrid j.val := h.1.2
      exact ⟨heq.ge, heq.le⟩

/-- All401 adopted table atoms, INCLUDING knot singletons, are genuinely
prime-test admissible on every fixed corrected buffer and literal logbox. -/
theorem tendsto_nativeAtom (eta : ℝ) (heta : 0 ≤ eta) (b : FloorAtom)
    (l r : Fin 2 → ℝ) (f : Point → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250)))) :
    Tendsto (fun N => nativeTest N eta (floorAtomSet b) l r f) atTop
      (𝓝 (∫ x in currentChenUpsilon6LogDomain eta ∩ scalarBox (floorAtomSet b) l r,
        f x * ∏ i, 1 / x i)) :=
  tendsto_nativeTest heta (measurableSet_floorAtomSet b)
    (atom_scalar_sandwich b).1 (atom_scalar_sandwich b).2 l r f hf

/-- Exact lookup-knot arithmetic harmonic masses tend to zero by the actual
prime sandwich. Only the limiting integral is removed using affine nullity. -/
theorem tendsto_nativeKnot_zero (eta : ℝ) (heta : 0 ≤ eta) (j : Fin 201)
    (l r : Fin 2 → ℝ) (f : Point → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250)))) :
    Tendsto (fun N => nativeTest N eta (floorAtomSet (.inr j)) l r f) atTop (𝓝 0) := by
  have hz : volume (currentChenUpsilon6LogDomain eta ∩ scalarBox (floorAtomSet (.inr j)) l r) = 0 := by
    apply measure_mono_null _ (profile_wall_volume_zero (floorGrid j.val))
    intro x hx
    exact hx.2.1.2
  have hzero : (∫ x in currentChenUpsilon6LogDomain eta ∩ scalarBox (floorAtomSet (.inr j)) l r,
      f x * ∏ i, 1 / x i) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]
  simpa only [hzero] using tendsto_nativeAtom eta heta (.inr j) l r f hf

end

end ImbalancedChen.P5U6SteppedPrimeAdmissibilitySourceOnly
