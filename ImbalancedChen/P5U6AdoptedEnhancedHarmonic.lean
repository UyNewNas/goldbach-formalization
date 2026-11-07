import ImbalancedChen.P5U6SteppedPrimeAdmissibility
import ImbalancedChen.P5U6RetainedAdoptedIntegral

/-!
SOURCE_ONLY / UNCOMPILED. Original adopted stepped-h248 harmonic mean on
each fixed corrected buffer and literal half-open logbox. Every one of the
401 scalar atoms, including exact knots, uses a proved native two-dimensional
prime-test limit. Only finite sums are exchanged. The final kernel has the
correct original R denominator. No sieve-density or causal lower supplier
is asserted by this independent harmonic theorem.
-/

namespace ImbalancedChen.P5U6AdoptedEnhancedHarmonicSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open Part5OriginalUpsilon5CausalDictionary
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open P5U6AdoptedH248BindingSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly
open P5U6SteppedPrimeAdmissibilitySourceOnly

abbrev Point := Fin 2 → ℝ

def bareCorrection (x : Point) : ℝ := 4 / originalResidual x

theorem continuousOn_bareCorrection :
    ContinuousOn bareCorrection (Set.univ.pi
      (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250))) := by
  have hR : Continuous originalResidual := by unfold originalResidual; fun_prop
  unfold bareCorrection
  apply continuousOn_const.div hR.continuousOn
  intro x hx
  have h0 := (hx 0 (mem_univ _)).2
  have h1 := (hx 1 (mem_univ _)).2
  have hpos : 0 < originalResidual x := by unfold originalResidual; linarith
  exact hpos.ne'

def nativeSteppedTest (N : ℕ) (eta : ℝ) (l r : Fin 2 → ℝ) (f : Point → ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
    (box l r).indicator (fun x => adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * f x)
      (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)

private theorem stepped_box_pointwise (l r : Fin 2 → ℝ) (f : Point → ℝ) (x : Point) :
    (box l r).indicator (fun x => adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * f x) x =
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        (scalarBox (floorAtomSet b) l r).indicator f x := by
  by_cases hx : x ∈ box l r
  · rw [indicator_of_mem hx]
    unfold adoptedH248Floor floorStep
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hs : currentChenUpsilon6OrdinaryProfile x ∈ floorAtomSet b
    · have hsb : x ∈ scalarBox (floorAtomSet b) l r := ⟨hs, hx⟩
      rw [indicator_of_mem hs, indicator_of_mem hsb]
    · have hsb : x ∉ scalarBox (floorAtomSet b) l r := fun h => hs h.1
      rw [indicator_of_notMem hs, indicator_of_notMem hsb]
      ring
  · rw [indicator_of_notMem hx]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hb : x ∉ scalarBox (floorAtomSet b) l r := fun h => hx h.2
    rw [indicator_of_notMem hb, mul_zero]

/-- Actual finite prime sums preserve all401 closed-lookup atoms exactly. -/
theorem nativeSteppedTest_eq_atom_sum (N : ℕ) (eta : ℝ) (l r : Fin 2 → ℝ) (f : Point → ℝ) :
    nativeSteppedTest N eta l r f =
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        nativeTest N eta (floorAtomSet b) l r f := by
  unfold nativeSteppedTest nativeTest
  simp_rw [stepped_box_pointwise, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem domain_subset_cube (eta : ℝ) :
    currentChenUpsilon6LogDomain eta ⊆ logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) := by
  intro x hx
  obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  · exact ⟨ha, hh.trans (by norm_num)⟩
  · exact ⟨(by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hv, hd⟩

private theorem integrable_atomDensity (eta : ℝ) (b : FloorAtom) (l r : Fin 2 → ℝ)
    (f : Point → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250)))) :
    IntegrableOn ((scalarBox (floorAtomSet b) l r).indicator
      (fun x => f x * ∏ i, 1 / x i)) (currentChenUpsilon6LogDomain eta) :=
  ((integrableOn_logPrimeBox_test_cube (by norm_num : (0 : ℝ) < 417 / 5000) f hf).mono_set
    (domain_subset_cube eta)).indicator
      (measurableSet_scalarBox (measurableSet_floorAtomSet b) l r)

/-- The genuine stepped integral is the finite sum of actual atom integrals.
No certificate value or recurrence conclusion is substituted for an integral. -/
theorem integral_stepped_eq_atom_sum (eta : ℝ) (l r : Fin 2 → ℝ) (f : Point → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250)))) :
    (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r,
      (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * f x) * ∏ i, 1 / x i) =
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        ∫ x in currentChenUpsilon6LogDomain eta ∩ scalarBox (floorAtomSet b) l r,
          f x * ∏ i, 1 / x i := by
  rw [← setIntegral_indicator (measurableSet_box l r)]
  have hpoint (x : Point) :
      (box l r).indicator (fun x => (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * f x) *
        ∏ i, 1 / x i) x =
      ∑ b : FloorAtom, floorAtomValue adoptedH248Numerators b *
        (scalarBox (floorAtomSet b) l r).indicator (fun x => f x * ∏ i, 1 / x i) x := by
    have hp := stepped_box_pointwise l r (fun x => f x * ∏ i, 1 / x i) x
    have hfun : (fun y : Point =>
        (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile y) * f y) * ∏ i, 1 / y i) =
        (fun y : Point => adoptedH248Floor (currentChenUpsilon6OrdinaryProfile y) *
          (f y * ∏ i, 1 / y i)) := by
      funext y
      ring
    rw [hfun]
    exact hp
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun b _ => (integrable_atomDensity eta b l r f hf).const_mul _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul,
    setIntegral_indicator (measurableSet_scalarBox (measurableSet_floorAtomSet b) l r)]

/-- Native harmonic limit for the actual discontinuous adopted floor,
obtained by finite synthesis of real prime-PNT cell and knot suppliers. -/
theorem tendsto_nativeSteppedTest (eta : ℝ) (heta : 0 ≤ eta) (l r : Fin 2 → ℝ) (f : Point → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin 2 => Icc (417 / 5000 : ℝ) (59 / 250)))) :
    Tendsto (fun N => nativeSteppedTest N eta l r f) atTop
      (𝓝 (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r,
        (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * f x) * ∏ i, 1 / x i)) := by
  have h := tendsto_finsetSum Finset.univ (fun b _ =>
    (tendsto_nativeAtom eta heta b l r f hf).const_mul (floorAtomValue adoptedH248Numerators b))
  rw [← integral_stepped_eq_atom_sum eta l r f hf] at h
  exact h.congr' (Eventually.of_forall (fun N => (nativeSteppedTest_eq_atom_sum N eta l r f).symm))

def nativeOrdinaryBoxTest (N : ℕ) (eta : ℝ) (l r : Fin 2 → ℝ) : ℝ :=
  nativeTest N eta Set.univ l r currentChenUpsilon6OrdinaryClippedTest

def nativeEnhancedBoxTest (N : ℕ) (eta : ℝ) (l r : Fin 2 → ℝ) : ℝ :=
  nativeOrdinaryBoxTest N eta l r + nativeSteppedTest N eta l r bareCorrection

private theorem scalarBox_univ (l r : Fin 2 → ℝ) : scalarBox Set.univ l r = box l r := by
  ext x
  simp [scalarBox]

/-- The enhanced object is one literal native pair sum with its original
reciprocal-totient coefficient, rather than an assumed limiting functional. -/
theorem nativeEnhancedBoxTest_eq_pair_sum (N : ℕ) (eta : ℝ) (l r : Fin 2 → ℝ) :
    nativeEnhancedBoxTest N eta l r =
      ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
        (box l r).indicator (fun x => currentChenUpsilon6OrdinaryClippedTest x +
          adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x)
            (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ) := by
  unfold nativeEnhancedBoxTest nativeOrdinaryBoxTest nativeTest nativeSteppedTest
  rw [scalarBox_univ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← add_div]
  congr 1
  by_cases hx : actualPrimeTupleLog N ![t.1, t.2] ∈ box l r
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
    ring

private theorem ordinary_density_eq {x : Point} (hx : x ∈ currentChenUpsilon6LogRectangle) :
    currentChenUpsilon6OrdinaryClippedTest x * (∏ i : Fin 2, 1 / x i) =
      currentChenUpsilon6OrdinaryKernel x := by
  rw [currentChenUpsilon6OrdinaryClippedTest_eq hx]
  unfold currentChenUpsilon6OrdinaryFactor currentChenUpsilon6OrdinaryKernel
  simp only [Fin.prod_univ_two]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem correction_density_eq (x : Point) :
    (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x) *
      (∏ i : Fin 2, 1 / x i) = originalEnhancement adoptedH248Floor x := by
  unfold bareCorrection originalEnhancement
  simp only [Fin.prod_univ_two, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Complete fixed-buffer original enhanced native harmonic mean on each
literal half-open logbox. Its limit is the actual adopted estimator integral. -/
theorem tendsto_nativeEnhancedBoxTest (eta : ℝ) (heta : 0 ≤ eta) (l r : Fin 2 → ℝ) :
    Tendsto (fun N => nativeEnhancedBoxTest N eta l r) atTop
      (𝓝 (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r, adoptedKernel x)) := by
  have ho := tendsto_nativeTest (lo := (2 : ℝ)) (hi := (5 : ℝ)) heta measurableSet_univ
    (by intro s hs; trivial) (by intro s hs; exact hs.2) l r
    currentChenUpsilon6OrdinaryClippedTest continuous_currentChenUpsilon6OrdinaryClippedTest.continuousOn
  rw [scalarBox_univ] at ho
  have hIord : (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r,
      currentChenUpsilon6OrdinaryClippedTest x * ∏ i, 1 / x i) =
        ∫ x in currentChenUpsilon6LogDomain eta ∩ box l r, currentChenUpsilon6OrdinaryKernel x := by
    apply setIntegral_congr_fun
      ((P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter (measurableSet_box l r))
    intro x hx
    exact ordinary_density_eq hx.1.1
  rw [hIord] at ho
  have hc := tendsto_nativeSteppedTest eta heta l r bareCorrection continuousOn_bareCorrection
  have hIcorr : (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r,
      (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x) * ∏ i, 1 / x i) =
        ∫ x in currentChenUpsilon6LogDomain eta ∩ box l r, originalEnhancement adoptedH248Floor x := by
    apply setIntegral_congr_fun
      ((P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter (measurableSet_box l r))
    intro x _
    exact correction_density_eq x
  rw [hIcorr] at hc
  have h := ho.add hc
  have hI : (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r, adoptedKernel x) =
      (∫ x in currentChenUpsilon6LogDomain eta ∩ box l r, currentChenUpsilon6OrdinaryKernel x) +
        ∫ x in currentChenUpsilon6LogDomain eta ∩ box l r, originalEnhancement adoptedH248Floor x :=
    integral_add ((integrableOn_currentChenUpsilon6OrdinaryKernel_domain eta).mono_set inter_subset_left)
      ((integrableOn_adoptedEnhancement heta).mono_set inter_subset_left)
  rw [← hI] at h
  exact h

/-- Finite original mask-box families may be selected before N. This is the
actual finite sum of box integrals; disjoint-mask identification is separate. -/
theorem tendsto_finite_box_sum {m : ℕ} (eta : ℝ) (heta : 0 ≤ eta)
    (l r : Fin m → Fin 2 → ℝ) :
    Tendsto (fun N => ∑ j : Fin m, nativeEnhancedBoxTest N eta (l j) (r j)) atTop
      (𝓝 (∑ j : Fin m, ∫ x in currentChenUpsilon6LogDomain eta ∩ box (l j) (r j), adoptedKernel x)) :=
  tendsto_finsetSum Finset.univ (fun j _ => tendsto_nativeEnhancedBoxTest eta heta (l j) (r j))

def boxMask {m : ℕ} (l r : Fin m → Fin 2 → ℝ) : Set Point := ⋃ j, box (l j) (r j)

theorem measurableSet_boxMask {m : ℕ} (l r : Fin m → Fin 2 → ℝ) :
    MeasurableSet (boxMask l r) := MeasurableSet.iUnion (fun j => measurableSet_box (l j) (r j))

theorem selected_boxMask_integral_eq_sum {m : ℕ} (eta : ℝ) (heta : 0 ≤ eta)
    (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j)))) :
    selectedEstimatorIntegral (fun x => x ∈ boxMask l r) eta =
      ∑ j : Fin m, ∫ x in currentChenUpsilon6LogDomain eta ∩ box (l j) (r j), adoptedKernel x := by
  have hset : currentChenUpsilon6LogDomain eta ∩ boxMask l r =
      ⋃ j : Fin m, currentChenUpsilon6LogDomain eta ∩ box (l j) (r j) := by
    ext x
    simp [boxMask]
  change (∫ x in currentChenUpsilon6LogDomain eta ∩ boxMask l r, adoptedKernel x) = _
  rw [hset]
  exact integral_iUnion_fintype
    (fun j => (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter
      (measurableSet_box (l j) (r j)))
    (fun i j hij => (hdis hij).mono inter_subset_right inter_subset_right)
    (fun _j => (integrableOn_adoptedEnhancedKernel heta).mono_set inter_subset_left)

def nativeRetainedBoxFamily {m : ℕ} (N : ℕ) (eta : ℝ)
    (l r : Fin m → Fin 2 → ℝ) : ℝ :=
  nativeEnhancedBoxTest N eta (fun _ => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) -
    ∑ j : Fin m, nativeEnhancedBoxTest N eta (l j) (r j)

private theorem full_box_domain (eta : ℝ) :
    currentChenUpsilon6LogDomain eta ∩ box (fun _ => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) = currentChenUpsilon6LogDomain eta := by
  apply inter_eq_left.mpr
  intro x hx
  obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
  exact ⟨ha, hh.trans (by norm_num), (by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hv, hd⟩

/-- Complete retained original enhanced harmonic limit for every fixed
finite disjoint half-open mask-box family, at each fixed corrected buffer.
The actual adopted step, its knot values, native prime tuples and phi weights
are all retained. The only geometric premise is disjointness of the boxes. -/
theorem tendsto_nativeRetainedBoxFamily {m : ℕ} (eta : ℝ) (heta : 0 ≤ eta)
    (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j)))) :
    Tendsto (fun N => nativeRetainedBoxFamily N eta l r) atTop
      (𝓝 (retainedEstimatorIntegral (fun x => x ∈ boxMask l r) eta)) := by
  have hfull := tendsto_nativeEnhancedBoxTest eta heta
    (fun _ => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  rw [full_box_domain eta] at hfull
  have h := hfull.sub (tendsto_finite_box_sum eta heta l r)
  have hselected := selected_boxMask_integral_eq_sum eta heta l r hdis
  have hret := full_sub_selected_eq_retained (fun x => x ∈ boxMask l r)
    (measurableSet_boxMask l r) heta
  rw [hselected] at hret
  change fullIntegral eta - (∑ j : Fin m,
    ∫ x in currentChenUpsilon6LogDomain eta ∩ box (l j) (r j), adoptedKernel x) = _ at hret
  change Tendsto (fun N => nativeRetainedBoxFamily N eta l r) atTop
    (𝓝 (fullIntegral eta - (∑ j : Fin m,
      ∫ x in currentChenUpsilon6LogDomain eta ∩ box (l j) (r j), adoptedKernel x))) at h
  rw [hret] at h
  exact h

private theorem disjoint_box_indicators {m : ℕ} (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j))))
    (f : Point → ℝ) (x : Point) :
    (∑ j : Fin m, (box (l j) (r j)).indicator f x) = (boxMask l r).indicator f x := by
  by_cases hx : x ∈ boxMask l r
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    rw [indicator_of_mem hx]
    calc
      _ = (box (l j) (r j)).indicator f x :=
        Finset.sum_eq_single j
          (fun i _ hij => indicator_of_notMem
            (fun hi => Set.disjoint_left.mp (hdis hij) hi hj) _)
          (by simp)
      _ = f x := indicator_of_mem hj _
  · rw [indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro j _
    exact indicator_of_notMem (fun hj => hx (mem_iUnion.mpr ⟨j, hj⟩)) _

/-- Exact direct retained native pair sum. Disjoint mask boxes remove each
selected pair once, with its actual adopted scalar knot value and phi weight. -/
theorem nativeRetainedBoxFamily_eq_pair_sum {m N : ℕ} (hN : 2 ≤ N) (eta : ℝ)
    (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j)))) :
    nativeRetainedBoxFamily N eta l r =
      ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
        ({x : Point | x ∉ boxMask l r}).indicator
          (fun x => currentChenUpsilon6OrdinaryClippedTest x +
            adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x)
          (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ) := by
  let f := fun x : Point => currentChenUpsilon6OrdinaryClippedTest x +
    adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x
  unfold nativeRetainedBoxFamily
  simp_rw [nativeEnhancedBoxTest_eq_pair_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hcoords : currentChenUpsilon6LogCoordinates N t = actualPrimeTupleLog N ![t.1, t.2] := by
    funext i
    fin_cases i <;> rfl
  have hrect := ((mem_currentChenUpsilon6OrdinarySelector_log_iff hN eta t).mp ht).2.2.1
  rw [hcoords] at hrect
  obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hrect
  have hfull : actualPrimeTupleLog N ![t.1, t.2] ∈
      box (fun _ => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) :=
    ⟨ha, hh.trans (by norm_num), (by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hv, hd⟩
  rw [← Finset.sum_div, ← sub_div]
  congr 1
  change (box (fun _ => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))).indicator f
    (actualPrimeTupleLog N ![t.1, t.2]) -
      (∑ j : Fin m, (box (l j) (r j)).indicator f (actualPrimeTupleLog N ![t.1, t.2])) =
        ({x : Point | x ∉ boxMask l r}).indicator f (actualPrimeTupleLog N ![t.1, t.2])
  rw [indicator_of_mem hfull, disjoint_box_indicators l r hdis f]
  by_cases hx : actualPrimeTupleLog N ![t.1, t.2] ∈ boxMask l r
  · rw [indicator_of_mem hx, indicator_of_notMem (show actualPrimeTupleLog N ![t.1, t.2] ∉
      {x : Point | x ∉ boxMask l r} from not_not.mpr hx)]
    ring
  · rw [indicator_of_notMem hx, indicator_of_mem hx]
    ring

/-- Consumer-facing retained native prime-pair harmonic theorem, with the
actual stepped adopted h248 lookup and one finite disjoint original boxmask. -/
theorem tendsto_retained_pair_sum {m : ℕ} (eta : ℝ) (heta : 0 ≤ eta)
    (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j)))) :
    Tendsto (fun N => ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
      ({x : Point | x ∉ boxMask l r}).indicator
        (fun x => currentChenUpsilon6OrdinaryClippedTest x +
          adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x)
        (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (retainedEstimatorIntegral (fun x => x ∈ boxMask l r) eta)) := by
  apply (tendsto_nativeRetainedBoxFamily eta heta l r hdis).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact nativeRetainedBoxFamily_eq_pair_sum hN eta l r hdis

end

end ImbalancedChen.P5U6AdoptedEnhancedHarmonicSourceOnly
