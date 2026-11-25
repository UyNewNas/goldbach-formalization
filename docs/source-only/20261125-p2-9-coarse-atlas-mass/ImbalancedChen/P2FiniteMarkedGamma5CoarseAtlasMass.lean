import ImbalancedChen.P2FiniteMarkedGamma5PrimeCube
import ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar

namespace ImbalancedChen.P2FiniteMarkedGamma5CoarseAtlasMass
noncomputable section
open Filter Finset Real LiLiuPrereqBuchstab
open Part5OriginalCausalSmoothAtlas (Plan Code atom atom_total atom_nonneg)
open Part5OriginalH430JointQueryEnclosure (Cube readout)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5AtlasEulerBudget
open P2FiniteMarkedGamma5IntegerSupport (finPhysicalProfile_nonzero_support)
open P2FiniteMarkedGamma5EulerWordBudget (finPhysicalProfile finToPhysical)
open P2FiniteMarkedGamma5PhysicalExtension (physicalProfile_bounds)
open P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent shell endpoint eventually_cut_le_half_floor)
open P2FiniteMarkedGamma5RadialTupleCount
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth radialWidth_pos exp_radialWidth_lt_two)
open scoped Classical Topology BigOperators

private abbrev normalizer := P2FiniteMarkedGamma5RadialRoughMass.norm

def mass (N k r : ℕ) (P : Plan) (accept : (Fin k → Code P) → Prop) (logQ h : ℝ) : ℝ :=
  ∑ u ∈ Part3.labelledPrimeTuples (k+(2+r)) (2*N),
    atlasProfile P accept logQ (N:ℝ) (radialWidth h) ((N:ℝ)^frozenLeafCutoffFloor)
      (fun j => ((u j).val : ℝ))

theorem weight_le_one_on_support {N k r : ℕ} {h : ℝ} (hN : 2 ≤ N)
    (hp : 0 < h) (h8 : h ≤ 1/8) (hc : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2)
    (P : Plan) (A : (Fin k → Code P) → Prop)
    (u : Fin (k+(2+r)) → Fin (2*N+1))
    (hu : u ∈ Part3.labelledPrimeTuples (k+(2+r)) (2*N)) (logQ : ℝ)
    (hw : atlasProfile P A logQ (N:ℝ) (radialWidth h) ((N:ℝ)^frozenLeafCutoffFloor)
      (fun j => ((u j).val : ℝ)) ≠ 0) :
    u ∈ bandTuples N (k+(2+r)) 0 2 ∧
      atlasProfile P A logQ (N:ℝ) (radialWidth h) ((N:ℝ)^frozenLeafCutoffFloor)
        (fun j => ((u j).val : ℝ)) ≤ 1 := by
  have h0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hb := rpow_pos_of_pos h0 frozenLeafCutoffFloor
  have hprime := (mem_filter.mp hu).2
  have H := atlasProfile_nonzero_original P A logQ (N:ℝ) (radialWidth h)
    ((N:ℝ)^frozenLeafCutoffFloor) (fun j => ((u j).val : ℝ)) hw
  obtain ⟨hf,hM⟩ := finPhysicalProfile_nonzero_support hb h0 (radialWidth_pos hp) H
  have hcap : (Part3.labelledProduct u : ℝ) < 2 * (N:ℝ) := by
    simpa only [Part3.labelledProduct,Nat.cast_prod] using
      hM.trans (mul_lt_mul_of_pos_right (exp_radialWidth_lt_two hp h8) h0)
  have hu0 : 0 < Part3.labelledProduct u := prod_pos (fun j _ => (hprime j).pos)
  refine ⟨mem_filter.mpr ⟨hu,fun j => hc.trans (hf j).le,?_,hcap.le⟩,?_⟩
  · simpa only [zero_mul] using (Nat.cast_pos.mpr hu0 : (0:ℝ) < Part3.labelledProduct u)
  · have hm : (∏ j, (u j).val) ≤ 2*N := by exact_mod_cast hcap.le
    have cube := P2FiniteMarkedGamma5PrimeCube.old_log_cube hN
      (fun j => (u j).val) hprime hm
    let z := oldLogCoordinates (k:=k) (r:=r) (N:ℝ) (fun j => ((u j).val : ℝ))
    have hr : readout P A z ≤ 1 := by
      rw [← atom_total P cube]
      apply sum_le_sum
      intro j _
      by_cases hh : A j <;> simp [hh,atom_nonneg]
    rw [atlasProfile_eq_original_weight P A logQ (N:ℝ) (radialWidth h) hb]
    have bds := physicalProfile_bounds logQ (N:ℝ) (radialWidth h)
      ((N:ℝ)^frozenLeafCutoffFloor) (finToPhysical k r (fun j => ((u j).val : ℝ)))
    exact (mul_le_mul_of_nonneg_left hr bds.1).trans (by simpa only [mul_one] using bds.2)

private theorem mass_le_card {N k r : ℕ} (hN : 2 ≤ N)
    {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1/8)
    (hc : cut N ≤ (N:ℝ)^frozenLeafCutoffFloor/2)
    (P : Plan) (A : (Fin k → Code P) → Prop) (logQ : ℝ) :
    mass N k r P A logQ h ≤ ((bandTuples N (k+(2+r)) 0 2).card : ℝ) := by
  let S := Part3.labelledPrimeTuples (k+(2+r)) (2*N)
  let T := bandTuples N (k+(2+r)) 0 2
  calc
    _ ≤ ∑ u ∈ S, if u ∈ T then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro u hu
      by_cases hz : atlasProfile P A logQ (N:ℝ) (radialWidth h) ((N:ℝ)^frozenLeafCutoffFloor)
          (fun j => ((u j).val : ℝ)) = 0
      · rw [hz]; split_ifs <;> norm_num
      · obtain ⟨ht,H⟩ := weight_le_one_on_support hN hp h8 hc P A u hu logQ hz
        simpa only [if_pos (show u ∈ T from ht)] using H
    _ = _ := by
      rw [← sum_filter]
      have eqT : S.filter (fun u => u ∈ T) = T := by
        ext u
        exact mem_filter.trans ⟨And.right,fun ht => ⟨(mem_filter.mp ht).1,ht⟩⟩
      rw [eqT]
      simp [T]

/-- One bound and one N threshold for all allowed labelled ranks, plans,
intercepts, readout predicates and radial widths. -/
theorem uniform_mass_bound :
    ∃ J : ℝ, 0 < J ∧ ∀ᶠ N : ℕ in atTop, ∀ (k r : ℕ),
      k+2+r ≤ frozenSourceRankBound → ∀ (P : Plan) (A : (Fin k → Code P) → Prop)
      (logQ h : ℝ), 0 < h → h ≤ 1/8 → normalizer N * mass N k r P A logQ h ≤ J := by
  let L := cutExponent⁻¹ * 2 * buchstab cutExponent⁻¹
  have hM : 0 ≤ multiplicity := by unfold multiplicity; positivity
  refine ⟨multiplicity * (|L|+1) + 1,by positivity,?_⟩
  have ht := (endpoint (c:=2) (by norm_num)).eventually
    (gt_mem_nhds (show L < |L|+1 by linarith [le_abs_self L]))
  filter_upwards [ht,eventually_cut_le_half_floor,eventually_ge_atTop (2:ℕ)] with N hrough hc hN
  intro k r hkr P A logQ h hp h8
  have hn : 0 ≤ normalizer N := div_nonneg
    (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) (Nat.cast_nonneg _)
  have hs : (shell N 0 2).card ≤ roughCount (2*(N:ℝ)) (cut N) :=
    card_le_card (show shell N 0 2 ⊆ roughNumbers (2*(N:ℝ)) (cut N) from
      fun _ hm => (mem_sdiff.mp hm).1)
  calc
    _ ≤ normalizer N * (multiplicity * (roughCount (2*(N:ℝ)) (cut N) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hn
      exact (mass_le_card hN hp h8 hc P A logQ).trans
        ((rank_card_le_boundaryCount N _ 0 2 (by omega)).trans
        ((all_ranks_bound N 0 2).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hM)))
    _ = multiplicity * (normalizer N * (roughCount (2*(N:ℝ)) (cut N) : ℝ)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hrough.le hM).trans (le_add_of_nonneg_right zero_le_one)

/-- A fixed finite sum of original nonnegative marks is charged once.
Its coarse price stays valid for all moving choices in the entry data. -/
theorem finite_marked_bound {ι : Type*} (I : Finset ι) (m : ι → ℝ)
    (hm : ∀ i ∈ I, 0 ≤ m i) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ (k r : ι → ℕ),
      (∀ i ∈ I, k i+2+r i ≤ frozenSourceRankBound) →
      ∀ (P : ι → Plan) (A : (i : ι) → (Fin (k i) → Code (P i)) → Prop)
        (logQ h : ι → ℝ), (∀ i ∈ I, 0 < h i ∧ h i ≤ 1/8) →
        normalizer N * (∑ i ∈ I, m i * mass N (k i) (r i) (P i) (A i) (logQ i) (h i)) ≤ C := by
  obtain ⟨J,hJ,H⟩ := uniform_mass_bound
  have hsum := sum_nonneg hm
  refine ⟨(∑ i ∈ I,m i)*J+1,by positivity,?_⟩
  filter_upwards [H] with N hN
  intro k r hk P A logQ h hh
  rw [mul_sum]
  calc
    _ = ∑ i ∈ I, m i * (normalizer N * mass N (k i) (r i) (P i) (A i) (logQ i) (h i)) :=
      sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ i ∈ I,m i*J := sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hN _ _ (hk i hi) (P i) (A i) _ _ (hh i hi).1 (hh i hi).2)
        (hm i hi))
    _ ≤ _ := by rw [← sum_mul]; linarith

end
end ImbalancedChen.P2FiniteMarkedGamma5CoarseAtlasMass
