import ImbalancedChen.P5OriginalWCanonicalMeshEndpoint
import ImbalancedChen.P5OriginalWWholeBoxRealRun
import ImbalancedChen.P5OriginalJointPresievedWFactors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The physical W owner rectangle has a single padded upper prefix corner.
It preserves both required order comparisons and dominates all four
actual prefix primes. The canonical rough slots are mapped to literal
occurrences, with exact product and no tuplewise regrouping.
-/
namespace ImbalancedChen.P5Z.OriginalWOwnerOccurrenceBinding
noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler
open OriginalNearCapRealEndpointGeometry
open OriginalPresievedRoughPrimeSlots JointPresievedSlotAffineRealization
open OriginalJointPresievedWFactors OriginalJointCommonBetaModel
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalWCanonicalMeshEndpoint OriginalWWholeBoxRealRun
open SelectedRealEndpointSupport

def paddedOwnerCorner (B : Box) (eta : ℚ) : LogFour :=
  fun i => (B.hi i : ℝ) + endpointPadding wPolicy B eta

/-- The actual selected W owner, with the actual source tuple inside its
half-open cell, gives one fixed padded corner for the whole owner box. -/
theorem active_W_owner_padded_corner {n N : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) {E : ℕ × ℕ → Prop}
    {t : Four} (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy) :
    let B := ownerBox n N t
    let u := paddedOwnerCorner B eta
    B.Valid ∧ 0 < B.lo 3 ∧ wholeBoxEligibleTest wPolicy B = true ∧
    (∀ i, (B.lo i : ℝ) ≤ u i) ∧
    (∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta) ∧
    0 ≤ u 2 ∧ u 1 ≤ u 0 ∧ u 3 ≤ u 2 ∧
    (∀ i : Fin 4, (slots t i : ℝ) ≤ (N : ℝ) ^ (u i)) := by
  let B := ownerBox n N t
  let u := paddedOwnerCorner B eta
  have hs := (Finset.mem_filter.mp ht).1
  have htag := (Finset.mem_filter.mp ht).2
  have hcell := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs)
  have hbox := cell_subset_closed_box n _ hcell
  have hvalid : B.Valid := gridBox_valid n _
  have hpositive : 0 < B.lo 3 := gridBox_lower_positive n _ 3
  have hcert := (boxPolicy_certificate B htag).2
  change wholeBoxEligibleTest (selectedPolicy n N t) B = true at hcert
  rw [hW] at hcert
  have hpad := (endpointPadding_positive wPolicy B eta hvalid hpositive hcert heta).1
  have hanti : StrictAnti (coordinates N t) := coordinates_strictAnti hN hs
  have hhiAnti : Antitone (fun i : Fin 4 => (B.hi i : ℝ)) := by
    change Antitone (fun i : Fin 4 =>
      ((gridBox n (owner n (coordinates N t))).hi i : ℝ))
    simpa only [cast_grid_hi] using mesh_upper_antitone
      (by norm_num [lower, upper] : (lower : ℝ) < (upper : ℝ)) hcell hanti
  have huAnti : Antitone u := by
    intro i j hij
    exact add_le_add_right (hhiAnti hij) _
  have hlo : ∀ i, (B.lo i : ℝ) ≤ u i := by
    intro i
    have hv : (B.lo i : ℝ) ≤ (B.hi i : ℝ) := by exact_mod_cast hvalid i
    exact hv.trans (le_add_of_nonneg_right hpad.le)
  have hsize : ∀ i : Fin 4, (slots t i : ℝ) ≤ (N : ℝ) ^ (u i) := by
    intro i
    have hp := actualPrimeTupleLog_rpow hN (slots t) (slots_pos hs) i
    have hn : (1 : ℝ) < N := by exact_mod_cast hN
    have hcoord : coordinates N t i ≤ u i := by
      change coordinates N t i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta
      exact (hbox.2 i).trans (le_add_of_nonneg_right hpad.le)
    rw [←hp]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hcoord
  refine ⟨hvalid,hpositive,hcert,hlo,fun i => le_rfl,?_,?_,?_,hsize⟩
  · have h : (0 : ℝ) < (B.lo 2 : ℝ) := by
      exact_mod_cast gridBox_lower_positive n (owner n (coordinates N t)) 2
    linarith [hlo 2]
  · exact huAnti (by norm_num : (0 : Fin 4) ≤ 1)
  · exact huAnti (by norm_num : (2 : Fin 4) ≤ 3)

/-- The literal physical occurrence map is independent of the W run and
its first-overflow branch. The residual slots retain their canonical order. -/
def physicalOccurrence (t : Four) (ps : List ℕ) : Occ ps.length → ℕ :=
  Sum.elim (slots t) (slotVector ps)

theorem physicalOccurrence_pos {N : ℕ} {E : ℕ × ℕ → Prop}
    {t : Four} (ht : t ∈ jointSelector N E) {ps : List ℕ}
    (hps : ∀ p ∈ ps, Nat.Prime p) :
    ∀ i, 0 < physicalOccurrence t ps i := by
  intro i
  rcases i with i | i
  · exact slots_pos ht i
  · exact (hps _ (List.getElem_mem i.isLt)).pos

/-- This is the exact W full-modulus product to which phase2's generic
same-trace transport is applied; no completedBins are imported. -/
theorem physicalOccurrence_whole_product (t : Four) (ps : List ℕ) :
    ((wholeLabels ps.length).map (physicalOccurrence t ps)).prod =
      fullPrefix t * ps.prod := by
  have hf : (front.map (slots t)).prod = fullPrefix t := by
    simp [front, fullPrefix, Fin.prod_univ_succ]
  have hr : ((List.finRange ps.length).map (slotVector ps)).prod = ps.prod := by
    change (List.ofFn (slotVector ps)).prod = ps.prod
    rw [ofFn_slotVector]
  calc
    _ = (front.map (slots t)).prod *
        ((List.finRange ps.length).map (slotVector ps)).prod := by
          simp [wholeLabels, physicalOccurrence, List.map_map, Function.comp_def]
    _ = fullPrefix t * ps.prod := by rw [hf, hr]

/-- Simultaneous prefix and rough upper size bounds for one fixed owner
and one fixed rough fine cell. This is the exact input type of the W run. -/
theorem physicalOccurrence_size {N m : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (B : Box) (eta : ℚ)
    (hbox : coordinates N t ∈ B.region)
    (hpad : 0 ≤ endpointPadding wPolicy B eta)
    (ps : List ℕ) (rho zeta : ℝ)
    (j : PresievedRoughGateMeshReserve.Grid ps.length m)
    (hrough : actualPrimeTupleLog N (slotVector ps) ∈ cell rho zeta m
      j)
    (hps : ∀ i : Fin ps.length, 0 < slotVector ps i) :
    ∀ i : Occ ps.length,
      (physicalOccurrence t ps i : ℝ) ≤
        wWeight N (paddedOwnerCorner B eta)
          (logPrimeMeshHi rho zeta m j) i := by
  intro i
  rcases i with i | i
  · have hn : (1 : ℝ) < N := by exact_mod_cast hN
    have hp := actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) i
    change (slots t i : ℝ) ≤ (N : ℝ) ^
      ((B.hi i : ℝ) + endpointPadding wPolicy B eta)
    rw [←hp]
    exact Real.rpow_le_rpow_of_exponent_le hn.le
      ((hbox.2 i).trans (le_add_of_nonneg_right hpad))
  · simpa [wWeight, exponent, physicalOccurrence] using
      prime_le_mesh_upper hN (slotVector ps) hps hrough i

/-- The actual nonzero ALL16 W mark has the literal same occurrence
product as its physical modulus. This uses only the e,d and canonical
rough-slot parts of the active factor theorem; its later natural
`completedBins` fields are deliberately never used. -/
theorem active_W_mark_occurrence_product {n N r : ℕ} {eta : ℚ}
    {nu0 epsilon : ℝ} (hN : 1 < N) (heta : 0 < eta)
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    (E : ℕ × ℕ → Prop) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy)
    (hr : r ∈ rowSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) t)
    (hq : ImbalancedChen.P5Z.OriginalJointPresievedCompiler.jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0) :
    ∃ e d : ℕ,
      e ∈ actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2)) ∧
      d ∈ fixedRoughSupport
        (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) ∧
      let ps := canonicalSlots N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d
      (∀ i, 0 < physicalOccurrence t ps i) ∧
      e * ((wholeLabels ps.length).map (physicalOccurrence t ps)).prod =
        fullPrefix t * r := by
  obtain ⟨e,he,d,hd,her,_,_,_,hprod,_⟩ :=
    active_joint_W_mark_factors hN heta hnu0 heps heBudget E ht hW hr hq
  let ps := canonicalSlots N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    ((N : ℝ) ^ (nu0 * epsilon ^ 2))
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d
  have hs := (Finset.mem_filter.mp ht).1
  have hp : ∀ p ∈ ps, Nat.Prime p := fun p hmem =>
    (canonicalSlots_prime_data hmem).1
  refine ⟨e,d,he,hd,?_,?_⟩
  · exact physicalOccurrence_pos hs hp
  · rw [physicalOccurrence_whole_product,hprod,her]
    ring

end
end ImbalancedChen.P5Z.OriginalWOwnerOccurrenceBinding
