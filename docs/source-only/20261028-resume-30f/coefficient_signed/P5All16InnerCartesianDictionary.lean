import ImbalancedChen.P5All16ActualInnerWallReconstruction
import ImbalancedChen.P5ActualInnerMeshSeparatedGamma

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual retained canonical inner words are identified with COMPLETE original
fine Cartesian prime boxes.  Every tuple of an inner box is strictly
ordered, hence is its retained product's canonical word; product fibres
are injective.  Conversely every canonical inner point occurs in its own
whole box.  No source equality, chart cover or coefficient conclusion is
supplied as a premise.

The full finite inner-box union is disjoint across ranks and mesh cells.
The resulting exact ordinary retained inner source has the independently
defined presievedCoefficient, same small e, full marked-prefix test and
original strict physical level.  A local rank bound is explicit; at the
actual all16 caller it is derived from the existing physical support.
Marked-prefix common-colour absorption and its final restoring scalar L1
budget remain separate from this dictionary.
-/

namespace ImbalancedChen.P5Z.All16InnerCartesianDictionary
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open OriginalOrdinaryCommonBetaModel OriginalPresievedRoughPrimeSlots
open JointPresievedSlotAffineRealization PresievedRoughGateMeshReserve
open All16FineMeshGateScalar All16ActualInnerWallReconstruction
open ActualInnerMeshSeparatedGamma

/-- Every tuple in an inner box is literally the canonical retained
prime word of its product, not merely a permutation of some source word. -/
theorem inner_box_tuple_eq_canonical {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    {ps : List ℕ} (hps : ps ∈ meshPrimeBox N cap w Z m j) :
    ps.prod ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z ∧
      ps = canonicalSlots N cap w Z ps.prod := by
  have hd := inner_list_actual_retained hN w Z ell hL hj ps hps
  have hsort := (inner_list_original_gates hN w Z ell hj ps hps).1
  have hprime : ∀ p ∈ ps, Nat.Prime p :=
    actualPrimeSlotBox_prime (meshPrimeAlphabet N cap w Z m) (List.ofFn j)
      (fun i hi p hp => (mem_roughPrimeFinset.mp (mesh_prime_rough hp)).2.1) ps hps
  have hcprime : ∀ p ∈ canonicalSlots N cap w Z ps.prod, Nat.Prime p :=
    fun p hp => (canonicalSlots_prime_data hp).1
  have hperm := (Nat.primeFactorsList_unique ((canonicalSlots_prod hd).symm) hprime).trans
    (Nat.primeFactorsList_unique
      (rfl : (canonicalSlots N cap w Z ps.prod).prod = (canonicalSlots N cap w Z ps.prod).prod)
      hcprime).symm
  refine ⟨hd, ?_⟩
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hba hab)
    (hsort.imp (fun _ _ h => h.le))
    ((canonicalSlots_descending N cap w Z ps.prod).imp (fun _ _ h => h.le)) hperm

/-- Full inner-box product fibres have exactly ONE tuple, even when the
prime alphabet was defined before any target tuple was inspected. -/
theorem inner_box_product_injective {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m) :
    Set.InjOn List.prod (meshPrimeBox N cap w Z m j : Set (List ℕ)) := by
  intro ps hps qs hqs hprod
  rw [(inner_box_tuple_eq_canonical hN w Z ell hL hj hps).2,
    (inner_box_tuple_eq_canonical hN w Z ell hL hj hqs).2, hprod]

/-- The rank of every actual product of a whole inner box is its
physical prime-factor rank. -/
theorem inner_box_product_rank {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    {ps : List ℕ} (hps : ps ∈ meshPrimeBox N cap w Z m j) :
    ps.prod.primeFactors.card = r := by
  have hc := inner_box_tuple_eq_canonical hN w Z ell hL hj hps
  have hlen : ps.length = r := by
    simpa only [List.length_ofFn] using
      actualPrimeSlotBox_length (meshPrimeAlphabet N cap w Z m) (List.ofFn j) ps hps
  have hcLen := congrArg List.length hc.2
  rw [canonicalSlots_length hc.1] at hcLen
  exact hcLen.symm.trans hlen

/-- The lower corner of an inner mesh cell is itself a valid point,
so its strict order forces the fine labels to be injective. -/
theorem inner_mesh_labels_injective {r m : ℕ} (ell : ℝ)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m) : Function.Injective j := by
  have hlo : logPrimeMeshLo 0 1 m j ∈ cell 0 1 m j := by
    apply mem_logPrimeMeshCell.mpr
    intro i
    exact ⟨le_rfl, (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m j i).2.1⟩
  have hanti := ((roughRegion_dictionary ell _).mp ((Finset.mem_filter.mp hj).2 _ hlo)).2
  intro i k hik
  apply hanti.injective
  simp only [logPrimeMeshLo, hik]

private theorem nodup_word_factorial_one {ι : Type*} [DecidableEq ι] :
    ∀ input : List ι, input.Nodup →
      (∏ i ∈ input.toFinset, (input.count i).factorial) = 1 := by
  intro input
  induction input with
  | nil => simp
  | cons a input ih =>
      intro hnd
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
      have hnot : a ∉ input.toFinset := by simpa using ha
      rw [List.toFinset_cons, Finset.prod_insert hnot]
      have hc : (a :: input).count a = 1 := by simp [ha]
      rw [hc]
      simp only [Nat.factorial_one, one_mul]
      calc
        _ = ∏ i ∈ input.toFinset, (input.count i).factorial := by
          apply Finset.prod_congr rfl
          intro i hi
          have hne : i ≠ a := by
            intro h
            exact ha (h ▸ List.mem_toFinset.mp hi)
          simp [hne, Ne.symm hne]
        _ = 1 := ih ht

/-- This strict-order inner subdivision has no repeated fine label.
Its literal M_res is one, derived before source normalization is used. -/
theorem inner_mesh_multiplicity_one {r m : ℕ} (ell : ℝ)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m) : meshMultiplicity j = 1 := by
  exact nodup_word_factorial_one (List.ofFn j)
    (List.nodup_ofFn.mpr (inner_mesh_labels_injective ell hj))

/-- The full union of actual inner Cartesian prime boxes at ranks <=R. -/
def innerTupleUnion (R N cap m : ℕ) (w Z ell : ℝ) : Finset (List ℕ) :=
  (Finset.range (R + 1)).biUnion (fun r =>
    (innerCells r 0 1 ell m).biUnion (fun j => meshPrimeBox N cap w Z m j))

def retainedInner (N cap m : ℕ) (w Z ell : ℝ) (d : ℕ) : Prop :=
  let ps := canonicalSlots N cap w Z d
  ∃ j ∈ innerCells ps.length 0 1 ell m,
    actualPrimeTupleLog N (slotVector ps) ∈ cell 0 1 m j

/-- Actual canonical source membership is equivalent to membership in
complete inner Cartesian boxes, with the explicit original rank bound. -/
theorem canonical_mem_inner_union_iff {R N cap m d : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hd : d ∈ fixedRoughSupport
      (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z)
    (hrank : d.primeFactors.card ≤ R) :
    canonicalSlots N cap w Z d ∈ innerTupleUnion R N cap m w Z ell ↔
      retainedInner N cap m w Z ell d := by
  constructor
  · intro hu
    obtain ⟨r, hr, hwithin⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨j, hj, hbox⟩ := Finset.mem_biUnion.mp hwithin
    have hlen : (canonicalSlots N cap w Z d).length = r := by
      simpa only [List.length_ofFn] using actualPrimeSlotBox_length
        (meshPrimeAlphabet N cap w Z m) (List.ofFn j) _ hbox
    subst r
    refine ⟨j, hj, ?_⟩
    apply ((mesh_box_dictionary hN w Z j _).mp ?_).2
    simpa only [ofFn_slotVector] using hbox
  · rintro ⟨j, hj, hv⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(canonicalSlots N cap w Z d).length, ?_, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
    · rw [canonicalSlots_length hd]
      exact Finset.mem_range.mpr (by omega)
    · have hrough : ∀ i, slotVector (canonicalSlots N cap w Z d) i ∈ roughPrimeFinset N cap w Z := by
        intro i
        rw [← roughPrimeUniverse_toFinset N cap w Z]
        exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.getElem_mem i.isLt)).1)
      have hbox := (mesh_box_dictionary hN w Z j _).mpr ⟨hrough, hv⟩
      simpa only [ofFn_slotVector] using hbox

/-- All tuples in the union are genuine retained canonical words. -/
theorem inner_union_tuple_canonical {R N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {ps : List ℕ} (hps : ps ∈ innerTupleUnion R N cap m w Z ell) :
    ps.prod ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z ∧
      ps = canonicalSlots N cap w Z ps.prod ∧ ps.prod.primeFactors.card ≤ R := by
  obtain ⟨r, hr, hwithin⟩ := Finset.mem_biUnion.mp hps
  obtain ⟨j, hj, hbox⟩ := Finset.mem_biUnion.mp hwithin
  have hc := inner_box_tuple_eq_canonical hN w Z ell hL hj hbox
  refine ⟨hc.1, hc.2, ?_⟩
  rw [inner_box_product_rank hN w Z ell hL hj hbox]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)

/-- Exact independent-source inner-divisor/complete-Cartesian-union
bijection, before separated convolutions or an arithmetic estimate. -/
theorem retained_inner_sum_eq_complete_union {R N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    (hrank : ∀ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
      d.primeFactors.card ≤ R) (H : ℕ → ℝ) :
    (∑ d ∈ (fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z).filter
      (retainedInner N cap m w Z ell), H d) =
      ∑ ps ∈ innerTupleUnion R N cap m w Z ell, H ps.prod := by
  apply Finset.sum_bij (fun d hd => canonicalSlots N cap w Z d)
  · intro d hd
    have hret := (Finset.mem_filter.mp hd).1
    exact (canonical_mem_inner_union_iff hN w Z ell hret (hrank d hret)).mpr
      (Finset.mem_filter.mp hd).2
  · intro d hd e he hcan
    have hdret := (Finset.mem_filter.mp hd).1
    have heret := (Finset.mem_filter.mp he).1
    have hp := congrArg List.prod hcan
    simpa only [canonicalSlots_prod hdret, canonicalSlots_prod heret] using hp
  · intro ps hps
    have hc := inner_union_tuple_canonical hN w Z ell hL hps
    refine ⟨ps.prod, Finset.mem_filter.mpr ⟨hc.1, ?_⟩, hc.2.1.symm⟩
    apply (canonical_mem_inner_union_iff hN w Z ell hc.1 hc.2.2).mp
    rw [← hc.2.1]
    exact hps
  · intro d hd
    rw [canonicalSlots_prod (Finset.mem_filter.mp hd).1]

/-- Different half-open mesh cells give disjoint actual list boxes. -/
theorem mesh_list_boxes_disjoint {r N cap m : ℕ} (hN : 1 < N)
    (w Z : ℝ) {j k : Grid r m} (hne : j ≠ k) :
    Disjoint (meshPrimeBox N cap w Z m j) (meshPrimeBox N cap w Z m k) := by
  apply Finset.disjoint_left.mpr
  intro ps hpj hpk
  have hlen : ps.length = r := by
    simpa only [List.length_ofFn] using actualPrimeSlotBox_length
      (meshPrimeAlphabet N cap w Z m) (List.ofFn j) ps hpj
  subst r
  have hj := ((mesh_box_dictionary hN w Z j (slotVector ps)).mp
    (by simpa only [ofFn_slotVector] using hpj)).2
  have hk := ((mesh_box_dictionary hN w Z k (slotVector ps)).mp
    (by simpa only [ofFn_slotVector] using hpk)).2
  exact hne (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 1) hj hk)

/-- Exact double sum over the complete inner Cartesian atoms. -/
theorem inner_union_sum (R N cap m : ℕ) (hN : 1 < N) (w Z ell : ℝ)
    (H : List ℕ → ℝ) :
    (∑ ps ∈ innerTupleUnion R N cap m w Z ell, H ps) =
      ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
        ∑ ps ∈ meshPrimeBox N cap w Z m j, H ps := by
  have hinner (r : ℕ) : Set.PairwiseDisjoint (innerCells r 0 1 ell m : Set (Grid r m))
      (fun j => meshPrimeBox N cap w Z m j) := by
    intro j hj k hk hne
    exact mesh_list_boxes_disjoint hN w Z hne
  have hranks : Set.PairwiseDisjoint (Finset.range (R + 1) : Set ℕ)
      (fun r => (innerCells r 0 1 ell m).biUnion (fun j => meshPrimeBox N cap w Z m j)) := by
    intro r hr q hq hne
    apply Finset.disjoint_left.mpr
    intro ps hpr hpq
    obtain ⟨j, hj, hboxr⟩ := Finset.mem_biUnion.mp hpr
    obtain ⟨k, hk, hboxq⟩ := Finset.mem_biUnion.mp hpq
    have hlr : ps.length = r := by
      simpa only [List.length_ofFn] using actualPrimeSlotBox_length
        (meshPrimeAlphabet N cap w Z m) (List.ofFn j) ps hboxr
    have hlq : ps.length = q := by
      simpa only [List.length_ofFn] using actualPrimeSlotBox_length
        (meshPrimeAlphabet N cap w Z m) (List.ofFn k) ps hboxq
    exact hne (hlr.symm.trans hlq)
  rw [innerTupleUnion, Finset.sum_biUnion hranks]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_biUnion (hinner r)

/-- The independent ACTUAL retained coefficient source on canonical
inner points is exactly the complete fine Cartesian source, with its
literal M_res shown explicitly and proved one on these strict cells. -/
theorem actual_retained_inner_source_eq_cartesian {R N cap m e : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    (hrank : ∀ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
      d.primeFactors.card ≤ R) (prefix : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z,
      if retainedInner N cap m w Z ell d then
        presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * d) * F (prefix * (e * d)) else 0) =
      ∑ r ∈ Finset.range (R + 1), ∑ j ∈ innerCells r 0 1 ell m,
        (1 / (meshMultiplicity j : ℝ)) *
          ∑ ps ∈ meshPrimeBox N cap w Z m j,
            presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
              F (prefix * (e * ps.prod)) := by
  rw [← Finset.sum_filter,
    retained_inner_sum_eq_complete_union hN w Z ell hL hrank,
    inner_union_sum R N cap m hN w Z ell]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_mesh_multiplicity_one ell hj]
  norm_num

end
end ImbalancedChen.P5Z.All16InnerCartesianDictionary
