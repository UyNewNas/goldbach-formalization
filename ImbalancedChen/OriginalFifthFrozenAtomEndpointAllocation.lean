import ImbalancedChen.OriginalFifthDualAnalyticCovers
import ImbalancedChen.OriginalFifthCanonicalEndpointSupport
import ImbalancedChen.OriginalFifthOwnCubeSignRefinement

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The NEW original policy5 retained carrier receives a fixed analytic cover
on each occupied native primitive atom and small reference box. Full
canonical natural endpoint support is DERIVED from that carrier's true
Q5, covering every original prefix and retained tail slot. The endpoint
vector then computes one deterministic capacity assignment valid for its
entire coordinate box. No assignment or support oracle is supplied.

The physical policy and all frozen ancestor caps remain the original
ones. The two density caps and old/new own-cube flags stay pointwise; the
OLD carrier's support is deliberately not inferred from a restored NEW
leaf. Two-capacity bounds here require both capacities at least one; no
analytic three-monomial license or C<1 sector conclusion is asserted.
-/

namespace ImbalancedChen.OriginalFifthFrozenAtomEndpointAllocation20261026b

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthRetainedSelectedTailSupport20261026b
open OriginalFifthLiteralAffineSignBank20261026b
open OriginalFifthNativeAtomChoices20261026b
open OriginalFifthOwnCubeSignRefinement20261026b
open OriginalFifthDualAnalyticCovers20261026b
open OriginalFifthCanonicalEndpointSupport20261026b
open OriginalFourthCanonicalIntegerEndpoints20261026b

def endpointVector (n N : ℕ) (input : List ℕ) (i : Fin input.length) : ℕ :=
  integerUpper n N input[i.val]

private theorem endpointVector_ofFn (n N : ℕ) (input : List ℕ) :
    List.ofFn (endpointVector n N input) = input.map (integerUpper n N) := by
  have h : List.ofFn (fun i : Fin input.length => input[i.val]) = input := List.ofFn_getElem
  have hm := congrArg (List.map (integerUpper n N)) h
  simpa only [List.map_ofFn, Function.comp_def, endpointVector] using hm

/-- One mesh and one eventual threshold work before every arithmetic
target and leaf, while the analytic NEW cover is constant on this atom
and its reference box. The complete old/new data remain the native data. -/
theorem exists_native_atom_endpoint_allocation
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 < e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (wAtom : SignWord R4 R5) (vAtom : CubeWord R4 R5)
    (hAtom : (refinedAtom R4 R5 e m j wAtom vAtom).Nonempty)
    (corner : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (rho : ℝ) (hrho : 0 < rho) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ,
      tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ (e : ℝ) / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ),
          leaf ∈ firstExitRetainedLeaves
            (policy5 e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m))
            weight [] true 1 (roughPrimeUniverse N cap w z) →
          5 ≤ leaf.selected.length →
          ∀ hw : (signAtom R4 R5 e m j wAtom).Nonempty,
          let t := actualPrimeTupleLog N (fifthTuple leaf.selected)
          let P := atomChoice R4 R5 e m j L wAtom hw
          let C := dualCovers R4 R5 e m j P corner delta
          t ∈ refinedAtom R4 R5 e m j wAtom vAtom →
          t ∈ logPrimeMeshCell 0 (19 / 96) m j →
          (∀ i, |t i - corner i| ≤ delta) →
          dataAt R4 R5 e m j L t = frozenData R4 R5 e m j L wAtom vAtom hAtom ∧
          actualDwellSupport ((N : ℝ) ^ C.2)
            (List.ofFn (endpointVector n N leaf.selected.reverse)) ∧
          (∀ i : Fin leaf.selected.reverse.length,
            leaf.selected.reverse[i.val] ≤ endpointVector n N leaf.selected.reverse i) ∧
          (∀ A B : ℝ, 1 ≤ A → 1 ≤ B → A * B = (N : ℝ) ^ C.2 →
            ∀ a : Fin leaf.selected.reverse.length → ℕ,
              (∀ i, a i ≤ endpointVector n N leaf.selected.reverse i) →
              (actualFrozenCapacityFactors A (endpointVector n N leaf.selected.reverse) a
                  (List.finRange leaf.selected.reverse.length)).1 *
                (actualFrozenCapacityFactors A (endpointVector n N leaf.selected.reverse) a
                  (List.finRange leaf.selected.reverse.length)).2 = (List.ofFn a).prod ∧
              ((actualFrozenCapacityFactors A (endpointVector n N leaf.selected.reverse) a
                  (List.finRange leaf.selected.reverse.length)).1 : ℝ) ≤ A ∧
              ((actualFrozenCapacityFactors A (endpointVector n N leaf.selected.reverse) a
                  (List.finRange leaf.selected.reverse.length)).2 : ℝ) ≤ B) := by
  obtain ⟨tau, htau, n, hbudget, hrealize⟩ := exists_actual_fifth_endpoint_realization
    e he chi m omega (fourthFamily R4) L J (fifthFamily R5 m) rho hrho heupper
  refine ⟨tau, htau, n, hbudget, ?_⟩
  filter_upwards [hrealize, eventually_ge_atTop (2 : ℕ)] with N hNdata hN
  intro cap w z hrough hz weight leaf hleaf hlen hw
  dsimp only
  intro ht hm hc
  let t := actualPrimeTupleLog N (fifthTuple leaf.selected)
  let P := atomChoice R4 R5 e m j L wAtom hw
  let C := dualCovers R4 R5 e m j P corner delta
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hep := hNdata cap w z hrough hz weight leaf hleaf hlen
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using firstExitRetainedLeaves_selected_reverse_sublist
      (policy5 e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m))
      weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hfront : List.ofFn (fifthTuple leaf.selected) <+ leaf.selected.reverse := by
    rw [fifthTuple_chronological_prefix leaf hlen]
    exact List.take_sublist 5 leaf.selected.reverse
  have hp : ∀ i, 0 < fifthTuple leaf.selected i := by
    intro i
    exact (mem_roughPrimeUniverse_prime
      (hsub.subset (hfront.subset (List.mem_ofFn.mpr ⟨i, rfl⟩)))).pos
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length]
    omega
  have hh : P1CorrectedFifthCausalTupleDictionary.tupleHistory (fifthTuple leaf.selected) =
      rosserAncestor 5 leaf.selected :=
    P1CorrectedFifthCausalTupleDictionary.tupleHistory_primeHistoryTuple _ h5
  have hphysical : physicalExponent e chi m omega (N : ℝ) (fourthFamily R4) L J
      (fifthFamily R5 m) leaf = actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t := by
    unfold physicalExponent
    rw [← hh]
    exact exponent5_on_selected_owner e chi m omega (fourthFamily R4) L J (fifthFamily R5 m)
      N hNnat (fifthTuple leaf.selected) hp j hj hm
  have hC := actual_atom_dualCovers R4 R5 e chi m omega J j hj L wAtom hw
    corner t delta hd hsmall ht.1 hm hc
  have hCnew : physicalExponent e chi m omega (N : ℝ) (fourthFamily R4) L J
      (fifthFamily R5 m) leaf + (e : ℝ) / 2 ≤ C.2 := by
    rw [hphysical]
    exact hC.2.1
  have hfull : actualDwellSupport ((N : ℝ) ^ C.2)
      (List.ofFn (endpointVector n N leaf.selected.reverse)) := by
    rw [endpointVector_ofFn]
    intro i hi
    exact (hep.2.1 i hi).trans (Real.rpow_le_rpow_of_exponent_le hNr.le hCnew)
  refine ⟨frozenData_spec R4 R5 e m j L wAtom vAtom hAtom ht, hfull, ?_, ?_⟩
  · intro i
    exact hep.1 _ (List.getElem_mem i.isLt)
  · intro A B hA hB hAB a ha
    apply actualFrozenCapacityFactors_on_box hA hB (endpointVector n N leaf.selected.reverse)
      (hAB.symm ▸ hfull) a ha

end
end ImbalancedChen.OriginalFifthFrozenAtomEndpointAllocation20261026b
