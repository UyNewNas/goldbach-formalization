import ImbalancedChen.OriginalSelectedEndpointQuotientInflation
import ImbalancedChen.OriginalFifthDualAnalyticCovers
import ImbalancedChen.OriginalFifthCanonicalEndpointSupport

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The actual nonseed RAW fifth winner supplies its bit-selected ORIGINAL
slots, chronological complement and retained tail at the same physical Q5.
One canonical natural endpoint mesh is fixed before N. Both the selected
product B_UPPER and all complementary/tail squares are inflated, using the
complete original rank budget. The quotient support is then at the fixed
NEW atom analytic cover divided by B_UPPER, not by the original B.

The atom's winner is constructed from primitive signs. Original B<=B_UPPER,
positive B_UPPER, positive quotient level and exact endpoint product
factorization are conclusions. No capacity>=1, allocation, old-carrier
support, C<1 sector, monomial estimate or external license is asserted.
-/

namespace ImbalancedChen.OriginalFifthSelectedNaturalEndpoints20261026b

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthRawWinnerArithmeticSupport20261026b
open OriginalFifthRetainedSelectedTailSupport20261026b
open OriginalFifthLiteralAffineSignBank20261026b
open OriginalFifthNativeAtomChoices20261026b
open OriginalFifthDualAnalyticCovers20261026b
open OriginalFifthCanonicalEndpointSupport20261026b
open OriginalFourthCanonicalIntegerEndpoints20261026b
open OriginalSelectedEndpointQuotientInflation20261026b

/-- The SAME five original positions are selected, in chronological order. -/
def selectedPrimes (I : Finset (Fin 5)) (p : Fin 5 → ℕ) : List ℕ := remainingPrimes Iᶜ p

theorem selectedPrimes_product (I : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    (selectedPrimes I p).prod = selectedFactor I p := by
  rw [selectedPrimes, remainingPrimes_product]
  have hs : Finset.univ.filter (fun q : Fin 5 => q ∉ Iᶜ) = I := by ext q; simp
  simp only [remainingFactor, selectedFactor, hs]

theorem selected_complement_total_length (I : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    (selectedPrimes I p).length + (remainingPrimes I p).length = 5 := by
  by_cases h0 : (0 : Fin 5) ∈ I <;> by_cases h1 : (1 : Fin 5) ∈ I <;>
    by_cases h2 : (2 : Fin 5) ∈ I <;> by_cases h3 : (3 : Fin 5) ∈ I <;>
    by_cases h4 : (4 : Fin 5) ∈ I
  all_goals simp [selectedPrimes, remainingPrimes, remainingSlots, h0, h1, h2, h3, h4]

private theorem selected_upper_product (I : Finset (Fin 5)) (p : Fin 5 → ℕ) (upper : ℕ → ℕ) :
    ((selectedPrimes I p).map upper).prod = selectedFactor I (fun q => upper (p q)) := by
  have hs : (selectedPrimes I p).map upper = selectedPrimes I (fun q => upper (p q)) := by
    simp only [selectedPrimes, remainingPrimes, List.map_map, Function.comp_def]
  rw [hs, selectedPrimes_product]

theorem endpoint_selected_times_remainder_product (I : Finset (Fin 5))
    (leaf : FirstExitLeaf ℕ) (hlen : 5 ≤ leaf.selected.length) (upper : ℕ → ℕ) :
    selectedFactor I (fun q => upper (fifthTuple leaf.selected q)) *
      ((remainingPrimes I (fifthTuple leaf.selected) ++ retainedTail leaf).map upper).prod =
      (leaf.selected.reverse.map upper).prod := by
  have hr : (remainingPrimes I (fifthTuple leaf.selected)).map upper =
      remainingPrimes I (fun q => upper (fifthTuple leaf.selected q)) := by
    simp only [remainingPrimes, List.map_map, Function.comp_def]
  rw [List.map_append, List.prod_append, ← mul_assoc, hr, remainingPrimes_product,
    selected_mul_remaining]
  have hsplit := congrArg (fun ps : List ℕ => (ps.map upper).prod)
    (chronological_prefix_tail_split leaf hlen)
  simpa only [List.map_append, List.prod_append, List.map_ofFn, List.prod_ofFn, Function.comp_def] using hsplit

/-- No upper-endpoint support is assumed. The actual native nonseed atom
and retained leaf supply the original gates and all chronological squares.
The original OLD carrier remains a separate object. -/
theorem exists_actual_selected_endpoint_quotient
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 < e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (sig : SignWord R4 R5) (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (k : Fin R5.length) (hnonseed : (atomChoice R4 R5 e m j L sig hsig).2 = k.succ)
    (corner : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (rho : ℝ) (hrho : 0 < rho) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) :
    let P := atomChoice R4 R5 e m j L sig hsig
    let cover := (dualCovers R4 R5 e m j P corner delta).2
    let I := (rawRowAt R5 m j k).selected
    ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ,
      tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ (e : ℝ) / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ),
          leaf ∈ firstExitRetainedLeaves
            (policy5 e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m))
            weight [] true 1 (roughPrimeUniverse N cap w z) →
          5 ≤ leaf.selected.length →
          let p := fifthTuple leaf.selected
          let t := actualPrimeTupleLog N p
          let Bupper := selectedFactor I (fun q => integerUpper n N (p q))
          t ∈ signAtom R4 R5 e m j sig → t ∈ logPrimeMeshCell 0 (19 / 96) m j →
          (∀ i, |t i - corner i| ≤ delta) →
          selectedFactor I p ≤ Bupper ∧ 0 < Bupper ∧
          0 < (N : ℝ) ^ cover / (Bupper : ℝ) ∧
          actualDwellSupport ((N : ℝ) ^ cover / (Bupper : ℝ))
            ((remainingPrimes I p ++ retainedTail leaf).map (integerUpper n N)) ∧
          Bupper * ((remainingPrimes I p ++ retainedTail leaf).map (integerUpper n N)).prod =
            (leaf.selected.reverse.map (integerUpper n N)).prod := by
  dsimp only
  let P := atomChoice R4 R5 e m j L sig hsig
  let cover := (dualCovers R4 R5 e m j P corner delta).2
  let I := (rawRowAt R5 m j k).selected
  let R := actualRoughVectorRankBound rho
  let tau : ℝ := (e : ℝ) / (4 * ((R : ℝ) + 1))
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hRpos : 0 < (R : ℝ) + 1 := by positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hwidth : tau * ((R : ℝ) + 1) ≤ (e : ℝ) / 2 := by
    have hEq : tau * ((R : ℝ) + 1) = (e : ℝ) / 4 := by
      dsimp [tau]
      field_simp [hRpos.ne']
      <;> ring
    rw [hEq]
    linarith
  obtain ⟨n, _hmesh, hcanonical⟩ := exists_uniform_canonical_endpoints tau htau
  refine ⟨tau, htau, n, hwidth, ?_⟩
  filter_upwards [hcanonical, eventually_ge_atTop (2 : ℕ)] with N hendpoint hN
  intro cap w z hrough hz weight leaf hleaf hlen
  dsimp only
  intro hatom hm hc
  let p := fifthTuple leaf.selected
  let t := actualPrimeTupleLog N p
  let S := selectedPrimes I p
  let T := remainingPrimes I p ++ retainedTail leaf
  let U := integerUpper n N
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using firstExitRetainedLeaves_selected_reverse_sublist
      (policy5 e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m))
      weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hfront : List.ofFn p <+ leaf.selected.reverse := by
    rw [fifthTuple_chronological_prefix leaf hlen]
    exact List.take_sublist 5 leaf.selected.reverse
  have hpMem (q : Fin 5) : p q ∈ leaf.selected.reverse :=
    hfront.subset (List.mem_ofFn.mpr ⟨q, rfl⟩)
  have hp : ∀ q, Nat.Prime (p q) := fun q => mem_roughPrimeUniverse_prime (hsub.subset (hpMem q))
  have hSTmem : ∀ a ∈ S ++ T, a ∈ leaf.selected.reverse := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp ha
      exact hpMem q
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp ha
        exact hpMem q
      · exact List.mem_of_mem_drop ha
  have hep (a : ℕ) (ha : a ∈ S ++ T) : a ≤ U a ∧ (U a : ℝ) ≤ (N : ℝ) ^ tau * (a : ℝ) := by
    have hm := hsub.subset (hSTmem a ha)
    exact hendpoint a (mem_roughPrimeUniverse_prime hm).pos ((mem_roughPrimeUniverse_upper hm).trans_le hz)
  have hlabel := atomChoice_spec R4 R5 e m j L sig hsig hatom
  have hparent := congrArg Prod.fst hlabel
  have hwinner := congrArg Prod.snd hlabel
  change parentOwner R4 e m j L t = P.1 at hparent
  change fifthOwner R4 R5 e m j (parentOwner R4 e m j L t) t = P.2 at hwinner
  rw [hparent, hnonseed] at hwinner
  have hactual0 := nonseed_retained_grouped_quotient_support R4 R5 e chi m omega J j hj L
    N cap w z heupper hNnat weight leaf hleaf hlen hm P.1 hparent k hwinner
  dsimp only at hactual0
  have hactual : actualDwellSupport
      ((N : ℝ) ^ physicalExponent e chi m omega (N : ℝ) (fourthFamily R4) L J
        (fifthFamily R5 m) leaf / (S.prod : ℝ)) T := by
    simpa only [S, T, selectedPrimes_product, physicalExponent, level5] using hactual0.1
  have hrank0 := actual_fifth_rank_bound e he.le chi m omega (fourthFamily R4) L J
    (fifthFamily R5 m) rho hrho N cap hNr w z hrough heupper weight leaf hleaf hlen
  have hlenST : S.length + T.length = leaf.selected.length := by
    have hfive := selected_complement_total_length I p
    dsimp only [S, T]
    simp only [List.length_append, retainedTail, List.length_drop, List.length_reverse]
    omega
  have hrank : S.length + T.length ≤ R := by
    rw [hlenST]
    exact hrank0
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by rw [rosserAncestor_length]; omega
  have hh : P1CorrectedFifthCausalTupleDictionary.tupleHistory p = rosserAncestor 5 leaf.selected :=
    P1CorrectedFifthCausalTupleDictionary.tupleHistory_primeHistoryTuple _ h5
  have hphysical : physicalExponent e chi m omega (N : ℝ) (fourthFamily R4) L J
      (fifthFamily R5 m) leaf = actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t := by
    unfold physicalExponent
    rw [← hh]
    exact exponent5_on_selected_owner e chi m omega (fourthFamily R4) L J (fifthFamily R5 m)
      N hNnat p (fun q => (hp q).pos) j hj hm
  have hC := actual_atom_dualCovers R4 R5 e chi m omega J j hj L sig hsig
    corner t delta hd hsmall hatom hm hc
  have hbudget : physicalExponent e chi m omega (N : ℝ) (fourthFamily R4) L J
      (fifthFamily R5 m) leaf + tau * ((R : ℝ) + 1) ≤ cover := by
    rw [hphysical]
    linarith [hC.2.1]
  have hquot := selected_endpoint_quotient_support hNr htau.le S T U
    (fun a ha => (mem_roughPrimeUniverse_prime
      (hsub.subset (hSTmem a (List.mem_append_left _ ha)))).pos)
    (fun a ha => (hep a (List.mem_append_left _ ha)).1)
    (fun a ha => (hep a ha).2) hrank hactual hbudget
  have hSprod : S.prod = selectedFactor I p := selectedPrimes_product I p
  have hUprod : (S.map U).prod = selectedFactor I (fun q => U (p q)) := selected_upper_product I p U
  rw [hSprod, hUprod] at hquot
  refine ⟨hquot.1, hquot.2.1, ?_, hquot.2.2, ?_⟩
  · have hBu : (0 : ℝ) < selectedFactor I (fun q => U (p q)) := by exact_mod_cast hquot.2.1
    exact div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _) hBu
  · exact endpoint_selected_times_remainder_product I leaf hlen U

end
end ImbalancedChen.OriginalFifthSelectedNaturalEndpoints20261026b
