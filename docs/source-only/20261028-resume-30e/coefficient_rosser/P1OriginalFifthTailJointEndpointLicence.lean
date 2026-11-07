import ImbalancedChen.P1ActualOriginalAndCommonFifthGuard
import ImbalancedChen.OriginalFifthSelectedNaturalEndpoints

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One canonical endpoint mesh, fixed BEFORE N, simultaneously pays every
full chronological square and every actual nonseed winner's selected /
complement-plus-entire-tail square at the same original Q5 auxiliary cover.
The selected endpoint product is divided out at the SAME endpoints.

Both original and checked coefficients are kept as independent actual
sources. The native old/new cap pair is not the original/checked pair.
Seed branches receive full support; selected quotient support is attached
only to an actual nonseed raw winner. No remainder is set to zero and no
factorization/distribution licence or upper comparison parent is assumed.
-/

namespace ImbalancedChen.P1OriginalFifthTailJointEndpointLicence

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1OriginalFifthAttainedRowBinding
open P1ActualVariableFifthProfiles
open P1Pair12ActualWireSourceSupport
open P1Pair12RetainedSignedSource
open P1OriginalSupportedRemainderJointCover
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
open OriginalFifthSelectedNaturalEndpoints20261026b

/-- A genuine geometric sector of the actual fifth source. Its complement
is retained explicitly in the signed identity below. -/
def nativeSector (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (sig : SignWord R4 R5)
    (corner : Fin 5 → ℝ) (delta : ℝ) (N : ℕ) (leaf : FirstExitLeaf ℕ) : Prop :=
  5 ≤ leaf.selected.length ∧
    let t := actualPrimeTupleLog N (fifthTuple leaf.selected)
    t ∈ signAtom R4 R5 e m j sig ∧ t ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
      ∀ i, |t i - corner i| ≤ delta

/-- Simultaneous full and selected endpoint support at ONE cover and ONE
natural endpoint map. The two cap brackets retain their actual old/new
parents. The nonseed mask is the constructed raw positional winner. -/
def FifthTailEndpointLicence
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1)) (licensedOriginal : ProducerRow → Prop)
    (sig : SignWord R4 R5) (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (corner : Fin 5 → ℝ) (delta : ℝ) (n N : ℕ) (leaf : FirstExitLeaf ℕ) : Prop :=
  let p := fifthTuple leaf.selected
  let t := actualPrimeTupleLog N p
  let P := atomChoice R4 R5 e m j licensedOriginal sig hsig
  let C := dualCovers R4 R5 e m j P corner delta
  let lambda := physicalExponent e chi m omega (N : ℝ) (fourthFamily R4)
    licensedOriginal J (fifthFamily R5 m) leaf
  (∀ a ∈ leaf.selected.reverse, a ≤ integerUpper n N a) ∧
    (originalVariableFourthProfile e chi omega m j (fourthFamily R4) licensedOriginal t +
      (e : ℝ) / 2 ≤ C.1 ∧ C.1 ≤
        originalVariableFourthProfile e chi omega m j (fourthFamily R4) licensedOriginal t + e) ∧
    (lambda + (e : ℝ) / 2 ≤ C.2 ∧ C.2 ≤ lambda + e) ∧
    actualDwellSupport ((N : ℝ) ^ C.2) (leaf.selected.reverse.map (integerUpper n N)) ∧
    ∀ k : Fin R5.length, P.2 = k.succ →
      let I := (rawRowAt R5 m j k).selected
      let Bupper := selectedFactor I (fun q => integerUpper n N (p q))
      selectedFactor I p ≤ Bupper ∧ 0 < Bupper ∧
        0 < (N : ℝ) ^ C.2 / (Bupper : ℝ) ∧
        actualDwellSupport ((N : ℝ) ^ C.2 / (Bupper : ℝ))
          ((remainingPrimes I p ++ retainedTail leaf).map (integerUpper n N)) ∧
        Bupper * ((remainingPrimes I p ++ retainedTail leaf).map (integerUpper n N)).prod =
          (leaf.selected.reverse.map (integerUpper n N)).prod

/-- The source conditions identify actual leaf membership and an occupied
primitive atom. Endpoint support, rank and the winner are conclusions. -/
def ActualSectorLicenceAt
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1)) (licensedOriginal : ProducerRow → Prop)
    (sig : SignWord R4 R5) (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (corner : Fin 5 → ℝ) (delta rho : ℝ) (n N : ℕ) : Prop :=
  ∀ (cap : ℕ) (w z : ℝ), (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
    ∀ (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ),
      leaf ∈ firstExitRetainedLeaves
        (policy5 e chi m omega (N : ℝ) (fourthFamily R4) licensedOriginal J (fifthFamily R5 m))
        weight [] true 1 (roughPrimeUniverse N cap w z) →
      nativeSector R4 R5 e m j sig corner delta N leaf →
      FifthTailEndpointLicence R4 R5 e chi m omega J j licensedOriginal sig hsig corner delta n N leaf

/-- Choose ONE natural mesh before N. Full support and actual nonseed
selected-complement/tail support are proved on that very same mesh; two
existential endpoint suppliers are not silently identified. -/
theorem exists_actual_fifth_tail_source_licence
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 < e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (licensedOriginal : ProducerRow → Prop)
    (sig : SignWord R4 R5) (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (corner : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (rho : ℝ) (hrho : 0 < rho) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ,
      tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ (e : ℝ) / 2 ∧
      ∀ᶠ N : ℕ in atTop,
        ActualSectorLicenceAt R4 R5 e chi m omega J j licensedOriginal sig hsig
          corner delta rho n N := by
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
  intro cap w z hrough hz weight leaf hleaf hsector
  rcases hsector with ⟨hlen, hatom, hm, hc⟩
  let p := fifthTuple leaf.selected
  let t := actualPrimeTupleLog N p
  let P := atomChoice R4 R5 e m j licensedOriginal sig hsig
  let C := dualCovers R4 R5 e m j P corner delta
  let lambda := physicalExponent e chi m omega (N : ℝ) (fourthFamily R4)
    licensedOriginal J (fifthFamily R5 m) leaf
  let U := integerUpper n N
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using firstExitRetainedLeaves_selected_reverse_sublist
      (policy5 e chi m omega (N : ℝ) (fourthFamily R4) licensedOriginal J (fifthFamily R5 m))
      weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hfront : List.ofFn p <+ leaf.selected.reverse := by
    rw [fifthTuple_chronological_prefix leaf hlen]
    exact List.take_sublist 5 leaf.selected.reverse
  have hpMem (q : Fin 5) : p q ∈ leaf.selected.reverse :=
    hfront.subset (List.mem_ofFn.mpr ⟨q, rfl⟩)
  have hp : ∀ q, Nat.Prime (p q) := fun q => mem_roughPrimeUniverse_prime (hsub.subset (hpMem q))
  have hep (a : ℕ) (ha : a ∈ leaf.selected.reverse) :
      a ≤ U a ∧ (U a : ℝ) ≤ (N : ℝ) ^ tau * (a : ℝ) := by
    have hmem := hsub.subset ha
    exact hendpoint a (mem_roughPrimeUniverse_prime hmem).pos
      ((mem_roughPrimeUniverse_upper hmem).trans_le hz)
  have hrank := actual_fifth_rank_bound e he.le chi m omega (fourthFamily R4)
    licensedOriginal J (fifthFamily R5 m) rho hrho N cap hNr w z hrough heupper weight leaf hleaf hlen
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by rw [rosserAncestor_length]; omega
  have hh : P1CorrectedFifthCausalTupleDictionary.tupleHistory p = rosserAncestor 5 leaf.selected :=
    P1CorrectedFifthCausalTupleDictionary.tupleHistory_primeHistoryTuple _ h5
  have hphysical : lambda = actualNext5 e chi m omega j (fourthFamily R4)
      licensedOriginal (fifthFamily R5 m) t := by
    unfold lambda physicalExponent
    rw [← hh]
    exact exponent5_on_selected_owner e chi m omega (fourthFamily R4) licensedOriginal J
      (fifthFamily R5 m) N hNnat p (fun q => (hp q).pos) j hj hm
  have hC := actual_atom_dualCovers R4 R5 e chi m omega J j hj licensedOriginal sig hsig
    corner t delta hd hsmall hatom hm hc
  have hnew : lambda + (e : ℝ) / 2 ≤ C.2 ∧ C.2 ≤ lambda + e := by
    rw [hphysical]
    exact hC.2
  have hbudget : lambda + tau * ((R : ℝ) + 1) ≤ C.2 := by linarith [hnew.1]
  have hactual : actualDwellSupport ((N : ℝ) ^ lambda) leaf.selected.reverse :=
    retained_native_support_at_actual_Q5 e chi m omega (fourthFamily R4) licensedOriginal J
      (fifthFamily R5 m) N cap w z heupper hNr weight leaf hleaf hlen
  have hfull : actualDwellSupport ((N : ℝ) ^ C.2) (leaf.selected.reverse.map U) := by
    apply actualDwellSupport_upper_inflation hNr htau.le id U leaf.selected.reverse
      (by simpa only [List.length_reverse] using hrank)
      (fun a ha => (hep a ha).2)
    · simpa using hactual
    · exact hbudget
  change FifthTailEndpointLicence R4 R5 e chi m omega J j licensedOriginal sig hsig
    corner delta n N leaf
  dsimp only [FifthTailEndpointLicence]
  refine ⟨fun a ha => (hep a ha).1, hC.1, hnew, hfull, ?_⟩
  intro k hnonseed
  let I := (rawRowAt R5 m j k).selected
  let S := selectedPrimes I p
  let T := remainingPrimes I p ++ retainedTail leaf
  have hSTmem : ∀ a ∈ S ++ T, a ∈ leaf.selected.reverse := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp ha
      exact hpMem q
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp ha
        exact hpMem q
      · exact List.mem_of_mem_drop ha
  have hlabel := atomChoice_spec R4 R5 e m j licensedOriginal sig hsig hatom
  have hparent := congrArg Prod.fst hlabel
  have hwinner := congrArg Prod.snd hlabel
  change parentOwner R4 e m j licensedOriginal t = P.1 at hparent
  change fifthOwner R4 R5 e m j (parentOwner R4 e m j licensedOriginal t) t = P.2 at hwinner
  rw [hparent, hnonseed] at hwinner
  have hquot0 := nonseed_retained_grouped_quotient_support R4 R5 e chi m omega J j hj
    licensedOriginal N cap w z heupper hNnat weight leaf hleaf hlen hm P.1 hparent k hwinner
  dsimp only at hquot0
  have hquotActual : actualDwellSupport ((N : ℝ) ^ lambda / (S.prod : ℝ)) T := by
    simpa only [lambda, S, T, selectedPrimes_product, physicalExponent, level5] using hquot0.1
  have hlenST : S.length + T.length = leaf.selected.length := by
    have hfive := selected_complement_total_length I p
    dsimp only [S, T]
    simp only [List.length_append, retainedTail, List.length_drop, List.length_reverse]
    omega
  have hquot := selected_endpoint_quotient_support hNr htau.le S T U
    (fun a ha => (mem_roughPrimeUniverse_prime
      (hsub.subset (hSTmem a (List.mem_append_left _ ha)))).pos)
    (fun a ha => (hep a (hSTmem a (List.mem_append_left _ ha))).1)
    (fun a ha => (hep a (hSTmem a ha)).2)
    (by rw [hlenST]; exact hrank) hquotActual hbudget
  have hSprod : S.prod = selectedFactor I p := selectedPrimes_product I p
  have hUprod : (S.map U).prod = selectedFactor I (fun q => U (p q)) := by
    have hmap : (selectedPrimes I p).map U = selectedPrimes I (fun q => U (p q)) := by
      simp only [selectedPrimes, remainingPrimes, List.map_map, Function.comp_def]
    rw [hmap, selectedPrimes_product]
  rw [hSprod, hUprod] at hquot
  refine ⟨hquot.1, hquot.2.1, ?_, hquot.2.2, ?_⟩
  · have hBu : (0 : ℝ) < selectedFactor I (fun q => U (p q)) := by exact_mod_cast hquot.2.1
    exact div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _) hBu
  · exact endpoint_selected_times_remainder_product I leaf hlen U

/-- Original and existing checked-bank licences receive independent actual
leaf covers, at one eventual target threshold. Their own original parents
and their own atom winners are retained. This is not equality of policies. -/
theorem exists_actual_original_checked_fifth_tail_cover
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 < e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (licensedOriginal : ProducerRow → Prop)
    (sig : SignWord R4 R5) (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (corner : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (rho : ℝ) (hrho : 0 < rho) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) :
    ∃ no nc : ℕ, ∀ᶠ N : ℕ in atTop,
      ActualSectorLicenceAt R4 R5 e chi m omega J j licensedOriginal sig hsig
        corner delta rho no N ∧
      ActualSectorLicenceAt R4 R5 e chi m omega J j (fun r => sourceGeometryFlag r = true)
        sig hsig corner delta rho nc N := by
  obtain ⟨tauO, htO, no, hwO, hO⟩ := exists_actual_fifth_tail_source_licence R4 R5 e he
    chi m omega J j hj licensedOriginal sig hsig corner delta hd hsmall rho hrho heupper
  obtain ⟨tauC, htC, nc, hwC, hC⟩ := exists_actual_fifth_tail_source_licence R4 R5 e he
    chi m omega J j hj (fun r => sourceGeometryFlag r = true)
      sig hsig corner delta hd hsmall rho hrho heupper
  exact ⟨no, nc, hO.and hC⟩

/-- Literal signed leaf contribution, with the full marked arithmetic
test and the original sign-sensitive small-prime attachment unchanged. -/
def originalSectorSum
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (licensedOriginal : ProducerRow → Prop)
    (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (sig : SignWord R4 R5) (corner : Fin 5 → ℝ) (delta : ℝ)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (inside : Bool) : ℝ :=
  ((firstExitRetainedLeaves
    (policy5 e chi m omega (N : ℝ) (fourthFamily R4) licensedOriginal J (fifthFamily R5 m))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z)).map (fun leaf =>
      if decide (nativeSector R4 R5 e m j sig corner delta N leaf) = inside then
        leaf.value * attachedLeafTest N cap mark w L G leaf.positive leaf.selected
      else 0)).sum

private theorem actual_physical_eq_sector_add_complement
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (licensedOriginal : ProducerRow → Prop)
    (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (sig : SignWord R4 R5) (corner : Fin 5 → ℝ) (delta : ℝ)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli
      ((policy5 e chi m omega (N : ℝ) (fourthFamily R4) licensedOriginal J (fifthFamily R5 m)) false)
        N cap w z,
      actualSmallRoughRho
        ((policy5 e chi m omega (N : ℝ) (fourthFamily R4) licensedOriginal J (fifthFamily R5 m)) false)
        N cap w z L q * G (mark * q)) =
    originalSectorSum R4 R5 e chi m omega licensedOriginal J j sig corner delta N cap mark w z L G true +
    originalSectorSum R4 R5 e chi m omega licensedOriginal J j sig corner delta N cap mark w z L G false := by
  rw [physical_test_eq_signedTest _
    (P4AOriginalVariableFifthPhysicalLedger.fifth_even e chi m omega (fourthFamily R4)
      licensedOriginal J (fifthFamily R5 m) (N : ℝ)), signedTest_eq_leaves]
  unfold originalSectorSum
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro leaf _hleaf
  by_cases hs : nativeSector R4 R5 e m j sig corner delta N leaf <;> simp [hs]

/-- The complete D supported-frontier remainder equals two independent
actual native sectors PLUS their exact signed complements. The eventual
licences above apply to precisely the sector leaves in this equality.
No matching of old/checked leaves, vanishing complement, or estimate is
postulated. G may be the exact marked AP count minus its coprime mean. -/
theorem supported_remainder_eq_actual_sector_and_complement
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (licensedOriginal : ProducerRow → Prop)
    (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (sig : SignWord R4 R5) (corner : Fin 5 → ℝ) (delta : ℝ)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    ((supportedFrontier e chi m omega N cap w z).map
      (signedRemainder R4 e chi m omega licensedOriginal J (fifthFamily R5 m)
        N cap mark w z L G)).sum =
      (originalSectorSum R4 R5 e chi m omega licensedOriginal J j sig corner delta
          N cap mark w z L G true -
        originalSectorSum R4 R5 e chi m omega (fun r => sourceGeometryFlag r = true)
          J j sig corner delta N cap mark w z L G true) +
      (originalSectorSum R4 R5 e chi m omega licensedOriginal J j sig corner delta
          N cap mark w z L G false -
        originalSectorSum R4 R5 e chi m omega (fun r => sourceGeometryFlag r = true)
          J j sig corner delta N cap mark w z L G false) := by
  rw [← physicalDifference_eq_supported_source]
  unfold physicalDifference P1Pair12ActualWireSourceSupport.wirePolicy5
  dsimp only
  rw [actual_physical_eq_sector_add_complement R4 R5 e chi m omega licensedOriginal
      J j sig corner delta N cap mark w z L G,
    actual_physical_eq_sector_add_complement R4 R5 e chi m omega
      (fun r => sourceGeometryFlag r = true) J j sig corner delta N cap mark w z L G]
  ring

end
end ImbalancedChen.P1OriginalFifthTailJointEndpointLicence
