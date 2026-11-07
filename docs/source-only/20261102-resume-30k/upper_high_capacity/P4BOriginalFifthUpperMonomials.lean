import ImbalancedChen.P4BUpperSelectedBoxCapacity
import ImbalancedChen.OriginalFifthEndpointSelectedCriticalWindow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual nonseed ORIGINAL upper fifth winner, at every retained rank
at least five. Both square families are derived from that retained leaf
and its original raw positional winner. The analytic cover is fixed on
the native atom; the physical policy5 cap and sign-sensitive attachment
are unchanged. No lower ALL16 or outer-U5 rank is used.
-/
namespace ImbalancedChen.P4BOriginalFifthUpperMonomials
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles P1OriginalFifthAttainedRowBinding
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthRawWinnerArithmeticSupport20261026b
open OriginalFifthRetainedSelectedTailSupport20261026b
open OriginalFifthSelectedNaturalEndpoints20261026b
open OriginalFifthLiteralAffineSignBank20261026b OriginalFifthNativeAtomChoices20261026b
open OriginalFifthDualAnalyticCovers20261026b OriginalFifthCanonicalEndpointSupport20261026b
open OriginalFifthEndpointSelectedCriticalWindow20261026b
open OriginalSelectedEndpointQuotientInflation20261026b
open P4BUpperSelectedBoxCapacity

private theorem complementary_filters {α : Type*} (P : α → Prop) (l : List α) :
    (l.filter (fun i => decide (P i)) ++ l.filter (fun i => decide (¬P i))).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : P a
      · simpa [ha] using ih.cons a
      · simp only [List.filter_cons, ha, decide_false, not_false_eq_true,
          decide_true, Bool.false_eq_true, if_false, if_true]
        exact (List.perm_append_comm).trans
          (((List.perm_append_comm).trans ih).cons a)

/-- The exact fifth mask is removed in chronological order. Repeated
endpoint values do not merge their original occurrences. -/
theorem selected_remainder_permutation (I : Finset (Fin 5)) (p : Fin 5 → ℕ)
    (tail : List ℕ) :
    (selectedPrimes I p ++ (remainingPrimes I p ++ tail)).Perm (List.ofFn p ++ tail) := by
  have h := ((complementary_filters (fun q : Fin 5 => q ∈ I) [0,1,2,3,4]).map p).append_right tail
  simpa [selectedPrimes, remainingPrimes, remainingSlots, List.map_append,
    List.ofFn_succ, List.append_assoc] using h

/-- The lost middle line is explicitly recovered, including a moving
residue allowance. A numerical window alone is not used as a licence. -/
theorem buffered_endpoint_critical {x cover e kappa B : ℝ}
    (hx : 1 < x) (he : 0 < e) (hcover : cover ≤ 153/256-e)
    (hk : kappa ≤ e/64)
    (hlo : x^(2*cover+2*e-1) ≤ B)
    (hhi : B ≤ x^((2/3)*(57/64-cover)-e/6)) :
    x^(2*(cover+e/32)-1) ≤ B ∧
      B ≤ x^actualSelectedSubproductUpper (1+3*kappa) (cover+e/32) := by
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)).trans hlo,
    hhi.trans (Real.rpow_le_rpow_of_exponent_le hx.le ?_)⟩
  unfold actualSelectedSubproductUpper
  apply le_min <;> linarith

/-- The original source supplies the full and selected endpoint squares,
then the constructed whole-box algorithm supplies all three monomials.
`upper` has only primitive coordinate containment/inflation hypotheses;
the existing canonical mesh supplies these uniformly before N and leaves.
The selected capacity is NOT assumed to be at least one. -/
theorem actual_nonseed_fifth_whole_box_monomials
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 < e)
    (hefine : (e : ℝ) ≤ 1/384) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J : Finset (Fin 5 → Fin (m+1))) (j : Fin 5 → Fin (m+1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (sig : SignWord R4 R5)
    (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (k : Fin R5.length) (hnonseed : (atomChoice R4 R5 e m j L sig hsig).2 = k.succ)
    (corner : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ)/30)
    (rho : ℝ) (hrho : 0 < rho) (tau : ℝ) (htau : 0 ≤ tau)
    (hwidth : tau*((actualRoughVectorRankBound rho : ℝ)+1) ≤ (e : ℝ)/2)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (hrough : (N : ℝ)^rho ≤ w)
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length)
    (hatom : actualPrimeTupleLog N (fifthTuple leaf.selected) ∈ signAtom R4 R5 e m j sig)
    (hm : actualPrimeTupleLog N (fifthTuple leaf.selected) ∈ logPrimeMeshCell 0 (19/96) m j)
    (hc : ∀ i, |actualPrimeTupleLog N (fifthTuple leaf.selected) i-corner i| ≤ delta)
    (upper : ℕ → ℕ) (hlower : ∀ p ∈ leaf.selected.reverse, p ≤ upper p)
    (hinflate : ∀ p ∈ leaf.selected.reverse, (upper p : ℝ) ≤ (N : ℝ)^tau*(p : ℝ))
    (kappa A : ℝ) (hk : kappa ≤ (e : ℝ)/64) (hA : 1 ≤ A)
    (hAu : A ≤ (N : ℝ)^(1/3-(e : ℝ)/128)) :
    let p := fifthTuple leaf.selected
    let I := (rawRowAt R5 m j k).selected
    let cover := (dualCovers R4 R5 e m j (atomChoice R4 R5 e m j L sig hsig) corner delta).2
    let S := selectedPrimes I p
    let T := remainingPrimes I p ++ retainedTail leaf
    let abc := endpoints ((N : ℝ)^cover) A upper S T leaf.selected.reverse
    actualDwellSupport ((N : ℝ)^cover) (leaf.selected.reverse.map upper) ∧
    actualDwellSupport ((N : ℝ)^cover/endpoint upper S) (T.map upper) ∧
    abc.1 ≤ A ∧ A^2*abc.2.1*abc.2.2^2 ≤ (N : ℝ)^(1-3*((e : ℝ)/64)) ∧
    (N : ℝ)^(7*(1+3*kappa)/32)*A*abc.1*abc.2.1^5*abc.2.2^2 ≤
      (N : ℝ)^(2-4*((e : ℝ)/64)) ∧
    (A*abc.2.2/abc.2.1)^(7/16 : ℝ)*A*abc.1*abc.2.1^5*abc.2.2^2 ≤
      (N : ℝ)^(2-39*((e : ℝ)/64)/8) := by
  dsimp only
  let p := fifthTuple leaf.selected
  let t := actualPrimeTupleLog N p
  let I := (rawRowAt R5 m j k).selected
  let P := atomChoice R4 R5 e m j L sig hsig
  let cover := (dualCovers R4 R5 e m j P corner delta).2
  let lam := physicalExponent e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m) leaf
  let S := selectedPrimes I p
  let T := remainingPrimes I p ++ retainedTail leaf
  let R := actualRoughVectorRankBound rho
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have heupper : 2*(e : ℝ) < (299/500 : ℝ) := by linarith
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using firstExitRetainedLeaves_selected_reverse_sublist
      (policy5 e chi m omega (N : ℝ) (fourthFamily R4) L J (fifthFamily R5 m))
      weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hfront : List.ofFn p <+ leaf.selected.reverse := by
    rw [fifthTuple_chronological_prefix leaf hlen]
    exact List.take_sublist 5 leaf.selected.reverse
  have hpmem (i : Fin 5) : p i ∈ leaf.selected.reverse :=
    hfront.subset (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hp (i : Fin 5) : Nat.Prime (p i) := mem_roughPrimeUniverse_prime (hsub.subset (hpmem i))
  have hpart : (S++T).Perm leaf.selected.reverse := by
    have h := selected_remainder_permutation I p (retainedTail leaf)
    rw [chronological_prefix_tail_split leaf hlen] at h
    exact h
  have hSTmem : ∀ q ∈ S++T, q ∈ leaf.selected.reverse := fun _ h => hpart.mem_iff.mp h
  have hrank : leaf.selected.length ≤ R := actual_fifth_rank_bound e he.le chi m omega
    (fourthFamily R4) L J (fifthFamily R5 m) rho hrho N cap hNr w z hrough heupper weight leaf hleaf hlen
  have hSTrank : S.length+T.length ≤ R := by
    have hh := hpart.length_eq
    simp only [List.length_append,List.length_reverse] at hh
    omega
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by rw [rosserAncestor_length]; omega
  have hh : P1CorrectedFifthCausalTupleDictionary.tupleHistory p = rosserAncestor 5 leaf.selected :=
    P1CorrectedFifthCausalTupleDictionary.tupleHistory_primeHistoryTuple _ h5
  have hlam : lam = actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t := by
    unfold lam physicalExponent
    rw [← hh]
    exact exponent5_on_selected_owner e chi m omega (fourthFamily R4) L J (fifthFamily R5 m)
      N hN p (fun i => (hp i).pos) j hj hm
  have hC := (actual_atom_dualCovers R4 R5 e chi m omega J j hj L sig hsig
    corner t delta hd hsmall hatom hm hc).2
  have hbudget : lam+tau*((R : ℝ)+1) ≤ cover := by rw [hlam]; linarith [hC.1]
  have hlabel := atomChoice_spec R4 R5 e m j L sig hsig hatom
  have hparent := congrArg Prod.fst hlabel
  have hwin := congrArg Prod.snd hlabel
  change parentOwner R4 e m j L t = P.1 at hparent
  change fifthOwner R4 R5 e m j (parentOwner R4 e m j L t) t = P.2 at hwin
  rw [hparent,hnonseed] at hwin
  have hquot0 := nonseed_retained_grouped_quotient_support R4 R5 e chi m omega J j hj L
    N cap w z heupper hN weight leaf hleaf hlen hm P.1 hparent k hwin
  have hquot : actualDwellSupport ((N : ℝ)^lam/(S.prod : ℝ)) T := by
    simpa only [S,T,selectedPrimes_product,lam,physicalExponent,level5] using hquot0.1
  have hupperquot := selected_endpoint_quotient_support hNr htau S T upper
    (fun q hq => (mem_roughPrimeUniverse_prime (hsub.subset
      (hSTmem q (List.mem_append_left _ hq)))).pos)
    (fun q hq => hlower q (hSTmem q (List.mem_append_left _ hq)))
    (fun q hq => hinflate q (hSTmem q hq)) hSTrank hquot hbudget
  have hfull0 := retained_native_support_at_actual_Q5 e chi m omega (fourthFamily R4) L J
    (fifthFamily R5 m) N cap w z heupper hNr weight leaf hleaf hlen
  have hfull : actualDwellSupport ((N : ℝ)^cover) (leaf.selected.reverse.map upper) := by
    apply actualDwellSupport_upper_inflation hNr htau id upper leaf.selected.reverse
      (by simpa only [List.length_reverse] using hrank) hinflate
    · simpa only [List.map_id,lam,physicalExponent,level5] using hfull0
    · exact hbudget
  have hselected : actualDwellSupport ((N : ℝ)^cover/endpoint upper S) (T.map upper) := by
    simpa only [endpoint_eq_cast] using hupperquot.2.2
  have hcost5 : tau*5 ≤ (e : ℝ)/2 := by
    have hR : (5 : ℝ) ≤ R := by exact_mod_cast hlen.trans hrank
    nlinarith [hwidth]
  have hcrit := actual_endpoint_selected_critical_window R4 R5 e he chi m omega J j hj L sig hsig k
    hnonseed corner delta hd hsmall N hN p hp hatom hm hc tau htau hcost5 upper
    (fun q _ => hlower _ (hpmem q)) (fun q _ => hinflate _ (hpmem q))
  have hSend : endpoint upper S =
      (selectedFactor I (fun q => upper (p q)) : ℝ) := by
    rw [endpoint_eq_cast]
    have hmap : S.map upper = selectedPrimes I (fun q => upper (p q)) := by
      simp only [S,selectedPrimes,remainingPrimes,List.map_map,Function.comp_def]
    rw [hmap,selectedPrimes_product]
  have hcap := actual_caps_from_atomChoice R4 R5 e chi m omega J j hj L sig hsig hatom hm
  rw [hnonseed] at hcap
  have hlamHigh : lam ≤ 153/256-2*(e : ℝ) := by
    rw [hlam,hcap.2,candidate,envelope_eq_v]
    exact sub_le_sub_right (VariableEnvelope.v_le_cap _) _
  have hcover : cover ≤ 153/256-(e : ℝ) := by rw [hlam] at hlamHigh; linarith [hC.2]
  have hwindow := buffered_endpoint_critical hNr heR hcover hk hcrit.2.2.1 hcrit.2.2.2.1
  rw [← hSend] at hwindow
  let theta : ℝ := cover+(e : ℝ)/32
  have hlevel : theta-2*((e : ℝ)/64) = cover := by dsimp [theta]; ring
  have hmns := monomials hNr (by positivity : 0<(e : ℝ)/64)
    (by linarith : (e : ℝ)/64 ≤ 1/12)
    (by dsimp [theta]; linarith [hcrit.1] : 1/2 ≤ theta)
    (by dsimp [theta]; linarith : theta ≤ 5/8)
    upper S T leaf.selected.reverse hpart
    (fun q hq => (mem_roughPrimeUniverse_prime (hsub.subset hq)).pos.trans_le (hlower q hq))
    hA (by convert hAu using 1 <;> ring)
    (by simpa only [hlevel] using hfull) (by simpa only [hlevel] using hselected)
    hwindow.1 hwindow.2
  exact ⟨hfull,hselected,by simpa only [hlevel] using hmns⟩

end
end ImbalancedChen.P4BOriginalFifthUpperMonomials
