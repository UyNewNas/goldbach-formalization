import ImbalancedChen.P4AOriginalR17PaidIntegral
import ImbalancedChen.P2Saving16FourteenCornerReciprocalResidual

/-!
SOURCE_ONLY / NOT COMPILED / UNEVALUATED.

One R17 rectangle-compiler choice supplies strict cap geometry, ordinary
occurrences and the complete signed distribution error for all fourteen
original saving16 cells. Independent chosen corners share that one Q and rho;
the common count, full integral upper bound and compiler reserve occur once.

This source requires the seven owner postimages of the finite-core package,
not their pre-extraction owners, and the 20261123 selected-api versions of
P4AOriginalR17PaidIntegral, P4AOrderedThirdCommonSchedule and
P4AOrderedThirdSameCoefficient. See SCHEDULE_SOURCE_MAP.json for source hashes.
The error remains explicit: this is no quantitative PP bound or final P2.5 endpoint.
-/
namespace ImbalancedChen.P2Saving16R17StrictFourteenCorners
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler (cell changed self_mem_cell)
open P2CanonicalWallFullResidualPayment (canonicalPrefix)
open P2Saving16NegativeOriginalFibreSum (selected)
open P2Saving16SevenOrderRowsCarrier (slotLower slotUpper)
open P2Saving16ActualUpperCornerCap (upperCorner upperCorner_in_box actual_upper_cap_same_Q_signed_product)
open P2Saving16FirstCornerReciprocalResidual (ordinaryPrefixContribution)
open P2Saving16FourteenCornerReciprocalResidual
  (scheduled_cell_ordinary_occurrence fourteenCornerSum r17_error_at_fourteen_corners)
open P2OriginalFourteenSignedRetainedLower (tupleWeight guardedTupleResidual)
open P2OriginalSaving16Full87SourceBinding (sourceCell atlasCell)
open P4AOriginalFull87SourceDictionary (newCap)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87OrdinarySignedGain (common_history_on_trim)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth coefficient keep)
open P4AOriginalNewFifthUnion (data)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P5OriginalCommonPositivePresieve (normalize)

/-- The compiler chooses beta, the aligned mesh and N0 once, before every cell,
pair and corner query. Each selected pair supplies the actual small divisor
for its physical fibre. The complete error and every counting term stay on
the same coefficient, with one original integral bound and compiler expense. -/
theorem r17_strict_fourteen_corners (eta : ℝ) (heta : 0 < eta) :
    ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0, ∀ a : ℝ, 0 < a → a ≤ 1/100 →
    ∀ nu v u_c betaMax : ℝ, 0 < nu → 0 < v → nu*v = 19/96 → 0 < u_c → 0 < betaMax →
    ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧ beta < betaMax ∧ beta^2 < v ∧
      nu*beta^2 < a ∧ nu*beta < 1/1000 ∧
    ∃ k N0 : ℕ, 2 ≤ N0 ∧
      let tau := alignedWidth (data e q a).m k
      0 < tau ∧ 12*tau < width r ∧ tau < P4AOriginalRemainingEighthSources.eta ∧
      ∀ N ≥ N0, Even N →
        let omega := nu*beta^2
        let w := (N : ℝ)^omega
        let z := cutoff N
        let L := (N : ℝ)^(nu*beta)
        let Q := moduli N w
        let rho := coefficient r n e q a omega N tau L
        let f := keep r n e q a omega N
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        let U := P4AOriginalR17PaidIntegral.integralUpper r n e q a omega eta u_c N
        normalize N (rawRoot (fresh (data e q a) omega N) N) <
            (∑ i, currentUpperEighteenPositive i) + eta ∧
        ((N : ℝ)/Real.log (N : ℝ)) *
            P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
            < u_c*singularNormalization N ∧
        physicalDensitySum Q rho < U ∧
        (∀ m : ℕ, rho m ≠ 0 → (m : ℝ) < (N : ℝ)^(599/1000 : ℝ)) ∧
        (∀ i : Fin 14, ∀ x ∈ selected f (fun _ => []) N N w z tau (width r) i,
          let p := canonicalPrefix 8 x.2
          let c := upperCorner N tau x.2
          let M := newCap (sourceCell i) c
          let J := P4AOriginalFull87SourceDictionary.selected (sourceCell i)
          actualPrimeTupleLog N p ∈ P2OriginalSaving16FourteenPhysicalAtlas.region ∧
          ordinaryPrefixContribution bank N N z p = tupleWeight p * guardedTupleResidual bank N N p ∧
          P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) c ∧
          (∀ u : Fin 8 → ℝ, (∀ j, slotLower N tau x.2 j ≤ u j ∧ u j ≤ slotUpper N tau x.2 j) →
            P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) u ∧
            M < VariableEnvelope.v (∑ j ∈ J, u j)) ∧
          P4AOriginalR17EighthParent.parent n e q a omega N (rosserAncestor 8 x.2.primeFactorsList) < M ∧
          ∀ y ∈ cell (fun _ => []) N N w z tau x.2,
            (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), canonicalPrefix 8 y k : ℕ) : ℝ) *
              (canonicalPrefix 8 y j : ℝ)^2 < (N : ℝ)^M) ∧
            (∀ j ∉ J, ((∏ k ∈ J, canonicalPrefix 8 y k : ℕ) : ℝ) *
              ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ J), canonicalPrefix 8 y k : ℕ) : ℝ) *
              (canonicalPrefix 8 y j : ℝ)^2 < (N : ℝ)^M) ∧
            x.1*y ∈ Q ∧
            ∀ G : ℕ → ℝ, rho (x.1*y) * G (x.1*y) =
              (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (x.1*y) -
                (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (x.1*y) -
                 actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (x.1*y)) +
                (if changed f (fun _ => []) N N w z tau y then
                  (if 0 ≤ (ArithmeticFunction.moebius y : ℝ) then actualSmallRosserPlus N N w L x.1
                   else actualSmallRosserMinus N N w L x.1) else 0)) * G (x.1*y)) ∧
        ∀ b T : ℝ, 0 < b → b < 1 → 0 < T → (Nat.ceil z : ℝ) ≤ T^(b/(1+b)) →
          ∀ c : Fin 14 → Fin 8 → ℝ,
            let mass := ((realHalfProductSource b N T).card : ℝ)
            let E := fourteenCornerSum r n e q a nu beta tau N b T c
            realPhysicalDistributionError b N T Q rho = E ∧
            (RealB b N : ℝ) ≤ mass*physicalDensitySum Q rho + E + (Nat.ceil z : ℝ) + (T+1) ∧
            (RealB b N : ℝ) ≤ mass*U + E + (Nat.ceil z : ℝ) + (T+1) := by
  obtain ⟨r0, hr⟩ := P4AOriginalR17PaidIntegral.original_signed_density_and_count_below eta heta
  refine ⟨r0, ?_⟩
  intro r hrr
  obtain ⟨n0, hn⟩ := hr r hrr
  obtain ⟨eo, heo, hord⟩ := scheduled_cell_ordinary_occurrence r
  obtain ⟨eh, heh, hhist⟩ := common_history_on_trim r
  refine ⟨n0, ?_⟩
  intro n hnn
  obtain ⟨ec, hec, hcomp⟩ := hn n hnn
  refine ⟨min ec (min eo eh), lt_min hec (lt_min heo heh), ?_⟩
  intro e he heBound
  have heSmall : (e : ℝ) < min eo eh := heBound.trans_le (min_le_right _ _)
  obtain ⟨qc, hqc, hc⟩ := hcomp e he (heBound.trans_le (min_le_left _ _))
  obtain ⟨qo, ho⟩ := hord e he (heSmall.trans_le (min_le_left _ _))
  obtain ⟨qh, _, hh⟩ := hhist e he (heSmall.trans_le (min_le_right _ _))
  refine ⟨max qc (max qo qh), hqc.trans_le (le_max_left _ _), ?_⟩
  intro q hq a ha haMax nu v u_c betaMax hnu hv huv hu hmax
  have hoh : max qo qh ≤ q := (le_max_right _ _).trans hq
  have hHistory := hh q ((le_max_right _ _).trans hoh) a haMax
  let meshMax := min (width r / 24) (P4AOriginalRemainingEighthSources.eta / 2)
  have hsource : 0 < P4AOriginalRemainingEighthSources.eta := by
    norm_num [P4AOriginalRemainingEighthSources.eta]
  have hmesh : 0 < meshMax := lt_min (div_pos (width_pos r) (by norm_num)) (half_pos hsource)
  obtain ⟨beta, hb, hb8, hbmax, hsq, hwa, hbl, k, N0, hN0, ⟨ht, hbound⟩, hpaid⟩ :=
    hc q ((le_max_left _ _).trans hq) a ha haMax nu v u_c betaMax hnu hv huv hu hmax meshMax hmesh
  let tau := alignedWidth (data e q a).m k
  have hw0 : tau ≤ width r / 24 := hbound.trans (min_le_left _ _)
  have he0 : tau ≤ P4AOriginalRemainingEighthSources.eta / 2 := hbound.trans (min_le_right _ _)
  have hw : 12*tau < width r := by linarith only [hw0, width_pos r]
  have heStrict : tau < P4AOriginalRemainingEighthSources.eta := by linarith only [he0, hsource]
  refine ⟨beta, hb, hb8, hbmax, hsq, hwa, hbl, k, N0, hN0, ht, hw, heStrict, ?_⟩
  intro N hN hEven
  let omega := nu*beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  have hNr : 1 < N := by omega
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hNr
  obtain ⟨hroot, hspend, hdensity, hsupport, hcount⟩ := hpaid N hN hEven
  refine ⟨hroot, hspend, hdensity, hsupport, ?_, ?_⟩
  · intro i x hx
    have hpair : x.1 ∈ actualSmallRosserSupport N N w ∧ x.2 ∈ P4AUpperTaggedParityCompiler.universe N N w z :=
      Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    have hsel := (Finset.mem_filter.mp hx).2
    have hOrd := ho n q a nu beta tau ((le_max_left _ _).trans hoh) haMax N hNr i x hx
    have hcap := fun (y : ℕ) (hy : y ∈ cell (fun _ => []) N N w z tau x.2) (G : ℕ → ℝ) =>
      actual_upper_cap_same_Q_signed_product r n e q a nu beta tau he.le hwa.le hHistory
        N hNreal ht hw heStrict i hpair.2 hsel.1 hsel.2.1 hy hpair.1 G
    have hself := hcap x.2 (self_mem_cell (fun _ => []) N N w z tau hpair.2) (fun _ => 1)
    have hrows := P2Saving16All96ClosedBox.original_all96_closed_box i N x.2 tau (width r)
      ht hw hsel.1 hsel.2.1
    have hcorner := hrows _ (upperCorner_in_box N x.2 tau ht)
    refine ⟨hOrd.1, hOrd.2, hcorner, fun u huBox => ⟨hrows u huBox, hself.1 u huBox⟩,
      hself.2.1, ?_⟩
    intro y hy
    obtain ⟨_, _, hfull, hcomplement, hmodulus, hproduct⟩ := hcap y hy (fun _ => 1)
    simp only [mul_one] at hproduct
    exact ⟨hfull, hcomplement, hmodulus, fun G =>
      congrArg (fun t : ℝ => t * G (x.1*y)) hproduct⟩
  · intro b T hbpos hbone hT hgate c
    have hcounts := hcount b T hbpos hbone hT hgate
    have herror := r17_error_at_fourteen_corners r n e q a nu beta tau N hNreal.le b T c
    dsimp only at hcounts herror ⊢
    rw [herror] at hcounts
    exact ⟨herror, hcounts⟩

end
end ImbalancedChen.P2Saving16R17StrictFourteenCorners
