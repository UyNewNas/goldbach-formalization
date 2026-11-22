import ImbalancedChen.P2Saving16NegativeNoDeletion
import ImbalancedChen.P2Saving16ActualUpperCornerCap
import ImbalancedChen.P2OriginalFourteenSignedRetainedLower

/-! Source only. The corner is the upper endpoint of the eight fine labels of an
actual negative-inner occurrence in original ascending cell 0. Different small
divisors, tails and ordered tuples with that corner retain their own summands.
The reciprocal prefix weight factors out of the coprime main term only. -/
namespace ImbalancedChen.P2Saving16FirstCornerReciprocalResidual
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2CanonicalWallFullResidualPayment (canonicalPrefix canonicalTail canonical_prefix_tail_data)
open P2Saving16NegativeOriginalFibreSum (selected selectedSum complementSum)
open P2Saving16OriginalPhysicalEightSource (originalPolicy)
open P2Saving16SameRhoDistributionFrontier (realHalfProductDiscrepancy)
open P2Saving16ActualUpperCornerCap (upperCorner)
open P2OriginalFourteenSignedRetainedLower (tupleWeight guardedTupleResidual)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalOrderedThirdActualCoefficient (keep)

/-- At the full occupied modulus, the ordinary ordered-eight weight and the
two remaining reciprocal totients have exactly their original factors. -/
theorem selected_reciprocal_totient (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (omega v tau delta : ℝ) (i : Fin 14) {x : ℕ × ℕ}
    (hx : x ∈ selected ret tag N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau delta i) :
    1 / (Nat.totient (x.1 * x.2) : ℝ) =
      tupleWeight (canonicalPrefix 8 x.2) /
        ((Nat.totient x.1 : ℝ) * (Nat.totient (canonicalTail 8 x.2) : ℝ)) := by
  have h := Finset.mem_filter.mp hx
  have hpair : x.1 ∈ actualSmallRosserSupport N cap ((N : ℝ)^omega) ∧
      x.2 ∈ universe N cap ((N : ℝ)^omega) ((N : ℝ)^v) :=
    Finset.mem_product.mp h.1
  obtain ⟨hp, hinj, _, hcop, hprod⟩ := canonical_prefix_tail_data hpair.2 h.2.1
  have hsmall := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hpair.1)
    (P2LowerFiniteCellRounding.universe_rough N cap _ _ hpair.2)
  have hphi : (Nat.totient x.2 : ℝ) =
      (Nat.totient (∏ j, canonicalPrefix 8 x.2 j) : ℝ) *
        (Nat.totient (canonicalTail 8 x.2) : ℝ) := by
    calc
      _ = (Nat.totient ((∏ j, canonicalPrefix 8 x.2 j) * canonicalTail 8 x.2) : ℝ) :=
        congrArg (fun d : ℕ => (Nat.totient d : ℝ)) hprod.symm
      _ = _ := by rw [Nat.totient_mul hcop, Nat.cast_mul]
  have hw : tupleWeight (canonicalPrefix 8 x.2) =
      1 / (Nat.totient (∏ j, canonicalPrefix 8 x.2 j) : ℝ) :=
    (actualPrimeBoxTuple_reciprocalTotient hp hinj).symm
  rw [Nat.totient_mul hsmall, Nat.cast_mul, hphi, hw]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul] <;> ring

/-- The original reciprocal-weighted ordinary frontier tested at one ordered prefix. -/
def ordinaryPrefixContribution (data : OriginalData) (N cap : ℕ) (z : ℝ)
    (p : Fin 8 → ℕ) : ℝ :=
  ((firstExitDepthFrontier 8 (policy6 data (N : ℝ)) (fun l : ℕ => 1 / ((l : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun st =>
      (st.selectedPrefix.map (fun l : ℕ => 1 / ((l : ℝ) - 1))).prod *
        (if primeHistoryTuple 8 st.selectedPrefix = p
          then guardedTupleResidual data N cap (primeHistoryTuple 8 st.selectedPrefix)
          else 0))).sum

/-- The actual ordered prefix has its own ordinary signed residual once in
the reciprocal-weighted w=0 frontier, on the existing pre-N history schedule. -/
theorem scheduled_first_cell_ordinary_occurrence (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        q0 ≤ q → a ≤ 1 / 100 →
        ∀ N : ℕ, 1 < N → ∀ x : ℕ × ℕ,
          let bank := P4AOriginalFull87UnionHistory.bank e q a
          let omega := nu * beta^2
          let w := (N : ℝ)^omega
          let p := canonicalPrefix 8 x.2
          x ∈ selected (keep r n e q a omega N) (fun _ => []) N N w (cutoff N)
              tau (width r) 0 →
          actualPrimeTupleLog N p ∈ P2OriginalSaving16FourteenPhysicalAtlas.region ∧
          ordinaryPrefixContribution bank N N (cutoff N) p =
            tupleWeight p * guardedTupleResidual bank N N p := by
  obtain ⟨e0, he0, he⟩ := P2Saving16ScheduledOriginalEight.scheduled_negative_inner_original_admission
    (width r) (P4AOriginalFull87HistoryCore.width_pos r)
  refine ⟨e0, he0, ?_⟩
  intro e hepos he0'
  have heR : 0 < (e : ℝ) := by exact_mod_cast hepos
  obtain ⟨m0, hm0⟩ := he e hepos he0' ((e : ℝ)/20) (by positivity) (by linarith)
  refine ⟨max 1 m0, ?_⟩
  intro n q a nu beta tau hq ha N hN x
  dsimp only
  intro hx
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let p := canonicalPrefix 8 x.2
  let f := keep r n e q a omega N
  have hsel := (Finset.mem_filter.mp hx).2
  have htrim := P2Saving16CommonTrimNegativeFibre.full87_trim_subset_original_region 0
    (width r) (P4AOriginalFull87HistoryCore.width_pos r) hsel.2.1
  have hneg : (ArithmeticFunction.moebius x.2 : ℝ) < 0 := hsel.2.2.1
  have hchanged : changed f (fun _ => []) N N w (cutoff N) tau x.2 := by
    simpa only [changed, if_neg (not_le_of_gt hneg)] using hsel.2.2.2
  have hdm : m0 ≤ bank.m := by
    have hm : m0 ≤ q := (le_max_right 1 m0).trans hq
    change m0 ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
    unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
    omega
  have hp0 : p ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
      (roughPrimeUniverse N N 0 (cutoff N)) :=
    hm0 r n q a nu beta tau rfl rfl hdm ha N hN hsel.1 htrim hneg hchanged
  refine ⟨?_, ?_⟩
  · rw [P2Saving16ScheduledOriginalEight.original_tuple_log_eq_actual_eight N x.2 hsel.1]
    exact P2OriginalSaving16TrimmedHistory.trimmedRegion_subset_region (width r)
      (P4AOriginalFull87HistoryCore.width_pos r) htrim
  · have hsum := firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 8
      (policy6 bank (N : ℝ)) (fun l : ℕ => 1 / ((l : ℝ) - 1))
      (roughPrimeUniverse N N 0 (cutoff N)) (roughPrimeUniverse_nodup N N 0 (cutoff N))
      (fun t => if t = p then guardedTupleResidual bank N N t else 0)
    simpa only [ordinaryPrefixContribution, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      if_pos hp0, tupleWeight] using hsum

/-- Original minus compiler at one full product. The beta and the two
arithmetic masses are evaluated at the physical small divisor and modulus. -/
def signedCornerGap (data : OriginalData) (N cap : ℕ) (w z L b T : ℝ)
    (x : ℕ × ℕ) : ℝ :=
  let d := x.2
  let m := x.1 * d
  (if d ∈ rawSupport (originalPolicy data N false) N cap w z ∧
      d ∉ rawSupport (policy6 data (N : ℝ) false) N cap w z then (-2 : ℝ) else -1) *
    actualSmallRosserMinus N cap w L x.1 *
    (realHalfProductCongruenceMass b N T m -
      realHalfProductCoprimeMass b N T m * (tupleWeight (canonicalPrefix 8 d) /
        ((Nat.totient x.1 : ℝ) * (Nat.totient (canonicalTail 8 d) : ℝ))))

theorem first_corner_signed_comparison (data : OriginalData)
    (ret : List ℕ → Bool) (tag : ℕ → List Bool) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (omega v tau delta L b T : ℝ) {x : ℕ × ℕ}
    (hx : x ∈ selected ret tag N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau delta 0) :
    let w := (N : ℝ)^omega
    let z := (N : ℝ)^v
    let m := x.1 * x.2
    let G := realHalfProductDiscrepancy b N T
    (0 < tau → 12*tau < delta →
      P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (P2OriginalSaving16Full87SourceBinding.atlasCell 0)
        (upperCorner N tau x.2)) ∧
      (actualSmallRoughRho (originalPolicy data N false) N cap w z L m -
        actualSmallRoughRho (policy6 data (N : ℝ) false) N cap w z L m) * G m -
        actualSmallRosserMinus N cap w L x.1 * G m =
      signedCornerGap data N cap w z L b T x := by
  dsimp only
  have h := (Finset.mem_filter.mp hx).2
  refine ⟨fun htau hwidth => P2Saving16All96ClosedBox.original_all96_closed_box 0 N x.2 tau delta htau hwidth
    h.1 h.2.1 _ (P2Saving16ActualUpperCornerCap.upperCorner_in_box N x.2 tau htau), ?_⟩
  let w := (N : ℝ)^omega
  let z := (N : ℝ)^v
  let m := x.1 * x.2
  have hc := P2Saving16NegativeCoefficientComparison.selected_original_and_compiler_coefficients
    (policy6 data (N : ℝ) false) (originalPolicy data N false) ret tag
    N cap w z tau delta L 0 (realHalfProductDiscrepancy b N T) hx
  have hfactor := selected_reciprocal_totient ret tag N cap omega v tau delta 0 hx
  have hmain : realHalfProductCoprimeMass b N T m / (Nat.totient m : ℝ) =
      realHalfProductCoprimeMass b N T m *
        (tupleWeight (canonicalPrefix 8 x.2) /
          ((Nat.totient x.1 : ℝ) * (Nat.totient (canonicalTail 8 x.2) : ℝ))) := by
    simpa only [div_eq_mul_inv, one_mul] using
      congrArg (fun k : ℝ => realHalfProductCoprimeMass b N T m * k) hfactor
  rw [hc.2.1, P2Saving16NegativeNoDeletion.original_switch_only_additions data N cap hN w z x.2]
  simp only [realHalfProductDiscrepancy, signedCornerGap]
  rw [hmain]
  split_ifs <;> ring

/-- Occurrence sum after replacing the compiler correction at one upper
corner by the original change minus its signed gap. -/
def firstCellCornerSum (r n : ℕ) (e : ℚ) (q : ℕ)
    (a nu beta tau : ℝ) (N : ℕ) (b T : ℝ) (c : Fin 8 → ℝ) : ℝ :=
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a omega N
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let S := selected f (fun _ => []) N N w z tau (width r) 0
  let G := realHalfProductDiscrepancy b N T
  P2Saving16ActualFourthFrontier.stoppedBeforeFour f N N w z L G +
    (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z),
      P2Saving16ActualFourthTuples.fourthTupleTerm f N N w z L G p) +
    (P2Saving16SignedCorrectionFamilies.positiveOuterSum f (fun _ => []) N N w z tau L G +
      (((∑ x ∈ S.filter (fun x => upperCorner N tau x.2 = c),
          (actualSmallRoughRho (originalPolicy bank N false) N N w z L (x.1*x.2) -
            actualSmallRoughRho (policy6 bank (N : ℝ) false) N N w z L (x.1*x.2)) *
            G (x.1*x.2) - signedCornerGap bank N N w z L b T x) +
        (∑ x ∈ S.filter (fun x => upperCorner N tau x.2 ≠ c),
          actualSmallRosserMinus N N w L x.1 * G (x.1*x.2))) +
        complementSum f (fun _ => []) N N w z tau (width r) L 0 G))

/-- Other corners of cell 0 and the whole pre-existing negative-inner
complement retain all their occurrences in the same physical error. -/
theorem r17_error_at_first_cell_corner (r n : ℕ) (e : ℚ) (q : ℕ)
    (a nu beta tau : ℝ) (N : ℕ) (hN : 1 ≤ (N : ℝ)) (b T : ℝ) (c : Fin 8 → ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let L := (N : ℝ)^(nu*beta)
    realPhysicalDistributionError b N T (P4AOriginalFull87CompiledCounting.moduli N w)
        (P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L) =
      firstCellCornerSum r n e q a nu beta tau N b T c := by
  classical
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a omega N
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let S := selected f (fun _ => []) N N w z tau (width r) 0
  let G := realHalfProductDiscrepancy b N T
  let F := fun x : ℕ × ℕ => actualSmallRosserMinus N N w L x.1 * G (x.1*x.2)
  let H := fun x : ℕ × ℕ => upperCorner N tau x.2 = c
  have hsplit : selectedSum f (fun _ => []) N N w z tau (width r) L 0 G =
      (∑ x ∈ S.filter H,
        (actualSmallRoughRho (originalPolicy bank N false) N N w z L (x.1*x.2) -
          actualSmallRoughRho (policy6 bank (N : ℝ) false) N N w z L (x.1*x.2)) *
          G (x.1*x.2) - signedCornerGap bank N N w z L b T x) +
      ∑ x ∈ S.filter (fun x => ¬ H x), F x := by
    change (∑ x ∈ S, F x) = _
    rw [← Finset.sum_filter_add_sum_filter_not S H F]
    apply congrArg (fun u : ℝ => u + ∑ x ∈ S.filter (fun x => ¬ H x), F x)
    apply Finset.sum_congr rfl
    intro x hx
    have hgap := (first_corner_signed_comparison bank f (fun _ => []) N N hN
      omega (19/96) tau (width r) L b T (Finset.mem_filter.mp hx).1).2
    dsimp only [F, G, z, cutoff] at hgap ⊢
    linarith only [hgap]
  have hbase := P2Saving16SameRhoDistributionFrontier.r17_distribution_error_on_actual_fourths
    r n e q a nu beta tau N b T
  dsimp only at hbase ⊢
  rw [P2Saving16NegativeOriginalFibreSum.negativeInner_exact_split f (fun _ => []) N N
    w z tau (width r) L 0 G, hsplit] at hbase
  exact hbase

/-- The ordinary occurrence and the corner grouped error share the original
R17 beta, mesh, carrier, density bound and single compiler expense. -/
theorem r17_scheduled_first_cell_corner (eta : ℝ) (heta : 0 < eta) :
    ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0, ∀ a : ℝ, 0 < a → a ≤ 1/100 →
    ∀ nu v u_c betaMax : ℝ, 0 < nu → 0 < v → nu*v = 19/96 → 0 < u_c → 0 < betaMax →
    ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧ beta < betaMax ∧ beta^2 < v ∧
      nu*beta^2 < a ∧ nu*beta < 1/1000 ∧
    ∃ k N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      let omega := nu * beta^2
      let w := (N : ℝ)^omega
      let L := (N : ℝ)^(nu*beta)
      let z := cutoff N
      let tau := P4AOriginalOrderedThirdActualCoefficient.alignedWidth (P4AOriginalNewFifthUnion.data e q a).m k
      let Q := P4AOriginalFull87CompiledCounting.moduli N w
      let rho := P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L
      let bank := P4AOriginalFull87UnionHistory.bank e q a
      let f := keep r n e q a omega N
      let U := P4AOriginalR17PaidIntegral.integralUpper r n e q a omega eta u_c N
      ((N : ℝ)/Real.log (N : ℝ)) *
          P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          < u_c * singularNormalization N ∧
      physicalDensitySum Q rho < U ∧
      (∀ x ∈ selected f (fun _ => []) N N w z tau (width r) 0,
        let p := canonicalPrefix 8 x.2
        actualPrimeTupleLog N p ∈ P2OriginalSaving16FourteenPhysicalAtlas.region ∧
        ordinaryPrefixContribution bank N N z p = tupleWeight p * guardedTupleResidual bank N N p) ∧
      ∀ b T : ℝ, 0 < b → b < 1 → 0 < T → (Nat.ceil z : ℝ) ≤ T^(b/(1+b)) →
      ∀ c : Fin 8 → ℝ,
        let mass := ((realHalfProductSource b N T).card : ℝ)
        let E := firstCellCornerSum r n e q a nu beta tau N b T c
        realPhysicalDistributionError b N T Q rho = E ∧
        (RealB b N : ℝ) ≤ mass*physicalDensitySum Q rho + E + (Nat.ceil z : ℝ) + (T+1) ∧
        (RealB b N : ℝ) ≤ mass*U + E + (Nat.ceil z : ℝ) + (T+1) := by
  obtain ⟨r0, hr⟩ := P4AOriginalR17PaidIntegral.original_signed_density_and_count eta heta
  refine ⟨r0, ?_⟩
  intro r hrr
  obtain ⟨n0, hn⟩ := hr r hrr
  obtain ⟨eo, heo, hord⟩ := scheduled_first_cell_ordinary_occurrence r
  refine ⟨n0, ?_⟩
  intro n hnn
  obtain ⟨ec, hec, hcomp⟩ := hn n hnn
  refine ⟨min ec eo, lt_min hec heo, ?_⟩
  intro e he heBound
  obtain ⟨qc, hqc, hcq⟩ := hcomp e he (heBound.trans_le (min_le_left _ _))
  obtain ⟨qo, hoq⟩ := hord e he (heBound.trans_le (min_le_right _ _))
  refine ⟨max qc qo, hqc.trans_le (le_max_left _ _), ?_⟩
  intro q hq a ha haMax nu v u_c betaMax hnu hv huv hu hmax
  obtain ⟨beta, hb, hb8, hbmax, hsq, hwa, hbl, k, N0, hN0, hpaid⟩ :=
    hcq q ((le_max_left _ _).trans hq) a ha haMax nu v u_c betaMax hnu hv huv hu hmax
  refine ⟨beta, hb, hb8, hbmax, hsq, hwa, hbl, k, N0, hN0, ?_⟩
  intro N hN hEven
  let tau := P4AOriginalOrderedThirdActualCoefficient.alignedWidth (P4AOriginalNewFifthUnion.data e q a).m k
  have hNr : 1 < N := by omega
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hNr.le
  obtain ⟨_, hspend, hdensity, _, hcount⟩ := hpaid N hN hEven
  refine ⟨hspend, hdensity, ?_, ?_⟩
  · intro x hx
    exact hoq n q a nu beta tau ((le_max_right _ _).trans hq) haMax N hNr x hx
  · intro b T hbpos hbone hT hgate c
    have hcounts := hcount b T hbpos hbone hT hgate
    have herror := r17_error_at_first_cell_corner r n e q a nu beta tau N hNreal b T c
    dsimp only at hcounts herror ⊢
    rw [herror] at hcounts
    exact ⟨herror, hcounts⟩

end
end ImbalancedChen.P2Saving16FirstCornerReciprocalResidual
