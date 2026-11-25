import ImbalancedChen.P2Saving16FirstCornerReciprocalResidual
import ImbalancedChen.P2Saving16FourteenNegativeFibrePartition

/-!
SOURCE_ONLY / NOT COMPILED / UNEVALUATED.

The original first-corner occurrence and signed comparison are used at every
one of the fourteen original cell indices. Each cell may choose its own
corner. All other corners and one complete negative-inner complement remain
in the same physical distribution error, at the original full products.

This source requires the seven owner postimages of the finite-core package,
not their pre-extraction owners, and the 20261123 selected-api versions of
P4AOriginalR17PaidIntegral, P4AOrderedThirdCommonSchedule and
P4AOrderedThirdSameCoefficient. SCHEDULE_SOURCE_MAP.json records the exact
upstream sources and declaration reuse. No PP estimate is supplied here.
-/
namespace ImbalancedChen.P2Saving16FourteenCornerReciprocalResidual

noncomputable section

open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2CanonicalWallFullResidualPayment (canonicalPrefix canonicalTail)
open P2Saving16NegativeOriginalFibreSum (selected selectedSum negativeTerm)
open P2Saving16FourteenNegativeFibrePartition (complement14 negativeInner_exact_split14)
open P2Saving16OriginalPhysicalEightSource (originalPolicy)
open P2Saving16SameRhoDistributionFrontier (realHalfProductDiscrepancy)
open P2Saving16ActualUpperCornerCap (upperCorner)
open P2Saving16FirstCornerReciprocalResidual
  (selected_reciprocal_totient ordinaryPrefixContribution signedCornerGap)
open P2OriginalFourteenSignedRetainedLower (tupleWeight guardedTupleResidual)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalOrderedThirdActualCoefficient (keep)

/-- One pre-N history schedule supplies the original reciprocal-weighted
ordinary occurrence at every original cell index. The same ordered prefix
occurs once in the w=0 frontier; full rough tails remain in the selected pair. -/
theorem scheduled_cell_ordinary_occurrence (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        q0 ≤ q → a ≤ 1 / 100 →
        ∀ N : ℕ, 1 < N → ∀ (i : Fin 14) (x : ℕ × ℕ),
          let bank := P4AOriginalFull87UnionHistory.bank e q a
          let omega := nu * beta^2
          let w := (N : ℝ)^omega
          let p := canonicalPrefix 8 x.2
          x ∈ selected (keep r n e q a omega N) (fun _ => []) N N w (cutoff N)
              tau (width r) i →
          actualPrimeTupleLog N p ∈ P2OriginalSaving16FourteenPhysicalAtlas.region ∧
          ordinaryPrefixContribution bank N N (cutoff N) p =
            tupleWeight p * guardedTupleResidual bank N N p := by
  obtain ⟨e0, he0, he⟩ := P2Saving16ScheduledOriginalEight.scheduled_negative_inner_original_admission
    (width r) (width_pos r)
  refine ⟨e0, he0, ?_⟩
  intro e hepos he0'
  have heR : 0 < (e : ℝ) := by exact_mod_cast hepos
  obtain ⟨m0, hm0⟩ := he e hepos he0' ((e : ℝ)/20) (by positivity) (by linarith)
  refine ⟨max 1 m0, ?_⟩
  intro n q a nu beta tau hq ha N hN i x
  dsimp only
  intro hx
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let p := canonicalPrefix 8 x.2
  let f := keep r n e q a omega N
  have hsel := (Finset.mem_filter.mp hx).2
  have htrim := P2Saving16CommonTrimNegativeFibre.full87_trim_subset_original_region i
    (width r) (width_pos r) hsel.2.1
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
      (width_pos r) htrim
  · have hsum := firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 8
      (policy6 bank (N : ℝ)) (fun l : ℕ => 1 / ((l : ℝ) - 1))
      (roughPrimeUniverse N N 0 (cutoff N)) (roughPrimeUniverse_nodup N N 0 (cutoff N))
      (fun t => if t = p then guardedTupleResidual bank N N t else 0)
    simpa only [ordinaryPrefixContribution, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      if_pos hp0, tupleWeight] using hsum

/-- At every original cell, keep the signed original-minus-compiler gap
at the same full modulus. The reciprocal prefix weight factors only from
the coprime main term, with the small divisor and complete tail retained. -/
theorem corner_signed_comparison (data : OriginalData)
    (ret : List ℕ → Bool) (tag : ℕ → List Bool) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (omega v tau delta L b T : ℝ) (i : Fin 14) {x : ℕ × ℕ}
    (hx : x ∈ selected ret tag N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau delta i) :
    let w := (N : ℝ)^omega
    let z := (N : ℝ)^v
    let m := x.1 * x.2
    let G := realHalfProductDiscrepancy b N T
    (0 < tau → 12*tau < delta →
      P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (P2OriginalSaving16Full87SourceBinding.atlasCell i)
        (upperCorner N tau x.2)) ∧
      (actualSmallRoughRho (originalPolicy data N false) N cap w z L m -
        actualSmallRoughRho (policy6 data (N : ℝ) false) N cap w z L m) * G m -
        actualSmallRosserMinus N cap w L x.1 * G m =
      signedCornerGap data N cap w z L b T x := by
  dsimp only
  have h := (Finset.mem_filter.mp hx).2
  refine ⟨fun htau hwidth => P2Saving16All96ClosedBox.original_all96_closed_box i N x.2 tau delta htau hwidth
    h.1 h.2.1 _ (P2Saving16ActualUpperCornerCap.upperCorner_in_box N x.2 tau htau), ?_⟩
  let w := (N : ℝ)^omega
  let z := (N : ℝ)^v
  let m := x.1 * x.2
  have hc := P2Saving16NegativeCoefficientComparison.selected_original_and_compiler_coefficients
    (policy6 data (N : ℝ) false) (originalPolicy data N false) ret tag
    N cap w z tau delta L i (realHalfProductDiscrepancy b N T) hx
  have hfactor := selected_reciprocal_totient ret tag N cap omega v tau delta i hx
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

/-- A single error expression. Each cell contributes its chosen-corner
occurrences and all its other corners; the original negative-inner
complement and the before-four/fourth/positive-outer terms occur once. -/
def fourteenCornerSum (r n : ℕ) (e : ℚ) (q : ℕ)
    (a nu beta tau : ℝ) (N : ℕ) (b T : ℝ) (c : Fin 14 → Fin 8 → ℝ) : ℝ :=
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a omega N
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let S := fun i : Fin 14 => selected f (fun _ => []) N N w z tau (width r) i
  let G := realHalfProductDiscrepancy b N T
  P2Saving16ActualFourthFrontier.stoppedBeforeFour f N N w z L G +
    (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z),
      P2Saving16ActualFourthTuples.fourthTupleTerm f N N w z L G p) +
    (P2Saving16SignedCorrectionFamilies.positiveOuterSum f (fun _ => []) N N w z tau L G +
      ((∑ i : Fin 14,
        (∑ x ∈ (S i).filter (fun x => upperCorner N tau x.2 = c i),
          (actualSmallRoughRho (originalPolicy bank N false) N N w z L (x.1*x.2) -
            actualSmallRoughRho (policy6 bank (N : ℝ) false) N N w z L (x.1*x.2)) *
            G (x.1*x.2) - signedCornerGap bank N N w z L b T x) +
        (∑ x ∈ (S i).filter (fun x => upperCorner N tau x.2 ≠ c i),
          actualSmallRosserMinus N N w L x.1 * G (x.1*x.2))) +
        ∑ x ∈ complement14 f (fun _ => []) N N w z tau (width r),
          negativeTerm f (fun _ => []) N N w z tau L G x))

/-- Split the original negative-inner sum once into its fourteen disjoint
selected families and one unchanged complement. Only the chosen-corner
summands are rewritten; their complete signed gaps remain explicit. -/
theorem r17_error_at_fourteen_corners (r n : ℕ) (e : ℚ) (q : ℕ)
    (a nu beta tau : ℝ) (N : ℕ) (hN : 1 ≤ (N : ℝ)) (b T : ℝ)
    (c : Fin 14 → Fin 8 → ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let L := (N : ℝ)^(nu*beta)
    realPhysicalDistributionError b N T (P4AOriginalFull87CompiledCounting.moduli N w)
        (P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L) =
      fourteenCornerSum r n e q a nu beta tau N b T c := by
  classical
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a omega N
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let S := fun i : Fin 14 => selected f (fun _ => []) N N w z tau (width r) i
  let G := realHalfProductDiscrepancy b N T
  let F := fun x : ℕ × ℕ => actualSmallRosserMinus N N w L x.1 * G (x.1*x.2)
  let H := fun (i : Fin 14) (x : ℕ × ℕ) => upperCorner N tau x.2 = c i
  have hsplit (i : Fin 14) : selectedSum f (fun _ => []) N N w z tau (width r) L i G =
      (∑ x ∈ (S i).filter (H i),
        (actualSmallRoughRho (originalPolicy bank N false) N N w z L (x.1*x.2) -
          actualSmallRoughRho (policy6 bank (N : ℝ) false) N N w z L (x.1*x.2)) *
          G (x.1*x.2) - signedCornerGap bank N N w z L b T x) +
      ∑ x ∈ (S i).filter (fun x => ¬ H i x), F x := by
    change (∑ x ∈ S i, F x) = _
    rw [← Finset.sum_filter_add_sum_filter_not (S i) (H i) F]
    apply congrArg (fun u : ℝ => u + ∑ x ∈ (S i).filter (fun x => ¬ H i x), F x)
    apply Finset.sum_congr rfl
    intro x hx
    have hgap := (corner_signed_comparison bank f (fun _ => []) N N hN
      omega (19/96) tau (width r) L b T i (Finset.mem_filter.mp hx).1).2
    dsimp only [F, G, z, cutoff] at hgap ⊢
    linarith only [hgap]
  have hbase := P2Saving16SameRhoDistributionFrontier.r17_distribution_error_on_actual_fourths
    r n e q a nu beta tau N b T
  dsimp only at hbase ⊢
  rw [negativeInner_exact_split14 f (fun _ => []) N N
    w z tau (width r) L (width_pos r) G] at hbase
  simp_rw [hsplit] at hbase
  exact hbase

end
end ImbalancedChen.P2Saving16FourteenCornerReciprocalResidual
