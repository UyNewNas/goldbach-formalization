import ImbalancedChen.P2Saving16NegativeFiniteCore
import ImbalancedChen.P2Saving16AttachedSignedTransport
import ImbalancedChen.P4AFull87TaggedAtomValue

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

The literal upper compiler correction at an occupied small/rough product.
The formula retains the beta sign and the same actual changed-cell test.
No geometric-corner identity, PP estimate, or additional payment follows. -/
namespace ImbalancedChen.P2Saving16ActualCompilerDifference
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)

/-- The actual R17 compiler coefficient at this full modulus equals the
R17 sixth raw attachment minus the transported historical signed change,
plus the one literal compiler correction. All terms use the same beta. -/
theorem r17_actual_coefficient_at_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) {s d : ℕ}
    (hs : s ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (nu * beta ^ 2)))
    (hd : d ∈ «universe» N N ((N : ℝ) ^ (nu * beta ^ 2))
      (P4AOriginalFull87RawChronology.cutoff N)) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let f := P4AOriginalOrderedThirdActualCoefficient.keep r n e q a omega N
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (s * d) =
      actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (s * d) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (s * d) -
         actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (s * d)) +
      (if changed f (fun _ => []) N N w z tau d then
        (if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then actualSmallRosserPlus N N w L s
         else actualSmallRosserMinus N N w L s)
       else 0) := by
  let omega := nu * beta ^ 2
  let w := (N : ℝ) ^ omega
  let z := P4AOriginalFull87RawChronology.cutoff N
  let L := (N : ℝ) ^ (nu * beta)
  let f := P4AOriginalOrderedThirdActualCoefficient.keep r n e q a omega N
  have hc := actual_product_correction f (fun _ => []) N N w z tau L hs hd
  have ht := P2Saving16AttachedSignedTransport.r17_attached_coefficient_difference
    r n e q a omega he hcut hh N hN N w z L (s * d)
  change P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (s * d) -
      actualSmallRoughRho (orderedEighth r n e q a omega N false) N N w z L (s * d) = _ at hc
  dsimp only
  linarith only [hc, ht]

end
end ImbalancedChen.P2Saving16ActualCompilerDifference
