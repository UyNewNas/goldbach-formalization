import ImbalancedChen.P2Saving16ActualCompilerDifference
import ImbalancedChen.P4AOriginalR17PaidIntegral
import ImbalancedChen.P4AFiniteCapTaggedPayment

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

Sum the actual changed-cell correction on the unique small/rough carrier.
The signed beta value and the full-modulus test stay inside every summand.
No geometric-corner equality or signed distribution estimate is asserted. -/
namespace ImbalancedChen.P2Saving16WeightedCompilerLedger
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16ActualCompilerDifference
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)

/-- Literal compiler correction with one term per actual small/rough pair.
The test is evaluated at the original full modulus and retains its sign. -/
def correctionSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) (universe N cap w z),
    (if changed ret tag N cap w z tau x.2 then
      (if 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ) then
        actualSmallRosserPlus N cap w L x.1
       else actualSmallRosserMinus N cap w L x.1)
     else 0) * G (x.1 * x.2)

/-- An exact signed weighted equality on the complete physical carrier.
Uniqueness of the small/rough split gives each full modulus one occurrence. -/
theorem actual_weighted_correction_sum
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) :
    (∑ m ∈ support N cap w z,
      (rho ret tag N cap w z tau L m - actualSmallRoughRho ret N cap w z L m) * G m) =
      correctionSum ret tag N cap w z tau L G := by
  change (∑ m ∈ smallRoughModuli (actualSmallRosserSupport N cap w) (universe N cap w z),
      (rho ret tag N cap w z tau L m - actualSmallRoughRho ret N cap w z L m) * G m) = _
  rw [sum_smallRoughModuli
    (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
    (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm)
    (fun m => (rho ret tag N cap w z tau L m - actualSmallRoughRho ret N cap w z L m) * G m)]
  unfold correctionSum
  apply Finset.sum_congr rfl
  intro x hx
  change x ∈ (actualSmallRosserSupport N cap w) ×ˢ (universe N cap w z) at hx
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp hx
  exact actual_weighted_product_correction ret tag N cap w z tau L ha hd G

/-- In density units this is exactly the compiler-versus-raw attached
increment, before any absolute-value estimate or reserve payment. -/
theorem actual_density_correction_sum
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) :
    physicalDensitySum (support N cap w z) (rho ret tag N cap w z tau L) -
      physicalDensitySum (support N cap w z) (actualSmallRoughRho ret N cap w z L) =
    correctionSum ret tag N cap w z tau L (fun m => 1 / (Nat.totient m : ℝ)) := by
  simpa only [physicalDensitySum, div_eq_mul_inv, one_div, sub_mul, Finset.sum_sub_distrib] using
    actual_weighted_correction_sum ret tag N cap w z tau L (fun m => 1 / (Nat.totient m : ℝ))

/-- The existing single compiler expense already contains exactly the
absolute value of this signed correction, alongside its beta projection
defect. This identity adds no new reserve or positivity premise. -/
theorem compilerExpense_eq_beta_add_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) :
    P4AFiniteCapTaggedConstructor.compilerExpense ret tag N cap w z tau L =
      (p4aReservePhysicalDensity ret N cap w z L -
        actualSmallEulerProduct N cap w * p4aReserveRawDensity ret N cap w z) +
      |correctionSum ret tag N cap w z tau L (fun m => 1 / (Nat.totient m : ℝ))| := by
  have hr := raw_physical_density_on_universe ret N cap w z L
  rw [raw_attachment_eq_actual ret N cap w z L] at hr
  change physicalDensitySum (support N cap w z) (actualSmallRoughRho ret N cap w z L) =
    p4aReservePhysicalDensity ret N cap w z L at hr
  have hc := actual_density_correction_sum ret tag N cap w z tau L
  rw [hr] at hc
  unfold P4AFiniteCapTaggedConstructor.compilerExpense
  rw [hc]

/-- The actual R17 envelope coefficient on its own Q, with one beta and
one arbitrary full-q test. The compiler correction is an exact summand;
it is not a second u_c or an independently selected sieve bound. -/
theorem r17_same_Q_weighted_ledger
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (G : ℕ → ℝ) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let Q := moduli N w
    let f := keep r n e q a omega N
    (∑ m ∈ Q, coefficient r n e q a omega N tau L m * G m) =
      (∑ m ∈ Q, actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L m * G m) -
      (∑ m ∈ Q, (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L m -
        actualSmallRoughRho (policy (width r) n e q a N false) N N w z L m) * G m) +
      correctionSum f (fun _ => []) N N w z tau L G := by
  let omega := nu * beta ^ 2
  let w := (N : ℝ) ^ omega
  let z := cutoff N
  let L := (N : ℝ) ^ (nu * beta)
  let Q := moduli N w
  let f := keep r n e q a omega N
  have hc := actual_weighted_correction_sum f (fun _ => []) N N w z tau L G
  change (∑ m ∈ Q, (coefficient r n e q a omega N tau L m -
    actualSmallRoughRho (P4AOriginalR17EighthParent.orderedEighth r n e q a omega N false)
      N N w z L m) * G m) = correctionSum f (fun _ => []) N N w z tau L G at hc
  have ht := P2Saving16AttachedSignedTransport.r17_envelope_carrier_attached_difference
    r n e q a nu beta he hcut hh N hN G
  change (∑ m ∈ Q, (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L m -
    actualSmallRoughRho (P4AOriginalR17EighthParent.orderedEighth r n e q a omega N false)
      N N w z L m) * G m) =
    (∑ m ∈ Q, (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L m -
      actualSmallRoughRho (policy (width r) n e q a N false) N N w z L m) * G m) at ht
  change (∑ m ∈ Q, coefficient r n e q a omega N tau L m * G m) =
    (∑ m ∈ Q, actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L m * G m) -
    (∑ m ∈ Q, (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L m -
      actualSmallRoughRho (policy (width r) n e q a N false) N N w z L m) * G m) +
    correctionSum f (fun _ => []) N N w z tau L G
  simp only [sub_mul, Finset.sum_sub_distrib] at hc ht ⊢
  linarith only [hc, ht]

/-- Density-scale specialization for the same literal Q and rho used by
the existing integral envelope. The signed correction appears once. -/
theorem r17_same_Q_density_ledger
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let Q := moduli N w
    let f := keep r n e q a omega N
    physicalDensitySum Q (coefficient r n e q a omega N tau L) =
      physicalDensitySum Q (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L) -
      (physicalDensitySum Q (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L) -
       physicalDensitySum Q (actualSmallRoughRho (policy (width r) n e q a N false) N N w z L)) +
      correctionSum f (fun _ => []) N N w z tau L (fun m => 1 / (Nat.totient m : ℝ)) := by
  simpa only [physicalDensitySum, div_eq_mul_inv, one_div, sub_mul, Finset.sum_sub_distrib] using
    r17_same_Q_weighted_ledger r n e q a nu beta tau he hcut hh N hN
      (fun m => 1 / (Nat.totient m : ℝ))

end
end ImbalancedChen.P2Saving16WeightedCompilerLedger
