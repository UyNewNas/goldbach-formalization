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

private theorem attach_indicator (p : Prop) (mu bminus bplus : ℝ) :
    signAttachedCoefficient (if p then mu else 0) bminus bplus =
      (if p then mu else 0) * (if 0 ≤ mu then bplus else bminus) := by
  classical
  by_cases hp : p <;> simp [hp, signAttachedCoefficient]

/-- At an occupied product, the compiler correction is the signed beta
value when the rough word changed, and zero otherwise. The value can be
negative or zero even in a changed cell. -/
theorem actual_product_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) {a d : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ universe N cap w z) :
    rho ret tag N cap w z tau L (a * d) -
      actualSmallRoughRho ret N cap w z L (a * d) =
    if changed ret tag N cap w z tau d then
      (if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a)
    else 0 := by
  let P := d ∈ universe N cap w z ∧
    P4AFull87TaggedAtomValue.admit ret tag N cap w z tau
      (label tag N tau d)
  let R := d ∈ rawSupport ret N cap w z
  let mu : ℝ := ArithmeticFunction.moebius d
  let bm := actualSmallRosserMinus N cap w L a
  let bp := actualSmallRosserPlus N cap w L a
  have hc : coefficient ret tag N cap w z tau d = if P then mu else 0 := by
    rw [P4AFull87TaggedAtomValue.literal_value]
    dsimp only [P4AFull87TaggedAtomValue.occupied, P, mu]
    split_ifs <;> simp
  have hr : raw ret N cap w z d = if R then mu else 0 := by
    simpa only [R, mu] using raw_value ret N cap w z d
  have hdelta : coefficient ret tag N cap w z tau d - raw ret N cap w z d =
      if changed ret tag N cap w z tau d then 1 else 0 := by
    have h := abs_coefficient_sub_raw ret tag N cap w z tau hd
    rw [abs_of_nonneg (sub_nonneg.mpr (raw_le_coefficient ret tag N cap w z tau d))] at h
    exact h
  have hcompiled : rho ret tag N cap w z tau L (a * d) =
      signAttachedCoefficient (coefficient ret tag N cap w z tau d) bm bp := by
    rw [rho_at_product ret tag N cap w z tau L ha hd]
    rfl
  have hraw : actualSmallRoughRho ret N cap w z L (a * d) =
      signAttachedCoefficient (raw ret N cap w z d) bm bp := by
    have h := smallRoughRho_mul
      (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
      (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm)
      (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) ha hd
    rw [raw_attachment_eq_actual ret N cap w z L] at h
    exact h
  rw [hcompiled, hraw]
  calc
    _ = (coefficient ret tag N cap w z tau d - raw ret N cap w z d) *
        (if 0 ≤ mu then bp else bm) := by
          rw [hc, hr, attach_indicator, attach_indicator]
          ring
    _ = _ := by
      rw [hdelta]
      dsimp only [mu, bm, bp]
      split_ifs <;> simp

/-- The same actual occurrence test stays attached to its full modulus;
there is no extra enumeration, sign replacement, or factorial. -/
theorem actual_weighted_product_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) {a d : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ universe N cap w z) (G : ℕ → ℝ) :
    (rho ret tag N cap w z tau L (a * d) -
      actualSmallRoughRho ret N cap w z L (a * d)) * G (a * d) =
    (if changed ret tag N cap w z tau d then
      (if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a)
     else 0) * G (a * d) :=
  congrArg (fun x : ℝ => x * G (a * d))
    (actual_product_correction ret tag N cap w z tau L ha hd)

/-- The actual R17 compiler coefficient at this full modulus equals the
R17 sixth raw attachment minus the transported historical signed change,
plus the one literal compiler correction. All terms use the same beta. -/
theorem r17_actual_coefficient_at_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) {s d : ℕ}
    (hs : s ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (nu * beta ^ 2)))
    (hd : d ∈ universe N N ((N : ℝ) ^ (nu * beta ^ 2))
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
