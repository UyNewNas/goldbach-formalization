import ImbalancedChen.P4AOriginalR17EighthSignedTransport
import ImbalancedChen.P4AUpperTaggedBetaAttachment
import ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

Lift the already supplied R17 versus enlarged historical sixth-to-eighth
rough-coefficient difference to the literal small/rough attached full
modulus. This is an equality of differences, not equality of the four
individual coefficients and not an equality with the ALL/ANY compiler. -/
namespace ImbalancedChen.P2Saving16AttachedSignedTransport
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler
open P4AUpperTaggedBetaAttachment
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)

/-- A raw coefficient is either zero or the fixed Mobius value of its
rough modulus. Hence the beta sign is determined by that modulus even
when a particular policy omits it. The zero branch contributes zero. -/
private theorem attach_indicator (p : Prop) (mu bminus bplus : ℝ) :
    signAttachedCoefficient (if p then mu else 0) bminus bplus =
      (if p then mu else 0) * (if 0 ≤ mu then bplus else bminus) := by
  classical
  by_cases hp : p <;> simp [hp, signAttachedCoefficient]

/-- Difference equality for four original raw policies lifts through the
same small/rough attachment. No sign, size or positivity premise on the
beta values is needed. -/
private theorem attached_difference_of_raw
    (u v s t : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (h : ∀ d : ℕ, raw u N cap w z d - raw v N cap w z d =
      raw s N cap w z d - raw t N cap w z d) (m : ℕ) :
    actualSmallRoughRho u N cap w z L m - actualSmallRoughRho v N cap w z L m =
      actualSmallRoughRho s N cap w z L m - actualSmallRoughRho t N cap w z L m := by
  rw [← raw_attachment_eq_actual u N cap w z L,
      ← raw_attachment_eq_actual v N cap w z L,
      ← raw_attachment_eq_actual s N cap w z L,
      ← raw_attachment_eq_actual t N cap w z L]
  simp only [smallRoughRho, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hd := h x.2
  rw [raw_value, raw_value, raw_value, raw_value] at hd
  simp only [smallRoughPairCoefficient]
  rw [raw_value, raw_value, raw_value, raw_value,
      attach_indicator, attach_indicator, attach_indicator, attach_indicator]
  calc
    _ = ((if x.2 ∈ rawSupport u N cap w z then (ArithmeticFunction.moebius x.2 : ℝ) else 0) -
          (if x.2 ∈ rawSupport v N cap w z then (ArithmeticFunction.moebius x.2 : ℝ) else 0)) *
        (if 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ) then actualSmallRosserPlus N cap w L x.1
         else actualSmallRosserMinus N cap w L x.1) := by ring
    _ = ((if x.2 ∈ rawSupport s N cap w z then (ArithmeticFunction.moebius x.2 : ℝ) else 0) -
          (if x.2 ∈ rawSupport t N cap w z then (ArithmeticFunction.moebius x.2 : ℝ) else 0)) *
        (if 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ) then actualSmallRosserPlus N cap w L x.1
         else actualSmallRosserMinus N cap w L x.1) := by rw [hd]
    _ = _ := by ring

/-- At every full modulus the complete R17 and historical enlarged-bank
sixth-to-eighth signed differences use the same small-prime beta pair.
`HistoryOnTrim` is the existing common-history condition used by the
rough transport; this theorem does not supply a compiler or PP bound. -/
theorem r17_attached_coefficient_difference
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0 ≤ e) (hcut : omega ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (cap : ℕ) (w z L : ℝ) (m : ℕ) :
    actualSmallRoughRho (orderedSixth n e q a omega N false) N cap w z L m -
      actualSmallRoughRho (orderedEighth r n e q a omega N false) N cap w z L m =
    actualSmallRoughRho (sixthPolicy n e q a N false) N cap w z L m -
      actualSmallRoughRho (policy (width r) n e q a N false) N cap w z L m := by
  apply attached_difference_of_raw
  intro d
  exact P4AOriginalR17EighthSignedTransport.coefficient_difference
    r n e q a omega he hcut hh N hN cap w z d

/-- The same literal equality with every occurrence's original test
weight, on any one full-modulus carrier. In particular one may choose the
physical Q and its discrepancy test without reselecting beta. -/
theorem r17_attached_weighted_difference
    (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (he : 0 ≤ e) (hcut : omega ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (cap : ℕ) (w z L : ℝ)
    (Q : Finset ℕ) (G : ℕ → ℝ) :
    (∑ m ∈ Q, (actualSmallRoughRho (orderedSixth n e q a omega N false) N cap w z L m -
      actualSmallRoughRho (orderedEighth r n e q a omega N false) N cap w z L m) * G m) =
    ∑ m ∈ Q, (actualSmallRoughRho (sixthPolicy n e q a N false) N cap w z L m -
      actualSmallRoughRho (policy (width r) n e q a N false) N cap w z L m) * G m := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [r17_attached_coefficient_difference r n e q a omega he hcut hh N hN cap w z L m]

/-- Instantiate the very Q, cutoff and one beta scale of the existing
physical envelope. This binds the raw attached change on that carrier;
the compiled rho itself is a distinct coefficient. -/
theorem r17_envelope_carrier_attached_difference
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (G : ℕ → ℝ) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let Q := P4AOriginalFull87CompiledCounting.moduli N w
    (∑ m ∈ Q, (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L m -
      actualSmallRoughRho (orderedEighth r n e q a omega N false) N N w z L m) * G m) =
    ∑ m ∈ Q, (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L m -
      actualSmallRoughRho (policy (width r) n e q a N false) N N w z L m) * G m := by
  exact r17_attached_weighted_difference r n e q a (nu * beta ^ 2) he hcut hh N hN N
    ((N : ℝ) ^ (nu * beta ^ 2)) (P4AOriginalFull87RawChronology.cutoff N)
    ((N : ℝ) ^ (nu * beta))
    (P4AOriginalFull87CompiledCounting.moduli N ((N : ℝ) ^ (nu * beta ^ 2))) G

end
end ImbalancedChen.P2Saving16AttachedSignedTransport
