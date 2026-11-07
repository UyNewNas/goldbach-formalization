import ImbalancedChen.ActualThirdOriginalP4ASymmetricTentPrerequisites

/- SOURCEONLY / UNCOMPILED. Independent peer algebra for the proposed paired
plane rescue. This only compares original operation objects; it does not
claim the complete saved-leaf integral theorem. -/
namespace ImbalancedChen.P0SymmetricPairedOperationPeer
noncomputable section
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdRoundedNewSourceOnly OriginalThirdPositiveLogSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly

/-- Interval addition has no rescaling/rounding; swapping the two summands
after the same initial constant is bitwise equality of both integer fields. -/
theorem add_interchange (x y z : IV) : add (add x y) z = add (add x z) y := by
  cases x
  cases y
  cases z
  unfold add
  congr 1 <;> omega

theorem symmetric_ex_bitwise (a b c d : ℝ) :
    ordinaryEx (symmetricLeft a c) (symmetricRight b d) 0 =
      ordinaryEx (symmetricLeft a c) (symmetricRight b d) 1 := by
  rfl

/-- The exact original interval tree for OLD, with exchanged x/y scalar
coefficients. The already rounded products are exchanged as whole objects. -/
theorem original_interval_tree_pair
    (constant xCoeff yCoeff zCoeff invz : ℝ) (ex : IV) :
    add (mul (add (add (ofReal constant) (mul ex (ofReal xCoeff)))
      (mul ex (ofReal yCoeff))) (ofReal invz)) (ofReal zCoeff) =
    add (mul (add (add (ofReal constant) (mul ex (ofReal yCoeff)))
      (mul ex (ofReal xCoeff))) (ofReal invz)) (ofReal zCoeff) := by
  rw [add_interchange]

/-- All real producer square means are identical under the xz/yz pairing. -/
theorem producer_mean_xz_eq_yz (a b c d : ℝ) (side : TentSide) :
    tentOldMean .xz side (symmetricLeft a c) (symmetricRight b d) =
      tentOldMean .yz side (symmetricLeft a c) (symmetricRight b d) := by
  cases side <;>
    simp only [tentOldMean, oldX, oldY, oldZ, planeSlope, sumX, sumY, sumZ,
      symmetricLeft, symmetricRight, boxEX, boxEY, boxEZInv,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- Actual rational endpoint operands coincide before any factor lookup. -/
theorem endpoint_xz_eq_yz (x z D : ℤ) (side : TentSide) :
    literalTentEndpoint .xz side ![x,x,z] D =
      literalTentEndpoint .yz side ![x,x,z] D := by
  cases side <;>
    simp only [literalTentEndpoint, literalTentX, literalTentY, literalTentZ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> push_cast <;> ring

/-- Independent algebra for the stronger rescue: the two TRUE ordered means
average to the source square mean. No query-order condition is involved. -/
theorem producer_mean_is_ordered_pair_average (a b c d : ℝ) (side : TentSide) :
    tentOldMean .xz side (symmetricLeft a c) (symmetricRight b d) =
      (orderedTentMean .xz side a b c d + orderedTentMean .yz side a b c d) / 2 := by
  cases side <;>
    simp only [orderedTentMean, tentOldMean, oldX, oldY, oldZ, planeSlope,
      sumX, sumY, sumZ, symmetricLeft, symmetricRight, boxEX, boxEY, boxEZInv,
      minMean, sumMean, invZMean,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- Any two valid ordered-chord lower bounds may be averaged, including
negative endpoint-query slopes. It is unnecessary to order those queries. -/
theorem average_of_two_lower_bounds {x y integral : ℝ}
    (hx : x ≤ integral) (hy : y ≤ integral) : (x+y)/2 ≤ integral := by
  linarith only [hx, hy]
/-- Exact scalar chord identity, valid even with a negative query slope or
Lean's total division at a zero denominator. Actual span positivity is paid
separately by the original geometric API. -/
theorem affine_chord_at_average (low high flo fhi m₁ m₂ : ℝ) :
    flo + ((m₁+m₂)/2-low)/(high-low)*(fhi-flo) =
      ((flo+(m₁-low)/(high-low)*(fhi-flo))+
        (flo+(m₂-low)/(high-low)*(fhi-flo)))/2 := by
  ring
end
end ImbalancedChen.P0SymmetricPairedOperationPeer




