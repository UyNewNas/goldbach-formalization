import ImbalancedChen.P4BOriginalRoughPairFinite
import ImbalancedChen.P4BOriginalSquarefreeP2
import ImbalancedChen.P1HistoricalTwoLongFiniteRoughData

/-! SOURCE ONLY / UNCOMPILED. The already-paid current-q squarefree P2
is applied to the actual smooth positive envelopes as well as the
complex long profiles. This handles both gap cross terms without a
global CompositeWeilInput or changing the physical modulus. -/
namespace ImbalancedChen.P4BOriginalEnvelopePolynomialPayment
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open PrimeProducts
open P4BOriginalRoughPairFinite (polyDelta)
open Part3.TwoLongLiteralMellinModes (N2 wideWindow)
open Part3.TwoLongFixedMRectangularCore (fixedMCore)
open Part3.TwoLongLiteralBrunSubstitution
open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds brunPairCoefficient brunPair_mass)
open Part3.TwoLongNaturalInternalP2 (internalP2Constant internalP2Constant_pos)
open Part3.TwoLongInternalP2Modes (N2_nonneg)
open Part3.TwoLongActualThreeBrunP2Receiver (modulusBudget modulusBudget_nonneg)
open P4BOriginalTwoLongExpandedCore (rho actual_modulus_class actual_modulus_moment)
open P4BOriginalFiniteSmoothCount (Q coefficient)

/-- Strong absolute-q sum, needed for the E3 comparison, on exactly
the current final Q/rho. The primary signed rho is not redefined. -/
theorem absolute_polynomial_sum (F G : 𝓢(ℝ,ℂ))
    (hF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    (hG : Function.support (G:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U V Z : ℝ} (hU : 0<U) (hV : 0<V) (hZ : 1≤Z)
    (j : ℕ) (g1 g2 : Bool) (Mset : Finset ℕ) (alpha : ℕ→ℂ)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (L : ℝ)
    (S : Finset ℕ) (hS : S⊆Q omega N)
    (hlevel : ∀ v∈S,coefficient m r n e q a omega k N L v≠0 → v≤D) :
    (∑ v∈S,‖rho m r n e q a omega k N L v‖*
      ∑ short∈Mset,‖polyDelta F G U V Z j g1 g2 short N v (alpha short)‖)≤
      p2Price F G*((Z^(2*j+1))^2*(∑ short∈Mset,‖alpha short‖))*
        (((D:ℝ)*Real.sqrt D+1)*(4*(1+Real.log (max 1 (D:ℝ))))^16) := by
  have H (v : ℕ) (hv : v∈S) :
      (∑ short∈Mset,‖polyDelta F G U V Z j g1 g2 short N v (alpha short)‖)≤
        p2Price F G*((Z^(2*j+1))^2*(∑ short∈Mset,‖alpha short‖))*modulusBudget v := by
    obtain ⟨hp,hcop,hsq,_⟩ := actual_modulus_class m r n e q a omega k N L (hS hv)
    apply (Finset.sum_le_sum (fun short hshort => polynomial_P2 F G hF hG hU hV hZ j g1 g2 short N v hp hsq hcop (alpha short))).trans_eq
    simp only [Finset.mul_sum,Finset.sum_mul]
  have hp0 : 0≤p2Price F G*((Z^(2*j+1))^2*(∑ short∈Mset,‖alpha short‖)) :=
    mul_nonneg (p2Price_nonneg F G) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  calc
    _≤∑ v∈S,‖rho m r n e q a omega k N L v‖*
        (p2Price F G*((Z^(2*j+1))^2*(∑ short∈Mset,‖alpha short‖))*modulusBudget v) :=
      Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (H v hv) (norm_nonneg _))
    _=(p2Price F G*((Z^(2*j+1))^2*(∑ short∈Mset,‖alpha short‖)))*
        ∑ v∈S,‖rho m r n e q a omega k N L v‖*modulusBudget v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _≤_ := mul_le_mul_of_nonneg_left (actual_modulus_moment m r n e q a omega k N D L S hS hlevel) hp0

end
end ImbalancedChen.P4BOriginalEnvelopePolynomialPayment
