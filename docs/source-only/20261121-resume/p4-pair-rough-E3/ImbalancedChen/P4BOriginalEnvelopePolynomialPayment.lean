import ImbalancedChen.P4BOriginalRoughPairFinite
import ImbalancedChen.P4BOriginalSquarefreeP2

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

def p2Price (F G : 𝓢(ℝ,ℂ)) : ℝ := internalP2Constant*N2 (F:ℝ→ℂ)*N2 (G:ℝ→ℂ)

theorem p2Price_nonneg (F G : 𝓢(ℝ,ℂ)) : 0≤p2Price F G :=
  mul_nonneg (mul_nonneg internalP2Constant_pos.le (N2_nonneg _)) (N2_nonneg _)

theorem polynomial_expansion (F G : ℝ→ℂ)
    (hF : Function.support F⊆Icc (1/2:ℝ) (5/2)) (hG : Function.support G⊆Icc (1/2:ℝ) (5/2))
    {U V Z : ℝ} (hU : 0<U) (hV : 0<V) (hZ : 1≤Z)
    (j : ℕ) (g1 g2 : Bool) (short N q : ℕ) (alpha : ℂ) :
    polyDelta F G U V Z j g1 g2 short N q alpha=
      ∑ d∈(brunSupport Z (2*j+1))×ˢ(brunSupport Z (2*j+1)),
        brunPairCoefficient Z j g1 g2 d *
          fixedMCore (wideWindow (U/d.1)) (wideWindow (V/d.2)) (short*d.1*d.2) N q alpha F G (U/d.1) (V/d.2) := by
  let I := wideWindow U ×ˢ wideWindow V
  let R := brunSupport Z (2*j+1) ×ˢ brunSupport Z (2*j+1)
  calc
    _=∑ p∈I,∑ d∈R,brunPairCoefficient Z j g1 g2 d*
        (alpha*F ((p.1:ℝ)/U)*G ((p.2:ℝ)/V)*divisorIndicator d.1 p.1*divisorIndicator d.2 p.2*
          MellinInsertion20261028.residueKernel q N (short*p.1*p.2)) := by
      unfold polyDelta
      simp_rw [polynomial_pair]
      simp only [I,R,Finset.sum_product,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      ring
    _=∑ d∈R,brunPairCoefficient Z j g1 g2 d*
        ∑ p∈I,alpha*F ((p.1:ℝ)/U)*G ((p.2:ℝ)/V)*divisorIndicator d.1 p.1*divisorIndicator d.2 p.2*
          MellinInsertion20261028.residueKernel q N (short*p.1*p.2) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _=_ := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      obtain ⟨hd1,hd2⟩ := Finset.mem_product.mp hd
      rw [I,Finset.sum_product,pair_divisor_substitution hU hV
        (brunSupport_bounds hZ _ hd1).1 (brunSupport_bounds hZ _ hd2).1 F G hF hG alpha short,
        ←fixedMCore_eq_kernel]

theorem polynomial_P2 (F G : 𝓢(ℝ,ℂ))
    (hF : Function.support (F:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    (hG : Function.support (G:ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U V Z : ℝ} (hU : 0<U) (hV : 0<V) (hZ : 1≤Z)
    (j : ℕ) (g1 g2 : Bool) (short N q : ℕ) (hq : 0<q) (hsq : Squarefree q)
    (hN : N.Coprime q) (alpha : ℂ) :
    ‖polyDelta F G U V Z j g1 g2 short N q alpha‖≤
      p2Price F G*((Z^(2*j+1))^2*‖alpha‖)*modulusBudget q := by
  rw [polynomial_expansion F G hF hG hU hV hZ]
  let R := brunSupport Z (2*j+1) ×ˢ brunSupport Z (2*j+1)
  have H (d : ℕ×ℕ) (hd : d∈R) :
      ‖fixedMCore (wideWindow (U/d.1)) (wideWindow (V/d.2)) (short*d.1*d.2) N q alpha F G (U/d.1) (V/d.2)‖≤
        p2Price F G*‖alpha‖*modulusBudget q := by
    have h1 : (0:ℝ)<d.1 := by exact_mod_cast (brunSupport_bounds hZ _ (Finset.mem_product.mp hd).1).1
    have h2 : (0:ℝ)<d.2 := by exact_mod_cast (brunSupport_bounds hZ _ (Finset.mem_product.mp hd).2).1
    have hp := P4BOriginalSquarefreeP2.naturalCore_P2 hsq F G hF hG
      (div_pos hU h1) (div_pos hV h2) (short*d.1*d.2) N hq hN alpha
    simpa only [p2Price,mul_assoc,mul_left_comm,mul_comm] using hp
  calc
    _≤∑ d∈R,‖brunPairCoefficient Z j g1 g2 d‖*(p2Price F G*‖alpha‖*modulusBudget q) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (H d hd) (norm_nonneg _)
    _=(p2Price F G*modulusBudget q)*∑ d∈R,‖brunPairCoefficient Z j g1 g2 d‖*‖alpha‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _≤(p2Price F G*modulusBudget q)*((Z^(2*j+1))^2*‖alpha‖) :=
      mul_le_mul_of_nonneg_left (brunPair_mass hZ j g1 g2 alpha)
        (mul_nonneg (p2Price_nonneg F G) (modulusBudget_nonneg q))
    _=_ := by ring

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
