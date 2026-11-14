import ImbalancedChen.Part3OriginalSwitchedSeparatedNativeSlots
import ImbalancedChen.Part3OriginalSwitchedMaassExchange

/-! A fixed absolutely summable Fourier majorant times the genuine
same-infinity cubic spectral and continuous measures at two marks. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRegularFourierBudget20261113
noncomputable section
open Finset MeasureTheory Complex
open scoped BigOperators Classical
open OriginalSwitchedSeparatedTransforms20261113 (factor factor_norm principal)
open OriginalSwitchedUniformRegularTransform20261113 (mode_uniform)
open OriginalSwitchedFourCoordinateSymbol20261113 (coefficient lattice_budget)
open OriginalSwitchedSchwartzPrices20261113 (weight)
open ActualMarkedCubicPrice20261112 (linePrice linePrice_pos)
open ActualPrescribedPositiveJ20261112 (positiveWeight)
open OriginalSwitchedCutoffModes20261113 (mode)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open private price_div from ImbalancedChen.Part3OriginalMarkedPacketLimits

def scaled (Φ : ℝ→ℂ) (t : ℝ) := positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ)

def term (d : ℕ+) (j : ℕ) (Y Q : ℝ) (m n : ℕ) (k : D4→ℤ) (t : ℝ) :=
  factor j Y Q d k m n*scaled (spectralTest (mode (k 0)) Y⁻¹) t

theorem tested (d : ℕ+) {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (t : ℝ) :
    HasSum (fun k => term d j Y Q m n k t) (scaled (switchedTest Y ((d.val:ℝ)*Q) m n) t) := by
  exact ((principal hm hn yp qp d t).div_const (Real.cosh (Real.pi*t):ℂ)).congr_fun
    (fun k => by dsimp only [term,scaled];ring)

theorem uniform_majorant :
    ∃ A : (D4→ℤ)→ℝ,(∀ k,0≤A k) ∧ Summable A ∧
      ∀ (Y : ℝ),1≤Y → ∀ (d : ℕ+) (j m n : ℕ) (Q : ℝ) (k : D4→ℤ) (t : ℝ),
      ‖term d j Y Q m n k t‖≤(A k*(1+Real.log (2*Y)^2))*linePrice t := by
  obtain ⟨r,C,cp,H⟩ := mode_uniform
  obtain ⟨_,_,ss,_⟩ := lattice_budget r
  let g := fun k : D4→ℤ => ‖coefficient k‖*(1+|(k 0:ℝ)|)^r
  refine ⟨fun k => C*g k,fun k => mul_nonneg cp (by dsimp only [g];positivity),ss.mul_left C,
    fun Y y1 d j m n Q k t => ?_⟩
  let p := 1+Real.log (2*Y)^2
  let w := (weight (k 0))^r
  let V := spectralTest (mode (k 0)) Y⁻¹
  have price : ‖scaled V t‖≤(C*p*w)*linePrice t := by
    apply price_div
    have ch := Real.cosh_pos (Real.pi*t)
    simp only [scaled,norm_div,Complex.norm_real,Real.norm_of_nonneg ch.le]
    rw [show (1+|t|)^3*Real.cosh (Real.pi*t)*(‖positiveWeight V t‖/Real.cosh (Real.pi*t))=
      (1+|t|)^3*‖positiveWeight V t‖ by field_simp [ch.ne']]
    exact H (k 0) Y y1 t
  rw [term,norm_mul]
  exact (mul_le_mul (factor_norm j Y Q d k m n) price (norm_nonneg _) (norm_nonneg _)).trans_eq
    (by dsimp only [g,p,w,weight];ring)

end
end ImbalancedChen.Part3.OriginalSwitchedRegularFourierBudget20261113
