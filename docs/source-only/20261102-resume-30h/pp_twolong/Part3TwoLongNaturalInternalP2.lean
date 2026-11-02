import Mathlib
import ImbalancedChen.Part3TwoLongInternalP2Modes
import ImbalancedChen.Part3TwoLongActualThreeBrunP2Receiver

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The P1 Fourier sum is paid at its actual natural fixedMCore source.
The UV/q^2 factor cancels the two divisor-frequency scales q/U,q/V.
The original nonprimitive short-product branch is exactly zero, as is q=1.
The conclusion is derived from CompositeWeilInput, not from FixedMP2.
The generic C2-only interface is deliberately not asserted: this theorem
covers actual compact smooth profiles via their Schwartz realization.
-/
namespace ImbalancedChen.Part3.TwoLongNaturalInternalP2
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongNaturalPeriodization
open ImbalancedChen.Part3.TwoLongNaturalP1
open ImbalancedChen.Part3.TwoLongP1AxisCancellation
open ImbalancedChen.Part3.TwoLongInternalP2FrequencySums
open ImbalancedChen.Part3.TwoLongN2FourierDecay
open ImbalancedChen.Part3.TwoLongInternalP2Modes
open ImbalancedChen.Part3.TwoLongActualThreeBrunP2Receiver
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

theorem compact_of_window (F : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2)) :
    HasCompactSupport (F : ℝ → ℂ) := by
  change IsCompact (closure (Function.support (F : ℝ → ℂ)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal hF isClosed_Icc)

/-- Refined original fixed-m P2, before combining its two separate
arithmetic constants. No size condition on a or relation among U,V,q. -/
theorem naturalCore_P2_refined (hWeil : CompositeWeilInput)
    (F G : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (m a q : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) (alpha : ℂ) :
    ‖fixedMCore (wideWindow U) (wideWindow V) m a q alpha F G U V‖ ≤
      4*fourierDecayConstant^2*‖alpha‖*N2 (F : ℝ → ℂ)*N2 (G : ℝ → ℂ)*
        ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
          (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hFN := N2_nonneg (F : ℝ → ℂ)
  have hGN := N2_nonneg (G : ℝ → ℂ)
  have hW := weilConstant_nonneg
  by_cases hm : Nat.Coprime m q
  · have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hphi : (Nat.totient q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    have haU : IsUnit ((a : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast,ZMod.isUnit_iff_coprime] using ha
    have hmU : IsUnit ((m : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast,ZMod.isUnit_iff_coprime] using hm
    have hb := actual_center_unit (a : ℤ) (m : ℤ) haU hmU
    have hs := centeredMode_tsum_le hWeil F G hU hV hq
      ((a : ℤ)*inverseResidue q (m : ℤ)) hb
    rw [naturalCore_P1 F G (compact_of_window F hF) (compact_of_window G hG)
      hF hG hU hV m a hm ha alpha]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (div_pos (mul_pos hU hV) (sq_pos_of_pos hqR))]
    change ‖alpha‖*(U*V/(q : ℝ)^2)*
      ‖∑' j : ℤ, ∑' k : ℤ,
        centeredMode F G U V q ((a : ℤ)*inverseResidue q (m : ℤ)) (j,k)‖ ≤ _
    calc
      _ ≤ ‖alpha‖*(U*V/(q : ℝ)^2)*
          (((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))*
          (4*((q : ℝ)/U)*((q : ℝ)/V)*
            ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
              (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ)))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp [hqR.ne',hU.ne',hV.ne',hphi]; ring
  · rw [naturalCore_zero_of_nonprimitive _ _ m a hm ha alpha F G U V,norm_zero]
    positivity

/-- A single fixed constant, independent of q,U,V,a,m,alpha and profiles. -/
def internalP2Constant : ℝ := 4*fourierDecayConstant^2*(weilConstant+1)

theorem internalP2Constant_pos : 0 < internalP2Constant := by
  have hF := fourierDecayConstant_pos
  have hW := weilConstant_nonneg
  unfold internalP2Constant
  positivity

theorem arithmetic_budget_le (q : ℕ) :
    (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
      (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ) ≤
        (weilConstant+1)*modulusBudget q := by
  have hX : 0 ≤ (q.divisors.card : ℝ)*Real.sqrt (q : ℝ) := by positivity
  have hY : 0 ≤ (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ) := by positivity
  have hW := weilConstant_nonneg
  unfold modulusBudget tau
  nlinarith [mul_nonneg hW hY]

/-- Original P2 for actual smooth supported profiles. The source is the
independently defined natural count minus its exact coprime mean. -/
theorem naturalCore_P2 (hWeil : CompositeWeilInput)
    (F G : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (m a q : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) (alpha : ℂ) :
    ‖fixedMCore (wideWindow U) (wideWindow V) m a q alpha F G U V‖ ≤
      internalP2Constant*‖alpha‖*N2 (F : ℝ → ℂ)*N2 (G : ℝ → ℂ)*modulusBudget q := by
  have hFN := N2_nonneg (F : ℝ → ℂ)
  have hGN := N2_nonneg (G : ℝ → ℂ)
  apply (naturalCore_P2_refined hWeil F G hF hG hU hV m a q hq ha alpha).trans
  calc
    _ ≤ (4*fourierDecayConstant^2*‖alpha‖*N2 (F : ℝ → ℂ)*N2 (G : ℝ → ℂ))*
        ((weilConstant+1)*modulusBudget q) :=
      mul_le_mul_of_nonneg_left (arithmetic_budget_le q) (by positivity)
    _ = _ := by unfold internalP2Constant; ring

/-- q=1 is included in the preceding theorem and is in fact identically
zero independently of Weil, primitive gates or regularity. -/
theorem naturalCore_q1 (I J : Finset ℕ) (m a : ℕ) (alpha : ℂ)
    (f g : ℝ → ℂ) (U V : ℝ) : fixedMCore I J m a 1 alpha f g U V = 0 :=
  fixedMCore_modulus_one I J m a alpha f g U V

end
end ImbalancedChen.Part3.TwoLongNaturalInternalP2
