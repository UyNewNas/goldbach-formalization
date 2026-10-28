import ImbalancedChen.Part3ActualHighConductorLogMargin
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The low-conductor SW exponent and natural conductor cutoff are chosen
from the requested logarithmic saving before the varying actual atom.
-/

namespace ImbalancedChen.Part3.ActualLowConductorLogChoiceSourceOnly

noncomputable section
open Classical
open scoped BigOperators
open ActualFilteredPrimitiveSWSourceOnly
open ActualLowConductorQuotientSumSourceOnly
open ActualHighConductorFixedQuotientSourceOnly
open ActualHighConductorLogMarginSourceOnly

/-- One cutoff exponent fixed before all actual coefficients and moduli. -/
def cutoffExponent (A : ℝ) : ℕ := Nat.ceil (A+3)

theorem cutoffExponent_ge (A : ℝ) : A+3 ≤ (cutoffExponent A : ℝ) := Nat.le_ceil _

/-- Low conductors with the actual natural cutoff have arbitrary log saving.
The explicit fixed divisor moment exponent is selected before Bsw. -/
theorem uniformAuxiliarySW_lowEnergy_log_choice
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → 2 ≤ Real.log (F i).scale →
        ∀ Q r : ℕ, 1 ≤ Q → 1 ≤ r → (Q : ℝ) ≤ (F i).scale →
          lowEnergy (F i) Q (logCutoff (Real.log (F i).scale) (cutoffExponent A)) r ≤
            C^2*(2 : ℝ)^(2*(2^(2*C0)))*(F i).U^2*tau r^(2*C0) /
              (Real.log (F i).scale)^A := by
  let b := cutoffExponent A
  let E : ℕ := 2*(2^(2*C0))
  let D : ℕ := b+1+E
  let ASW : ℝ := (A+(D : ℝ))/2
  have hASW : 0 < ASW := by dsimp only [ASW]; positivity
  have hL : 0 ≤ ((b+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨C,hC,x0,hx0,hbound⟩ :=
    uniformAuxiliarySW_lowEnergy F B C0 sigma kappa c0 hadmissible hSW
      ASW ((b+1 : ℕ) : ℝ) hASW hL
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx ht Q r hQ hr hQX
  let t := Real.log (F i).scale
  let R := logCutoff t b
  have htpos : 0 < t := by dsimp only [t]; linarith
  obtain ⟨hR,hRlo,hRhi⟩ := logCutoff_bounds ht b
  have hRlog : (R : ℝ) ≤ t^((b+1 : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast] using hRhi
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : Real.log (Q : ℝ) ≤ t := Real.log_le_log hQpos hQX
  have ha : 0 ≤ 1+Real.log (Q : ℝ) := by
    have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith [Real.log_nonneg hq]
  have hU : 0 ≤ (F i).U := by linarith [(hadmissible i).1]
  have hc : 0 ≤ (C*(F i).U/t^ASW)^2*tau r^(2*C0) := by
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (tau_nonneg r) _)
  have hden : (t^ASW)^2 = t^A*(t^(b+1)*t^E) := by
    rw [pow_two,← Real.rpow_add htpos ASW ASW]
    have heq : ASW+ASW = A+(D : ℝ) := by dsimp only [ASW]; ring
    rw [heq,Real.rpow_add htpos A (D : ℝ),Real.rpow_natCast]
    dsimp only [D]
    rw [pow_add]
  have hid : (C*(F i).U/t^ASW)^2*tau r^(2*C0)*t^(b+1)*(2*t)^E =
      C^2*(2 : ℝ)^E*(F i).U^2*tau r^(2*C0)/t^A := by
    rw [div_pow,hden,mul_pow]
    field_simp [(Real.rpow_pos_of_pos htpos A).ne',pow_ne_zero (b+1) htpos.ne',
      pow_ne_zero E htpos.ne']
    <;> ring
  refine (hbound i hx Q R r hQ hr hRlog).trans ?_
  change (C*(F i).U/t^ASW)^2*tau r^(2*C0)*(R : ℝ)*(1+Real.log (Q : ℝ))^E ≤ _
  calc
    _ ≤ (C*(F i).U/t^ASW)^2*tau r^(2*C0)*t^(b+1)*(2*t)^E := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hRhi hc
      · exact pow_le_pow_left₀ ha (by dsimp only [t] at *; linarith) E
      · exact pow_nonneg ha E
      · exact mul_nonneg hc (pow_nonneg htpos.le _)
    _ = _ := hid

/-- The actual prefix length dominates U; this binds both low/high norms
to the same original positive alpha support. -/
theorem U_le_actual_prefix {d : MediumAtom} (hU : 1 ≤ d.U) :
    d.U ≤ (Nat.floor (2*d.U) : ℝ) := by
  have h := Nat.lt_floor_add_one (2*d.U)
  linarith

/-- A positive auxiliary integer has at least the divisor 1. -/
theorem one_le_tau {r : ℕ} (hr : 1 ≤ r) : (1 : ℝ) ≤ tau r := by
  have hmem : 1 ∈ r.divisors := Nat.mem_divisors.mpr ⟨one_dvd r,by omega⟩
  have hc : 1 ≤ r.divisors.card := Finset.card_pos.mpr ⟨1,hmem⟩
  exact_mod_cast hc

end
end ImbalancedChen.Part3.ActualLowConductorLogChoiceSourceOnly
