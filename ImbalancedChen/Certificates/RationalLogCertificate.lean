import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-!
Verification status: uncompiled candidate. See `docs/part2/HANDOFF.md`.

# Kernel-checked rational enclosures of the actual real logarithm

The numerical producer may suggest a certificate, but acceptance consists
of rational inequalities checked by Lean. Soundness uses the existing
Mathlib odd-series bounds, including their stated (unsharpened) remainder.
There is no floating-point evaluation, native decision oracle, or stored
real logarithm in the mathematical definitions.
-/

namespace ImbalancedChen.Certificates

open scoped BigOperators

/-- The rational argument of the odd logarithmic series. -/
def logParameter (q : ℚ) : ℚ := (q - 1) / (q + 1)

/-- A finite rational lower bound suggested by the logarithmic series. -/
def logSeriesLower (q : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n,
    logParameter q ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)

/-- The exact Mathlib remainder, rather than a sharper external tail. -/
def logSeriesUpper (q : ℚ) (n : ℕ) : ℚ :=
  logSeriesLower q n +
    2 * logParameter q ^ (2 * n + 1) / (1 - logParameter q ^ 2)

/-- A fully rational proof obligation for one logarithm. -/
structure RationalLogCertificate where
  argument : ℚ
  terms : ℕ
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def RationalLogCertificate.Valid (c : RationalLogCertificate) : Prop :=
  1 ≤ c.argument ∧
    c.lower ≤ logSeriesLower c.argument c.terms ∧
    logSeriesUpper c.argument c.terms ≤ c.upper

instance (c : RationalLogCertificate) : Decidable c.Valid := by
  unfold RationalLogCertificate.Valid
  infer_instance

/-- An executable finite check; its correctness is proved below. -/
def RationalLogCertificate.check (c : RationalLogCertificate) : Bool :=
  decide c.Valid

private theorem logParameter_bounds {q : ℚ} (hq : 1 ≤ q) :
    0 ≤ logParameter q ∧ logParameter q < 1 := by
  have hden : 0 < q + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hq) hden.le
  · change (q - 1) / (q + 1) < 1
    exact (div_lt_one hden).mpr (by linarith)

private theorem logParameter_identity {q : ℚ} (hq : 1 ≤ q) :
    (1 + logParameter q) / (1 - logParameter q) = q := by
  have hden : q + 1 ≠ 0 := ne_of_gt (by linarith : 0 < q + 1)
  unfold logParameter
  field_simp [hden]
  ring

/-- The finite checks enclose `Real.log` of the supplied rational argument.
The certificate's two stored endpoints are not themselves a semantic
assumption about the logarithm. -/
theorem RationalLogCertificate.check_sound (c : RationalLogCertificate)
    (hcheck : c.check = true) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
      Real.log (c.argument : ℝ) ≤ (c.upper : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hcheck
  rcases hv with ⟨hq, hlo, hhi⟩
  obtain ⟨hx0, hx1⟩ := logParameter_bounds hq
  have hx0R : (0 : ℝ) ≤ (logParameter c.argument : ℝ) := by exact_mod_cast hx0
  have hx1R : (logParameter c.argument : ℝ) < (1 : ℝ) := by exact_mod_cast hx1
  have heq : (1 + (logParameter c.argument : ℝ)) /
      (1 - (logParameter c.argument : ℝ)) = (c.argument : ℝ) := by
    exact_mod_cast logParameter_identity hq
  have hl := Real.sum_range_le_log_div hx0R hx1R c.terms
  have hu := Real.log_div_le_sum_range_add hx0R hx1R c.terms
  rw [heq] at hl hu
  have hlCast : (logSeriesLower c.argument c.terms : ℝ) =
      2 * ∑ i ∈ Finset.range c.terms,
        (logParameter c.argument : ℝ) ^ (2 * i + 1) /
          (2 * (i : ℝ) + 1) := by
    simp [logSeriesLower]
  have huCast : (logSeriesUpper c.argument c.terms : ℝ) =
      (logSeriesLower c.argument c.terms : ℝ) +
        2 * (logParameter c.argument : ℝ) ^ (2 * c.terms + 1) /
          (1 - (logParameter c.argument : ℝ) ^ 2) := by
    simp [logSeriesUpper]
  have hloR : (c.lower : ℝ) ≤ (logSeriesLower c.argument c.terms : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (logSeriesUpper c.argument c.terms : ℝ) ≤ (c.upper : ℝ) := by
    exact_mod_cast hhi
  rw [hlCast] at hloR
  rw [huCast, hlCast] at hhiR
  simp only [mul_div_assoc] at hhiR
  constructor <;> linarith

end ImbalancedChen.Certificates
