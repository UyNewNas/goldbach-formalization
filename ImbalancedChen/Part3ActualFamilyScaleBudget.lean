import ImbalancedChen.Part3ActualLabelBudgetCardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Original physical scales in the actual per-mode hard-tail budget

The original geometry and physical scale definitions are identified in the
accompanying source provenance. The polynomial bound applies to every natural
feature index, including zero. Positivity of the physical scales is supplied
separately for the positive indices. This calculation concerns a single mode.
-/

noncomputable section

namespace ImbalancedChen.Part3

namespace ActualPositiveLatticeSmoothCoverSourceOnly

def scaleB (e : MediumAtom) (delta l : ℕ) : ℝ := (l : ℝ)*e.U*e.Q3/delta

def scaleC (e : MediumAtom) (D g l : ℕ) : ℝ := e.U*e.Q3*e.Q2/((g : ℝ)*l*D)

end ActualPositiveLatticeSmoothCoverSourceOnly

namespace TransposedPrimitiveUPayment

theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ _ := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

theorem V_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : d.V ≤ d.scale := by
  change d.V ≤ d.U * d.V
  exact le_mul_of_one_le_left (by linarith [hd.2.1]) hd.1

end TransposedPrimitiveUPayment

namespace ActualFamilyScaleBudget20261127

open TransposedPrimitiveUPayment ActualPositiveLatticeSmoothCoverSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualCompletedHardTailMass20261026b
open ActualLabelBudgetCardinality20261127

theorem geometry_le_scale {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    d.U ≤ d.scale ∧ d.V ≤ d.scale ∧ d.Q1 ≤ d.scale ∧
      d.Q2 ≤ d.scale ∧ d.Q3 ≤ d.scale := by
  have hdKeep := hd
  obtain ⟨hU, hV, _hQ1, hQ2, hQ3, _, _, _, hg1, hg2, _⟩ := hdKeep
  have hX := one_le_scale hd
  have hUx : d.U ≤ d.scale := by unfold MediumAtom.scale; nlinarith
  have hVx : d.V ≤ d.scale := V_le_scale hd
  have hn : d.scale ^ (-sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hX (by linarith : -sigma ≤ 0)
  have hQ1x : d.Q1 ≤ d.scale := by
    calc
      _ ≤ d.U * d.scale ^ (-sigma) := hg1.le
      _ ≤ d.U * 1 := mul_le_mul_of_nonneg_left hn (by linarith)
      _ = d.U := mul_one _
      _ ≤ _ := hUx
  have hpow : d.scale ^ (1 - 8 * sigma) ≤ d.scale := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by linarith : 1 - 8 * sigma ≤ 1)
  have hU2 : 1 ≤ d.U ^ 2 := by nlinarith
  have hQ32 : 1 ≤ d.Q3 ^ 2 := by nlinarith
  have hprod : 1 ≤ d.U ^ 2 * d.Q3 ^ 2 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ d.U ^ 2 * d.Q3 ^ 2 := mul_le_mul hU2 hQ32 zero_le_one (sq_nonneg _)
  have hQ2x : d.Q2 ≤ d.scale := by
    calc
      _ = d.Q2 * 1 := by ring
      _ ≤ d.Q2 * (d.U ^ 2 * d.Q3 ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by linarith)
      _ = d.U ^ 2 * d.Q2 * d.Q3 ^ 2 := by ring
      _ ≤ d.scale ^ (1 - 8 * sigma) := hg2.le
      _ ≤ _ := hpow
  have hprod2 : 1 ≤ d.U ^ 2 * d.Q2 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ d.U ^ 2 * d.Q2 := mul_le_mul hU2 hQ2 zero_le_one (sq_nonneg _)
  have hQ3x : d.Q3 ≤ d.scale := by
    calc
      _ ≤ d.Q3 ^ 2 := by nlinarith
      _ = 1 * d.Q3 ^ 2 := by ring
      _ ≤ (d.U ^ 2 * d.Q2) * d.Q3 ^ 2 :=
        mul_le_mul_of_nonneg_right hprod2 (sq_nonneg _)
      _ ≤ d.scale ^ (1 - 8 * sigma) := hg2.le
      _ ≤ _ := hpow
  exact ⟨hUx, hVx, hQ1x, hQ2x, hQ3x⟩

variable {b : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}

theorem scaleB_pos (he : MediumAdmissible b sigma kappa c0 e)
    {delta l : ℕ} (hl : 0 < l) (hdelta : 0 < delta) : 0 < scaleB e delta l := by
  have hU := zero_lt_one.trans_le he.1
  have hQ3 := zero_lt_one.trans_le he.2.2.2.2.1
  unfold scaleB
  positivity

theorem scaleC_pos (he : MediumAdmissible b sigma kappa c0 e)
    {D g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l) : 0 < scaleC e D g l := by
  have hU := zero_lt_one.trans_le he.1
  have hQ2 := zero_lt_one.trans_le he.2.2.2.1
  have hQ3 := zero_lt_one.trans_le he.2.2.2.2.1
  unfold scaleC
  positivity

private theorem one_le_cast_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (1 : ℝ) ≤ n := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

theorem actual_scaleF_le (he : MediumAdmissible b sigma kappa c0 e)
    (hsigma : 0 < sigma) (D g : ℕ) : scaleF e D g ≤ e.scale := by
  have hx : 0 ≤ e.scale := zero_le_one.trans (one_le_scale he)
  by_cases hg : g = 0
  · simp [scaleF, hg, hx]
  by_cases hD : D = 0
  · simp [scaleF, hD, hx]
  apply le_trans _ (geometry_le_scale he hsigma).1
  apply div_le_self (zero_le_one.trans he.1)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_cast_of_ne_zero hg) he.2.2.1)
    (one_le_cast_of_ne_zero hD)

theorem actual_scaleC_le (he : MediumAdmissible b sigma kappa c0 e)
    (hsigma : 0 < sigma) (D g l : ℕ) : scaleC e D g l ≤ e.scale ^ 3 := by
  have hU := zero_le_one.trans he.1
  have hQ2 := zero_le_one.trans he.2.2.2.1
  have hQ3 := zero_le_one.trans he.2.2.2.2.1
  have hx := zero_le_one.trans (one_le_scale he)
  have hgeom := geometry_le_scale he hsigma
  have hnum : e.U * e.Q3 * e.Q2 ≤ e.scale * e.scale * e.scale :=
    mul_le_mul (mul_le_mul hgeom.1 hgeom.2.2.2.2 hQ3 hx) hgeom.2.2.2.1 hQ2
      (mul_nonneg hx hx)
  have hden : (1 : ℝ) ≤ (g * l * D : ℕ) ∨ g * l * D = 0 := by
    by_cases h : g * l * D = 0
    · exact Or.inr h
    · exact Or.inl (one_le_cast_of_ne_zero h)
  unfold scaleC
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  rcases hden with h | h
  · exact (div_le_self (mul_nonneg (mul_nonneg hU hQ3) hQ2) h).trans
      (by simpa [pow_succ] using hnum)
  · simp [h, pow_nonneg hx]

theorem actual_sharedSmoothFrequencyBound_le (he : MediumAdmissible b sigma kappa c0 e)
    (hsigma : 0 < sigma) (D : ℕ) (Z : ℝ) (hZ : 1 ≤ Z) :
    (e.sharedSmoothFrequencyBound Z D : ℝ) ≤ 65 * Z * e.scale ^ 5 := by
  have hx := one_le_scale he
  have hx0 := zero_le_one.trans hx
  have hZ0 := zero_le_one.trans hZ
  have hQ1 := zero_le_one.trans he.2.2.1
  have hQ2 := zero_le_one.trans he.2.2.2.1
  have hQ3 := zero_le_one.trans he.2.2.2.2.1
  have hV := zero_le_one.trans he.2.1
  have hgeom := geometry_le_scale he hsigma
  have h1 := hgeom.2.2.1
  have h2 := hgeom.2.2.2.1
  have h3 := hgeom.2.2.2.2
  let N := 64 * Z * e.Q1 * e.Q3 ^ 2 * e.Q2 ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hNle : N ≤ 64 * Z * e.scale ^ 5 := by
    calc
      N ≤ 64 * Z * e.scale * e.scale ^ 2 * e.scale ^ 2 := by
        have h64 : 0 ≤ 64 * Z := by positivity
        have hfirst := mul_le_mul_of_nonneg_left h1 h64
        have hsecond := mul_le_mul hfirst (pow_le_pow_left₀ hQ3 h3 2)
          (sq_nonneg _) (mul_nonneg h64 hx0)
        exact mul_le_mul hsecond (pow_le_pow_left₀ hQ2 h2 2) (sq_nonneg _)
          (mul_nonneg (mul_nonneg h64 hx0) (sq_nonneg _))
      _ = _ := by ring
  have hdiv : N / ((D : ℝ) * e.V) ≤ N := by
    by_cases hD : D = 0
    · simp [hD, hN]
    · exact div_le_self hN (one_le_mul_of_one_le_of_one_le
        (one_le_cast_of_ne_zero hD) he.2.1)
  have hzpow : 1 ≤ Z * e.scale ^ 5 :=
    one_le_mul_of_one_le_of_one_le hZ (one_le_pow₀ hx)
  change (Nat.ceil (N / ((D : ℝ) * e.V)) : ℝ) ≤ _
  have hceil := (Nat.ceil_lt_add_one (div_nonneg hN (mul_nonneg (Nat.cast_nonneg D) hV))).le
  nlinarith only [hceil, hdiv, hNle, hzpow]

theorem actual_scaleC_sq_rawLabelBudget_le (he : MediumAdmissible b sigma kappa c0 e)
    (hsigma : 0 < sigma) (D delta g l : ℕ) (eta : ℝ) (heta : 0 < eta) :
    scaleC e D g l ^ 2 *
        rawLabelBudget (baseCarrier e (D / delta))
          (e.sharedSmoothFrequencyBound (e.scale ^ eta) D) (scaleF e D g) ≤
      202800 * e.scale ^ (19 + 2 * eta) := by
  let x := e.scale
  let Z := x ^ eta
  let H := e.sharedSmoothFrequencyBound Z D
  have hx : 1 ≤ x := one_le_scale he
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hZ : 1 ≤ Z := Real.one_le_rpow hx heta.le
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hQ := he.2.2.2.1
  have hF := actual_scaleF_le he hsigma D g
  have hQx : e.Q2 ≤ x := (geometry_le_scale he hsigma).2.2.2.1
  have hHx : (H : ℝ) ≤ 65 * Z * x ^ 5 := actual_sharedSmoothFrequencyBound_le he hsigma D Z hZ
  have hf3 : 2 * scaleF e D g + 1 ≤ 3 * x := by change scaleF e D g ≤ x at hF; linarith
  have hq2 : e.Q2 + 1 ≤ 2 * x := by linarith
  have hh2 : 2 * (H : ℝ) ≤ 130 * Z * x ^ 5 := by linarith
  have hpair : (e.Q2 + 1) * (2 * (H : ℝ)) ≤ (2 * x) * (130 * Z * x ^ 5) :=
    mul_le_mul hq2 hh2 (by positivity) (by positivity)
  have hpair0 : 0 ≤ (e.Q2 + 1) * (2 * (H : ℝ)) :=
    mul_nonneg (by linarith) (by positivity)
  have hraw := (actual_rawLabelBudget_le he D delta g Z).trans
    (mul_le_mul hf3 (pow_le_pow_left₀ hpair0 hpair 2) (sq_nonneg _) (by positivity))
  have hc := actual_scaleC_le he hsigma D g l
  have hc0 : 0 ≤ scaleC e D g l := by
    have hU := zero_le_one.trans he.1
    have hQ3 := zero_le_one.trans he.2.2.2.2.1
    have hQ2 := zero_le_one.trans hQ
    unfold scaleC
    positivity
  have hcsq : scaleC e D g l ^ 2 ≤ (x ^ 3) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  calc
    _ ≤ scaleC e D g l ^ 2 * ((3 * x) * ((2 * x) * (130 * Z * x ^ 5)) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
    _ ≤ (x ^ 3) ^ 2 * ((3 * x) * ((2 * x) * (130 * Z * x ^ 5)) ^ 2) :=
      mul_le_mul_of_nonneg_right hcsq (by positivity)
    _ = 202800 * x ^ 19 * Z ^ 2 := by ring
    _ = _ := by
      change 202800 * x ^ 19 * (x ^ eta) ^ 2 = 202800 * x ^ (19 + 2 * eta)
      rw [show (19 + 2 * eta : ℝ) = 19 + (eta + eta) by ring,
        Real.rpow_add hxpos, Real.rpow_add hxpos eta eta, Real.rpow_ofNat]
      ring

end ActualFamilyScaleBudget20261127

end ImbalancedChen.Part3

end
