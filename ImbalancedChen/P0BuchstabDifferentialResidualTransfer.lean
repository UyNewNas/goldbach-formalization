import ImbalancedChen.P0BuchstabStepErrorTransfer
import ImbalancedChen.P2BuchstabPolynomialStep

/-!
A primitive differential-residual bridge for the actual Buchstab renewal.
The weighted candidates use the existing exact rational polynomial eval and
its derivative. Below 2 they have the exact initial reciprocal; above 2 they
are P(u)/u. An anchor defect at 2 is allowed, so the candidates may jump.

FTC converts the finite polynomial derivative residual against the previous
candidate into a local additive renewal defect. The previously established
interval-integrable contraction then gives a depth-uniform actual-Buchstab
error bound. Only stages strictly before the requested finite depth occur in
the hypotheses. No error against Buchstab or table/bank soundness is assumed.

SOURCE_WRITTEN_UNCOMPILED; no compiler or numerical replay was run.
-/

namespace ImbalancedChen.P0BuchstabDifferentialResidualTransfer

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open P0BuchstabRenewalErrorPropagation P0BuchstabStepErrorTransfer
open Certificates.P2BuchstabPolynomialStep
open scoped Interval

/-- The actual initial reciprocal plus a polynomial correction after 2.
Its weighted right limit at the anchor is exactly eval P 2. -/
def polynomialCandidate (p : List ℚ) (u : ℝ) : ℝ :=
  1 / max 1 u + (Ioi (2 : ℝ)).indicator
    (fun v => (eval p v - 1) / max 1 v) u

theorem polynomialCandidate_below (p : List ℚ) {u : ℝ} (hu : u ≤ 2) :
    polynomialCandidate p u = 1 / max 1 u := by
  simp only [polynomialCandidate,
    indicator_of_notMem (show u ∉ Ioi (2 : ℝ) from not_lt.mpr hu), add_zero]

theorem polynomialCandidate_above (p : List ℚ) {u : ℝ} (hu : 2 < u) :
    polynomialCandidate p u = eval p u / u := by
  have hu1 : 1 ≤ u := by linarith
  simp only [polynomialCandidate, indicator_of_mem hu, max_eq_right hu1]
  ring

/-- Even a nonzero anchor defect gives an integrable candidate, including
the anchor jump itself. No continuity at 2 is presumed. -/
theorem polynomialCandidate_intervals (p : List ℚ) : AllIntervals (polynomialCandidate p) := by
  have hd : Continuous (fun u : ℝ => max 1 u) := continuous_const.max continuous_id
  have hn : ∀ u : ℝ, max 1 u ≠ 0 := by
    intro u
    have h := le_max_left (1 : ℝ) u
    linarith
  have hc : Continuous (fun u : ℝ => (eval p u - 1) / max 1 u) :=
    ((eval_continuous p).sub continuous_const).div hd hn
  have hi : LocallyIntegrable ((Ioi (2 : ℝ)).indicator
      (fun u : ℝ => (eval p u - 1) / max 1 u)) volume :=
    hc.locallyIntegrable.indicator measurableSet_Ioi
  intro a b
  exact ((continuous_approx 0).intervalIntegrable a b).add
    ((hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)

/-- FTC gives the local additive renewal noise from the anchor and the
true derivative residual of the weighted polynomial. The residual is
compared with the previous finite candidate, not with Buchstab itself. -/
theorem polynomialCandidate_renewal_error {R alpha eta : ℝ}
    (hR : 2 ≤ R) (halpha : 0 ≤ alpha) (heta : 0 ≤ eta)
    (p : List ℚ) {previous : ℝ → ℝ} (hprevious : AllIntervals previous)
    (hanchor : |eval p 2 - 1| ≤ alpha)
    (hresidual : ∀ t ∈ Icc (2 : ℝ) R,
      |eval (derivative p) t - previous (t - 1)| ≤ eta)
    {u : ℝ} (hu : u ∈ Icc (1 : ℝ) R) :
    |polynomialCandidate p u - renewal previous u| ≤
      alpha / 2 + contraction R * eta := by
  have hq := contraction_bounds hR
  have hepsilon : 0 ≤ alpha / 2 + contraction R * eta :=
    add_nonneg (div_nonneg halpha (by norm_num)) (mul_nonneg hq.1 heta)
  by_cases hu2 : u ≤ 2
  · rw [polynomialCandidate_below p hu2]
    simpa [renewal, max_eq_left hu2] using hepsilon
  · have htwo : 2 < u := lt_of_not_ge hu2
    have hupos : 0 < u := by linarith
    have hRpos : 0 < R := by linarith
    have hFTC : (∫ t in (2 : ℝ)..u, eval (derivative p) t) =
        eval p u - eval p 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _
        exact hasDerivAt_eval p t
      · exact (eval_continuous (derivative p)).intervalIntegrable 2 u
    have hsub := intervalIntegral.integral_sub
      ((eval_continuous (derivative p)).intervalIntegrable 2 u)
      (delayed_intervals hprevious 2 u)
    have heq : polynomialCandidate p u - renewal previous u =
        ((eval p 2 - 1) + ∫ t in (2 : ℝ)..u,
          eval (derivative p) t - previous (t - 1)) / u := by
      rw [polynomialCandidate_above p htwo]
      unfold renewal
      rw [max_eq_right htwo.le, max_eq_right hu.1, hsub, hFTC]
      ring
    have hint : |∫ t in (2 : ℝ)..u,
        eval (derivative p) t - previous (t - 1)| ≤ eta * (u - 2) := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (2 : ℝ)) (b := u) (C := eta)
        (f := fun t => eval (derivative p) t - previous (t - 1)) (fun t ht => by
          rw [Set.uIoc_of_le htwo.le] at ht
          simpa only [Real.norm_eq_abs] using
            hresidual t ⟨ht.1.le, ht.2.trans hu.2⟩)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htwo.le)] using hb
    have hsum : |(eval p 2 - 1) + ∫ t in (2 : ℝ)..u,
        eval (derivative p) t - previous (t - 1)| ≤ alpha + eta * (u - 2) :=
      (abs_add_le _ _).trans (add_le_add hanchor hint)
    have hfactor : (u - 2) / u ≤ contraction R := by
      unfold contraction
      apply (div_le_div_iff₀ hupos hRpos).mpr
      nlinarith [hu.2]
    have hanchorfactor : alpha / u ≤ alpha / 2 :=
      div_le_div_of_nonneg_left halpha (by norm_num) htwo.le
    rw [heq, abs_div, abs_of_pos hupos]
    calc
      _ ≤ (alpha + eta * (u - 2)) / u := div_le_div_of_nonneg_right hsum hupos.le
      _ = alpha / u + ((u - 2) / u) * eta := by ring
      _ ≤ alpha / 2 + contraction R * eta :=
        add_le_add hanchorfactor (mul_le_mul_of_nonneg_right hfactor heta)

/-- Finite polynomial method of steps, retaining the original exact seed. -/
def polynomialStages (p : ℕ → List ℚ) : ℕ → ℝ → ℝ
  | 0, u => approx 0 u
  | n + 1, u => polynomialCandidate (p n) u

theorem polynomialStages_intervals (p : ℕ → List ℚ) (n : ℕ) :
    AllIntervals (polynomialStages p n) := by
  cases n with
  | zero => exact fun a b => (continuous_approx 0).intervalIntegrable a b
  | succ n => exact polynomialCandidate_intervals (p n)

/-- A finite list of primitive polynomial residual bounds controls every
intermediate stage by the existing exact renewal error budget. -/
theorem polynomialStages_error_budget {R alpha eta : ℝ}
    (hR : 2 ≤ R) (halpha : 0 ≤ alpha) (heta : 0 ≤ eta)
    (p : ℕ → List ℚ) (n : ℕ)
    (hanchor : ∀ k < n, |eval (p k) 2 - 1| ≤ alpha)
    (hresidual : ∀ k < n, ∀ t ∈ Icc (2 : ℝ) R,
      |eval (derivative (p k)) t - polynomialStages p k (t - 1)| ≤ eta) :
    ∀ u ∈ Icc (1 : ℝ) R,
      |polynomialStages p n u - approx n u| ≤
        budget R (fun _ => alpha / 2 + contraction R * eta) n := by
  have hepsilon : 0 ≤ alpha / 2 + contraction R * eta :=
    add_nonneg (div_nonneg halpha (by norm_num))
      (mul_nonneg (contraction_bounds hR).1 heta)
  have hrec : ∀ k, k ≤ n → ∀ u ∈ Icc (1 : ℝ) R,
      |polynomialStages p k u - approx k u| ≤
        budget R (fun _ => alpha / 2 + contraction R * eta) k := by
    intro k
    induction k with
    | zero => intro _ u _; simp [polynomialStages, budget]
    | succ k ih =>
        intro hk u hu
        have hkprev : k ≤ n := by omega
        have hkstage : k < n := by omega
        have hlocal := polynomialCandidate_renewal_error hR halpha heta (p k)
          (polynomialStages_intervals p k) (hanchor k hkstage) (hresidual k hkstage) hu
        have hprop := renewal_error_of_intervals hR
          (budget_nonneg hR (fun _ => alpha / 2 + contraction R * eta)
            (fun _ => hepsilon) k)
          (polynomialStages_intervals p k)
          (fun a b => (continuous_approx k).intervalIntegrable a b) (ih hkprev) hu
        calc
          _ = |(polynomialCandidate (p k) u - renewal (polynomialStages p k) u) +
              (renewal (polynomialStages p k) u - renewal (approx k) u)| := by
            rw [polynomialStages, approx_succ_renewal]
            congr 1
            ring
          _ ≤ |polynomialCandidate (p k) u - renewal (polynomialStages p k) u| +
              |renewal (polynomialStages p k) u - renewal (approx k) u| := abs_add_le _ _
          _ ≤ (alpha / 2 + contraction R * eta) + contraction R *
              budget R (fun _ => alpha / 2 + contraction R * eta) k := add_le_add hlocal hprop
          _ = budget R (fun _ => alpha / 2 + contraction R * eta) (k + 1) := by
            rw [budget]
            ring
  exact hrec n le_rfl

/-- Differential residuals and anchor defects of the actual rational
polynomial candidates imply an error against the actual Buchstab function.
The bound is uniform in depth and uses only the first n primitive records. -/
theorem polynomialStages_error_actual {R alpha eta : ℝ}
    (hR : 2 ≤ R) (halpha : 0 ≤ alpha) (heta : 0 ≤ eta)
    (p : ℕ → List ℚ) (n : ℕ) (hdepth : R ≤ (n : ℝ) + 2)
    (hanchor : ∀ k < n, |eval (p k) 2 - 1| ≤ alpha)
    (hresidual : ∀ k < n, ∀ t ∈ Icc (2 : ℝ) R,
      |eval (derivative (p k)) t - polynomialStages p k (t - 1)| ≤ eta) :
    ∀ u ∈ Icc (1 : ℝ) R,
      |polynomialStages p n u - buchstab u| ≤
        R * (alpha / 2 + contraction R * eta) / 2 := by
  have hepsilon : 0 ≤ alpha / 2 + contraction R * eta :=
    add_nonneg (div_nonneg halpha (by norm_num))
      (mul_nonneg (contraction_bounds hR).1 heta)
  intro u hu
  rw [buchstab_eq_approx n u (hu.2.trans hdepth)]
  exact (polynomialStages_error_budget hR halpha heta p n hanchor hresidual u hu).trans
    (budget_le_uniform hR hepsilon (fun _ => alpha / 2 + contraction R * eta)
      (fun _ => le_rfl) n)

end

end ImbalancedChen.P0BuchstabDifferentialResidualTransfer

