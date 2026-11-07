import MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction
import Mathlib.Tactic

/-!
A quantitative stability theorem for the actual Buchstab method of steps.
The renewal operator below is exactly the defining integral of the pinned
`LiLiuPrereqBuchstab.approx`, including both continuous cutoffs.

On [1,R], R >= 2, its sup error coefficient is (R-2)/R < 1.
Literal additive perturbations therefore have a depth-independent error
bound R*epsilon/2. At any depth n with R <= n+2, the reference approximant
is exactly the actual Buchstab function. No final error bound, bank endpoint
licence, table soundness, or saved-output estimate is assumed.

SOURCE_WRITTEN_UNCOMPILED. No compilation or numerical replay was performed.
-/

namespace ImbalancedChen.P0BuchstabRenewalErrorPropagation

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

/-- The actual positive Buchstab renewal operator, with its literal cutoffs. -/
def renewal (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 + ∫ t in (2 : ℝ)..max 2 u, f (t - 1)) / max 1 u

theorem approx_succ_renewal (n : ℕ) : approx (n + 1) = renewal (approx n) := rfl

def contraction (R : ℝ) : ℝ := (R - 2) / R

theorem contraction_bounds {R : ℝ} (hR : 2 ≤ R) :
    0 ≤ contraction R ∧ contraction R < 1 := by
  have hRpos : 0 < R := by linarith
  constructor
  · exact div_nonneg (by linarith) hRpos.le
  · exact (div_lt_one hRpos).mpr (by linarith)

theorem continuous_renewal {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (renewal f) := by
  have hc : Continuous (fun t : ℝ => f (t - 1)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hp : Continuous (fun u : ℝ => ∫ t in (2 : ℝ)..u, f (t - 1)) :=
    continuous_iff_continuousAt.mpr
      (fun u => (hc.integral_hasStrictDerivAt 2 u).hasDerivAt.continuousAt)
  have hd : Continuous (fun u : ℝ => max 1 u) := continuous_const.max continuous_id
  have hn : ∀ u : ℝ, max 1 u ≠ 0 := by
    intro u
    have h := le_max_left (1 : ℝ) u
    linarith
  exact (continuous_const.add
    (hp.comp (continuous_const.max continuous_id))).div hd hn

/-- Nonnegative delayed inputs give a strictly positive renewal output. -/
theorem renewal_positive {f : ℝ → ℝ} (hf : Continuous f)
    (hnonneg : ∀ u : ℝ, 1 ≤ u → 0 ≤ f u) (u : ℝ) :
    0 < renewal f u := by
  have hc : Continuous (fun t : ℝ => f (t - 1)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hi := intervalIntegral.integral_mono_on (le_max_left (2 : ℝ) u)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 2 (max 2 u))
    (hc.intervalIntegrable 2 (max 2 u))
    (fun t ht => hnonneg (t - 1) (by linarith [ht.1]))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hi
  exact div_pos (by linarith only [hi])
    (lt_of_lt_of_le (by norm_num) (le_max_left (1 : ℝ) u))

/-- Exact sup-norm coefficient on a fixed physical argument window.
The input error is needed only on that same window, since every delayed
argument t-1 lies in [1,R]. -/
theorem renewal_error {R E : ℝ} (hR : 2 ≤ R) (hE : 0 ≤ E)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (herr : ∀ v ∈ Icc (1 : ℝ) R, |f v - g v| ≤ E)
    {u : ℝ} (hu : u ∈ Icc (1 : ℝ) R) :
    |renewal f u - renewal g u| ≤ contraction R * E := by
  have hq := contraction_bounds hR
  by_cases hu2 : u ≤ 2
  · simpa [renewal, max_eq_left hu2] using mul_nonneg hq.1 hE
  · have htwo : 2 ≤ u := (lt_of_not_ge hu2).le
    have hupos : 0 < u := by linarith
    have hRpos : 0 < R := by linarith
    have hfc : Continuous (fun t : ℝ => f (t - 1)) :=
      hf.comp (continuous_id.sub continuous_const)
    have hgc : Continuous (fun t : ℝ => g (t - 1)) :=
      hg.comp (continuous_id.sub continuous_const)
    have hsub := intervalIntegral.integral_sub
      (hfc.intervalIntegrable 2 u) (hgc.intervalIntegrable 2 u)
    have heq : renewal f u - renewal g u =
        (∫ t in (2 : ℝ)..u, f (t - 1) - g (t - 1)) / u := by
      unfold renewal
      rw [max_eq_right htwo, max_eq_right hu.1, hsub]
      ring
    have hint : |∫ t in (2 : ℝ)..u, f (t - 1) - g (t - 1)| ≤ E * (u - 2) := by
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (2 : ℝ)) (b := u) (C := E)
        (f := fun t : ℝ => f (t - 1) - g (t - 1)) (fun t ht => by
          rw [Set.uIoc_of_le htwo] at ht
          simpa only [Real.norm_eq_abs] using
            herr (t - 1) ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htwo)] using hbound
    have hfactor : (u - 2) / u ≤ contraction R := by
      unfold contraction
      apply (div_le_div_iff₀ hupos hRpos).mpr
      nlinarith [hu.2]
    rw [heq, abs_div, abs_of_pos hupos]
    calc
      _ ≤ (E * (u - 2)) / u := div_le_div_of_nonneg_right hint hupos.le
      _ = ((u - 2) / u) * E := by ring
      _ ≤ contraction R * E := mul_le_mul_of_nonneg_right hfactor hE

/-- A literal perturbed method of steps; eta is the local additive error,
not an assumed enclosure of the limiting Buchstab function. -/
def noisyApprox (eta : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, u => approx 0 u
  | n + 1, u => renewal (noisyApprox eta n) u + eta n u

theorem continuous_noisyApprox (eta : ℕ → ℝ → ℝ)
    (heta : ∀ n, Continuous (eta n)) (n : ℕ) : Continuous (noisyApprox eta n) := by
  induction n with
  | zero => exact continuous_approx 0
  | succ n ih => exact (continuous_renewal ih).add (heta n)

/-- A positive perturbation keeps every finite renewal approximation
strictly positive, directly from the actual initial reciprocal. -/
theorem noisyApprox_positive (eta : ℕ → ℝ → ℝ)
    (heta : ∀ n, Continuous (eta n))
    (heta0 : ∀ n u, 0 ≤ eta n u) (n : ℕ) (u : ℝ) :
    0 < noisyApprox eta n u := by
  induction n generalizing u with
  | zero =>
      change 0 < 1 / max 1 u
      exact div_pos (by norm_num)
        (lt_of_lt_of_le (by norm_num) (le_max_left (1 : ℝ) u))
  | succ n ih =>
      exact add_pos_of_pos_of_nonneg
        (renewal_positive (continuous_noisyApprox eta heta n)
          (fun v _ => (ih v).le) u) (heta0 n u)

/-- The exact finite error recurrence, with one local error per renewal. -/
def budget (R : ℝ) (delta : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => contraction R * budget R delta n + delta n

theorem budget_nonneg {R : ℝ} (hR : 2 ≤ R) (delta : ℕ → ℝ)
    (hdelta : ∀ n, 0 ≤ delta n) (n : ℕ) : 0 ≤ budget R delta n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (mul_nonneg (contraction_bounds hR).1 ih) (hdelta n)

theorem noisyApprox_error {R : ℝ} (hR : 2 ≤ R)
    (eta : ℕ → ℝ → ℝ) (heta : ∀ n, Continuous (eta n))
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 ≤ delta n)
    (hlocal : ∀ n u, u ∈ Icc (1 : ℝ) R → |eta n u| ≤ delta n)
    (n : ℕ) : ∀ u ∈ Icc (1 : ℝ) R,
      |noisyApprox eta n u - approx n u| ≤ budget R delta n := by
  induction n with
  | zero => intro u _; simp [noisyApprox, budget]
  | succ n ih =>
      intro u hu
      have hr := renewal_error hR (budget_nonneg hR delta hdelta n)
        (continuous_noisyApprox eta heta n) (continuous_approx n) ih hu
      calc
        _ = |(renewal (noisyApprox eta n) u - renewal (approx n) u) + eta n u| := by
          rw [noisyApprox, approx_succ_renewal]
          congr 1
          ring
        _ ≤ |renewal (noisyApprox eta n) u - renewal (approx n) u| + |eta n u| :=
          abs_add_le _ _
        _ ≤ contraction R * budget R delta n + delta n := add_le_add hr (hlocal n u hu)
        _ = budget R delta (n + 1) := rfl

/-- Because the true renewal operator is contractive on every fixed
window, a uniformly bounded local error has a bound independent of depth. -/
theorem budget_le_uniform {R epsilon : ℝ} (hR : 2 ≤ R) (hepsilon : 0 ≤ epsilon)
    (delta : ℕ → ℝ) (hdelta : ∀ n, delta n ≤ epsilon) (n : ℕ) :
    budget R delta n ≤ R * epsilon / 2 := by
  have hRpos : 0 < R := by linarith
  have hfixed : contraction R * (R * epsilon / 2) + epsilon = R * epsilon / 2 := by
    unfold contraction
    field_simp [hRpos.ne'] <;> ring
  induction n with
  | zero => exact div_nonneg (mul_nonneg hRpos.le hepsilon) (by norm_num)
  | succ n ih =>
      calc
        budget R delta (n + 1) = contraction R * budget R delta n + delta n := rfl
        _ ≤ contraction R * (R * epsilon / 2) + epsilon :=
          add_le_add (mul_le_mul_of_nonneg_left ih (contraction_bounds hR).1) (hdelta n)
        _ = R * epsilon / 2 := hfixed

/-- Actual Buchstab error after a sufficient finite number of steps.
The only approximation hypothesis is the literal local perturbation size. -/
theorem noisyApprox_error_actual {R epsilon : ℝ} (hR : 2 ≤ R)
    (hepsilon : 0 ≤ epsilon) (eta : ℕ → ℝ → ℝ)
    (heta : ∀ n, Continuous (eta n))
    (hlocal : ∀ n u, u ∈ Icc (1 : ℝ) R → |eta n u| ≤ epsilon)
    (n : ℕ) (hdepth : R ≤ (n : ℝ) + 2) :
    ∀ u ∈ Icc (1 : ℝ) R,
      |noisyApprox eta n u - buchstab u| ≤ R * epsilon / 2 := by
  intro u hu
  rw [buchstab_eq_approx n u (hu.2.trans hdepth)]
  exact (noisyApprox_error hR eta heta (fun _ => epsilon) (fun _ => hepsilon)
    hlocal n u hu).trans (budget_le_uniform hR hepsilon (fun _ => epsilon) (fun _ => le_rfl) n)

end

end ImbalancedChen.P0BuchstabRenewalErrorPropagation

