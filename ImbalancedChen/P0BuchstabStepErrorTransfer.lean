import ImbalancedChen.P0BuchstabRenewalErrorPropagation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Finite discontinuous step errors in the actual Buchstab renewal integral.
The local noise is a literal finite sum of interval indicators and constants.
Its integrability and absolute size follow from that finite data. The uniform
finite-depth bound is inherited from the actual renewal contraction, rather
than assuming a bound against Buchstab. Closed versus right-open endpoint
conventions have exactly the same next renewal value.

SOURCE_WRITTEN_UNCOMPILED; no compiler or numerical replay was run.
-/

namespace ImbalancedChen.P0BuchstabStepErrorTransfer

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open P0BuchstabRenewalErrorPropagation
open scoped Interval BigOperators

/-- Local integrability expressed in the exact form needed by renewal. -/
def AllIntervals (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, IntervalIntegrable f volume a b

theorem delayed_intervals {f : ℝ → ℝ} (hf : AllIntervals f) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => f (t - 1)) volume a b := by
  simpa only [sub_add_cancel] using (hf (a - 1) (b - 1)).comp_sub_right 1

/-- An integrable step input still has a continuous renewal output. -/
theorem continuous_renewal_of_intervals {f : ℝ → ℝ} (hf : AllIntervals f) :
    Continuous (renewal f) := by
  have hp : Continuous (fun u : ℝ => ∫ t in (2 : ℝ)..u, f (t - 1)) :=
    intervalIntegral.continuous_primitive (delayed_intervals hf) 2
  have hd : Continuous (fun u : ℝ => max 1 u) := continuous_const.max continuous_id
  have hn : ∀ u : ℝ, max 1 u ≠ 0 := by
    intro u
    have h := le_max_left (1 : ℝ) u
    linarith
  exact (continuous_const.add
    (hp.comp (continuous_const.max continuous_id))).div hd hn

/-- The contraction uses integrability, and allows arbitrary jumps in the
input. The input bound is the inherited finite-stage error on [1,R]. -/
theorem renewal_error_of_intervals {R E : ℝ} (hR : 2 ≤ R) (hE : 0 ≤ E)
    {f g : ℝ → ℝ} (hf : AllIntervals f) (hg : AllIntervals g)
    (herr : ∀ v ∈ Icc (1 : ℝ) R, |f v - g v| ≤ E)
    {u : ℝ} (hu : u ∈ Icc (1 : ℝ) R) :
    |renewal f u - renewal g u| ≤ contraction R * E := by
  have hq := contraction_bounds hR
  by_cases hu2 : u ≤ 2
  · simpa [renewal, max_eq_left hu2] using mul_nonneg hq.1 hE
  · have htwo : 2 ≤ u := (lt_of_not_ge hu2).le
    have hupos : 0 < u := by linarith
    have hRpos : 0 < R := by linarith
    have hsub := intervalIntegral.integral_sub
      (delayed_intervals hf 2 u) (delayed_intervals hg 2 u)
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

theorem noisyApprox_intervals (eta : ℕ → ℝ → ℝ)
    (heta : ∀ n, AllIntervals (eta n)) (n : ℕ) : AllIntervals (noisyApprox eta n) := by
  induction n with
  | zero => exact fun a b => (continuous_approx 0).intervalIntegrable a b
  | succ n ih =>
      intro a b
      exact ((continuous_renewal_of_intervals ih).intervalIntegrable a b).add (heta n a b)

theorem noisyApprox_error_of_intervals {R : ℝ} (hR : 2 ≤ R)
    (eta : ℕ → ℝ → ℝ) (heta : ∀ n, AllIntervals (eta n))
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 ≤ delta n)
    (hlocal : ∀ n u, u ∈ Icc (1 : ℝ) R → |eta n u| ≤ delta n)
    (n : ℕ) : ∀ u ∈ Icc (1 : ℝ) R,
      |noisyApprox eta n u - approx n u| ≤ budget R delta n := by
  induction n with
  | zero => intro u _; simp [noisyApprox, budget]
  | succ n ih =>
      intro u hu
      have hr := renewal_error_of_intervals hR (budget_nonneg hR delta hdelta n)
        (noisyApprox_intervals eta heta n)
        (fun a b => (continuous_approx n).intervalIntegrable a b) ih hu
      calc
        _ = |(renewal (noisyApprox eta n) u - renewal (approx n) u) + eta n u| := by
          rw [noisyApprox, approx_succ_renewal]
          congr 1
          ring
        _ ≤ |renewal (noisyApprox eta n) u - renewal (approx n) u| + |eta n u| :=
          abs_add_le _ _
        _ ≤ contraction R * budget R delta n + delta n := add_le_add hr (hlocal n u hu)
        _ = budget R delta (n + 1) := rfl

/-- Literal finite interval-constant data. Overlapping intervals are allowed. -/
def stepFunction {m : ℕ} (lo hi coefficient : Fin m → ℝ) (u : ℝ) : ℝ :=
  ∑ i : Fin m, (Icc (lo i) (hi i)).indicator (fun _ => coefficient i) u

theorem stepFunction_integrable {m : ℕ} (lo hi coefficient : Fin m → ℝ) :
    Integrable (stepFunction lo hi coefficient) volume := by
  apply integrable_finsetSum
  intro i _
  exact ((continuous_const : Continuous (fun _ : ℝ => coefficient i)).integrableOn_Icc
    (a := lo i) (b := hi i)).integrable_indicator measurableSet_Icc

theorem stepFunction_abs_le {m : ℕ} (lo hi coefficient : Fin m → ℝ) (u : ℝ) :
    |stepFunction lo hi coefficient u| ≤ ∑ i : Fin m, |coefficient i| := by
  unfold stepFunction
  calc
    _ ≤ ∑ i : Fin m, |(Icc (lo i) (hi i)).indicator (fun _ => coefficient i) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, |coefficient i| := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hu : u ∈ Icc (lo i) (hi i)
      · simp only [indicator_of_mem hu, le_refl]
      · simp only [indicator_of_notMem hu, abs_zero]
        exact abs_nonneg _

/-- Concrete discontinuous step data now yields the same uniform-depth
actual-Buchstab estimate. The only numerical premise is a finite sum of
absolute local step coefficients, not a bound against the true function. -/
theorem stepNoise_error_actual {m : ℕ} {R epsilon : ℝ} (hR : 2 ≤ R)
    (hepsilon : 0 ≤ epsilon) (lo hi coefficient : ℕ → Fin m → ℝ)
    (hcoeff : ∀ n, (∑ i : Fin m, |coefficient n i|) ≤ epsilon)
    (n : ℕ) (hdepth : R ≤ (n : ℝ) + 2) :
    ∀ u ∈ Icc (1 : ℝ) R,
      |noisyApprox (fun k => stepFunction (lo k) (hi k) (coefficient k)) n u -
        buchstab u| ≤ R * epsilon / 2 := by
  intro u hu
  rw [buchstab_eq_approx n u (hu.2.trans hdepth)]
  have hlocal : ∀ k v, v ∈ Icc (1 : ℝ) R →
      |stepFunction (lo k) (hi k) (coefficient k) v| ≤ epsilon := by
    intro k v _
    exact (stepFunction_abs_le (lo k) (hi k) (coefficient k) v).trans (hcoeff k)
  exact (noisyApprox_error_of_intervals hR
    (fun k => stepFunction (lo k) (hi k) (coefficient k))
    (fun k a b => (stepFunction_integrable (lo k) (hi k) (coefficient k)).intervalIntegrable)
    (fun _ => epsilon) (fun _ => hepsilon) hlocal n u hu).trans
      (budget_le_uniform hR hepsilon (fun _ => epsilon) (fun _ => le_rfl) n)

/-- Finite endpoint changes disappear in the delayed renewal integral,
including changes at either end of the integration interval. -/
theorem renewal_eq_away_knots {m : ℕ} (knots : Fin m → ℝ)
    {f g : ℝ → ℝ}
    (hfg : ∀ v, (∀ i, v ≠ knots i) → f v = g v) (u : ℝ) :
    renewal f u = renewal g u := by
  have hne : ∀ᵐ t : ℝ ∂volume, ∀ i : Fin m, t ≠ knots i + 1 := by
    apply ae_all_iff.mpr
    intro i
    rw [ae_iff]
    simpa only [not_not] using
      (measure_singleton (knots i + 1) : volume {knots i + 1} = 0)
  have hint : (∫ t in (2 : ℝ)..max 2 u, f (t - 1)) =
      ∫ t in (2 : ℝ)..max 2 u, g (t - 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with t ht
    intro _
    apply hfg (t - 1)
    intro i heq
    exact ht i (by linarith)
  unfold renewal
  rw [hint]

/-- Closed and half-open conventions for every finite step give exactly
one and the same next renewal output. -/
theorem renewal_stepFunction_eq_halfOpen {m : ℕ}
    (lo hi coefficient : Fin m → ℝ) (u : ℝ) :
    renewal (stepFunction lo hi coefficient) u =
      renewal (fun v => ∑ i : Fin m,
        (Ico (lo i) (hi i)).indicator (fun _ => coefficient i) v) u := by
  apply renewal_eq_away_knots hi
  intro v hv
  unfold stepFunction
  apply Finset.sum_congr rfl
  intro i _
  have hmem : v ∈ Icc (lo i) (hi i) ↔ v ∈ Ico (lo i) (hi i) := by
    constructor
    · intro h
      exact ⟨h.1, lt_of_le_of_ne h.2 (hv i)⟩
    · intro h
      exact ⟨h.1, h.2.le⟩
  by_cases h : v ∈ Icc (lo i) (hi i)
  · rw [indicator_of_mem h, indicator_of_mem (hmem.mp h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mpr h'))]

/-- A finite right-open table, allowing the usual adjacent grid cells. -/
def halfOpenStep {m : ℕ} (lo hi coefficient : Fin m → ℝ) (u : ℝ) : ℝ :=
  ∑ i : Fin m, (Ico (lo i) (hi i)).indicator (fun _ => coefficient i) u

theorem halfOpenStep_integrable {m : ℕ} (lo hi coefficient : Fin m → ℝ) :
    Integrable (halfOpenStep lo hi coefficient) volume := by
  apply integrable_finsetSum
  intro i _
  have hc : IntegrableOn (fun _ : ℝ => coefficient i) (Icc (lo i) (hi i)) volume :=
    (continuous_const : Continuous (fun _ : ℝ => coefficient i)).integrableOn_Icc
  exact (hc.mono_set Ico_subset_Icc_self).integrable_indicator measurableSet_Ico

/-- Disjoint half-open cells pay only the largest local coefficient, with
no factor for the number of table cells. No coverage premise is needed. -/
theorem halfOpenStep_abs_le {m : ℕ} {lo hi coefficient : Fin m → ℝ}
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hdisjoint : Pairwise (fun i j : Fin m =>
      Disjoint (Ico (lo i) (hi i)) (Ico (lo j) (hi j))))
    (hcoeff : ∀ i, |coefficient i| ≤ epsilon) (u : ℝ) :
    |halfOpenStep lo hi coefficient u| ≤ epsilon := by
  classical
  by_cases hex : ∃ i : Fin m, u ∈ Ico (lo i) (hi i)
  · obtain ⟨i, hactive⟩ := hex
    have heq : halfOpenStep lo hi coefficient u = coefficient i := by
      unfold halfOpenStep
      calc
        _ = (Ico (lo i) (hi i)).indicator (fun _ => coefficient i) u := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            have hnot : u ∉ Ico (lo j) (hi j) := by
              intro hj
              exact Set.disjoint_left.mp (hdisjoint hji) hj hactive
            exact indicator_of_notMem hnot _
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ i))
        _ = coefficient i := indicator_of_mem hactive _
    rw [heq]
    exact hcoeff i
  · have heq : halfOpenStep lo hi coefficient u = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi => hex ⟨i, hi⟩) _
    rw [heq, abs_zero]
    exact hepsilon

/-- The interval-integrable form of the actual-function transfer. -/
theorem noisyApprox_error_actual_of_intervals {R epsilon : ℝ} (hR : 2 ≤ R)
    (hepsilon : 0 ≤ epsilon) (eta : ℕ → ℝ → ℝ)
    (heta : ∀ n, AllIntervals (eta n))
    (hlocal : ∀ n u, u ∈ Icc (1 : ℝ) R → |eta n u| ≤ epsilon)
    (n : ℕ) (hdepth : R ≤ (n : ℝ) + 2) :
    ∀ u ∈ Icc (1 : ℝ) R,
      |noisyApprox eta n u - buchstab u| ≤ R * epsilon / 2 := by
  intro u hu
  rw [buchstab_eq_approx n u (hu.2.trans hdepth)]
  exact (noisyApprox_error_of_intervals hR eta heta (fun _ => epsilon)
    (fun _ => hepsilon) hlocal n u hu).trans
      (budget_le_uniform hR hepsilon (fun _ => epsilon) (fun _ => le_rfl) n)

/-- The concrete finite table bridge: a per-cell local error epsilon on a
half-open grid gives the same depth-independent R*epsilon/2 error against
the actual Buchstab function. Neither grid length nor knot count is paid. -/
theorem halfOpenStep_error_actual {m : ℕ} {R epsilon : ℝ} (hR : 2 ≤ R)
    (hepsilon : 0 ≤ epsilon) (lo hi coefficient : ℕ → Fin m → ℝ)
    (hdisjoint : ∀ n, Pairwise (fun i j : Fin m =>
      Disjoint (Ico (lo n i) (hi n i)) (Ico (lo n j) (hi n j))))
    (hcoeff : ∀ n i, |coefficient n i| ≤ epsilon)
    (n : ℕ) (hdepth : R ≤ (n : ℝ) + 2) :
    ∀ u ∈ Icc (1 : ℝ) R,
      |noisyApprox (fun k => halfOpenStep (lo k) (hi k) (coefficient k)) n u -
        buchstab u| ≤ R * epsilon / 2 := by
  apply noisyApprox_error_actual_of_intervals hR hepsilon
    (fun k => halfOpenStep (lo k) (hi k) (coefficient k))
    (fun k a b => (halfOpenStep_integrable (lo k) (hi k) (coefficient k)).intervalIntegrable)
  · intro k u _
    exact halfOpenStep_abs_le hepsilon (hdisjoint k) (hcoeff k) u
  · exact hdepth
end

end ImbalancedChen.P0BuchstabStepErrorTransfer


