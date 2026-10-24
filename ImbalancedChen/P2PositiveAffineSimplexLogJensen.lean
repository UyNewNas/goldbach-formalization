import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no producer or numeric replay.

Analytic core of the frozen per-simplex moment engine for catalog savings
7, 17 and 19.  The physical integral is g/prod_i L_i under Lebesgue measure
restricted to the actual simplex.  Normalize the genuine weight g by its
positive integral, apply Mathlib's proved exponential Jensen theorem to
-sum_i log L_i, then transport the result back to that same weighted integral.

`weighted_probability_log_jensen` accepts individual normalized log-moment
upper bounds, not a target gain or reciprocal-integral bound.
`weighted_log_gap_cubic_lower` proves the engine's cubic exp correction from
individual log-gap lower bounds.  Compact positive affine cells receive an
automatic integrability specialization.  No simplex volume/moment formula,
degree-6 log-gap arithmetic or integer floor certificate is silently supplied.
-/

namespace ImbalancedChen.P2PositiveAffineSimplexLogJensenSourceOnly

noncomputable section

open Set MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

def mass (μ : Measure α) (g : α → ℝ) : ℝ := ∫ x, g x ∂μ

def weightedProbability (μ : Measure α) (g : α → ℝ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (g x / mass μ g))

theorem weightedProbability_isProbability (μ : Measure α) (g : α → ℝ)
    (hg : Integrable g μ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g) :
    IsProbabilityMeasure (weightedProbability μ g) := by
  have hi : Integrable (fun x => g x / mass μ g) μ := hg.div_const _
  have hn : ∀ᵐ x ∂μ, 0 ≤ g x / mass μ g := hg0.mono fun x hx => div_nonneg hx hm.le
  constructor
  rw [weightedProbability, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div]
  change ENNReal.ofReal (mass μ g / mass μ g) = 1
  rw [div_self hm.ne']
  simp

/-- Actual Radon-Nikodym formula, including the weight normalization. -/
theorem integral_weightedProbability (μ : Measure α) (g : α → ℝ)
    (hg : Measurable g) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g) (f : α → ℝ) :
    (∫ x, f x ∂weightedProbability μ g) = (∫ x, g x * f x ∂μ) / mass μ g := by
  rw [weightedProbability, integral_withDensity_eq_integral_toReal_smul
    ((hg.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x, (g x * f x) / mass μ g ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg0] with x hx
      rw [ENNReal.toReal_ofReal (div_nonneg hx hm.le), smul_eq_mul]
      ring
    _ = _ := integral_div _ _

theorem integrable_weightedProbability (μ : Measure α) (g : α → ℝ)
    (hg : Measurable g) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g)
    {f : α → ℝ} (hf : Integrable (fun x => g x * f x) μ) :
    Integrable f (weightedProbability μ g) := by
  unfold weightedProbability
  apply (integrable_withDensity_iff_integrable_smul'
    ((hg.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  apply (hf.div_const (mass μ g)).congr
  filter_upwards [hg0] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hm.le), smul_eq_mul]
  ring

variable {ι : Type*} [Fintype ι]

def negativeLogProduct (L : ι → α → ℝ) (x : α) : ℝ := -∑ i, Real.log (L i x)

theorem exp_negativeLogProduct (L : ι → α → ℝ) {x : α} (hL : ∀ i, 0 < L i x) :
    Real.exp (negativeLogProduct L x) = 1 / ∏ i, L i x := by
  have hp : 0 < ∏ i, L i x := Finset.prod_pos (fun i hi => hL i)
  have hl : Real.log (∏ i, L i x) = ∑ i, Real.log (L i x) :=
    Real.log_prod (fun i hi => (hL i).ne')
  rw [negativeLogProduct, ← hl, Real.exp_neg, Real.exp_log hp]
  simp only [one_div]

/-- Weighted exponential Jensen for the actual reciprocal product integral.
The supplied bounds concern individual log moments, never the target integral. -/
theorem weighted_probability_log_jensen
    (μ : Measure α) (g : α → ℝ) (L : ι → α → ℝ) (B : ι → ℝ)
    (hgMeas : Measurable g) (hgInt : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g)
    (hL0 : ∀ᵐ x ∂μ, ∀ i, 0 < L i x)
    (hLog : ∀ i, Integrable (fun x => g x * Real.log (L i x)) μ)
    (hRecip : Integrable (fun x => g x / ∏ i, L i x) μ)
    (hBound : ∀ i, (∫ x, g x * Real.log (L i x) ∂μ) / mass μ g ≤ B i) :
    mass μ g * Real.exp (-∑ i, B i) ≤ ∫ x, g x / ∏ i, L i x ∂μ := by
  let ν := weightedProbability μ g
  letI : IsProbabilityMeasure ν := weightedProbability_isProbability μ g hgInt hg0 hm
  have hLogν (i : ι) : Integrable (fun x => Real.log (L i x)) ν :=
    integrable_weightedProbability μ g hgMeas hg0 hm (hLog i)
  have hU : Integrable (negativeLogProduct L) ν :=
    (integrable_finsetSum Finset.univ (fun i hi => hLogν i)).neg
  have hRaw : Integrable (fun x => g x * (1 / ∏ i, L i x)) μ := by
    simpa only [mul_one_div] using hRecip
  have hRecipν : Integrable (fun x => 1 / ∏ i, L i x) ν :=
    integrable_weightedProbability μ g hgMeas hg0 hm hRaw
  have hLν : ∀ᵐ x ∂ν, ∀ i, 0 < L i x :=
    (withDensity_absolutelyContinuous _ _).ae_le hL0
  have hExpEq : (fun x => Real.exp (negativeLogProduct L x)) =ᵐ[ν]
      (fun x => 1 / ∏ i, L i x) :=
    hLν.mono (fun x hx => exp_negativeLogProduct L hx)
  have hExp : Integrable (Real.exp ∘ negativeLogProduct L) ν :=
    hRecipν.congr hExpEq.symm
  have hJ := Real.convexOn_exp.map_integral_le
    Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun x => mem_univ (negativeLogProduct L x))) hU hExp
  have hMean : (∫ x, negativeLogProduct L x ∂ν) =
      -∑ i, (∫ x, Real.log (L i x) ∂ν) := by
    simp only [negativeLogProduct, integral_neg,
      integral_finsetSum Finset.univ (fun i hi => hLogν i)]
  have hMom (i : ι) : (∫ x, Real.log (L i x) ∂ν) ≤ B i := by
    rw [integral_weightedProbability μ g hgMeas hg0 hm]
    exact hBound i
  have hMeanLower : -∑ i, B i ≤ ∫ x, negativeLogProduct L x ∂ν := by
    rw [hMean]
    exact neg_le_neg (Finset.sum_le_sum (fun i hi => hMom i))
  have hNormalized : Real.exp (-∑ i, B i) ≤
      (∫ x, g x / ∏ i, L i x ∂μ) / mass μ g := by
    calc
      _ ≤ Real.exp (∫ x, negativeLogProduct L x ∂ν) := Real.exp_le_exp.mpr hMeanLower
      _ ≤ ∫ x, Real.exp (negativeLogProduct L x) ∂ν := hJ
      _ = ∫ x, 1 / ∏ i, L i x ∂ν := integral_congr_ae hExpEq
      _ = _ := by
        rw [integral_weightedProbability μ g hgMeas hg0 hm]
        simp only [mul_one_div]
  have h := (le_div_iff₀ hm).1 hNormalized
  nlinarith

def cubicCorrection (T : ℝ) : ℝ := 1 + T * (1 + T * (1 / 2 + T / 6))

theorem cubicCorrection_le_exp {T : ℝ} (hT : 0 ≤ T) : cubicCorrection T ≤ Real.exp T := by
  have h := Real.sum_le_exp_of_nonneg hT 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  dsimp [cubicCorrection]
  nlinarith

/-- The actual producer's cubic positive exponential correction is sound once
the individual log-gap lower bounds have been proved. -/
theorem weighted_log_gap_cubic_lower
    (μ : Measure α) (g : α → ℝ) (L : ι → α → ℝ) (means gaps : ι → ℝ)
    (hgMeas : Measurable g) (hgInt : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g)
    (hL0 : ∀ᵐ x ∂μ, ∀ i, 0 < L i x)
    (hLog : ∀ i, Integrable (fun x => g x * Real.log (L i x)) μ)
    (hRecip : Integrable (fun x => g x / ∏ i, L i x) μ)
    (hMeans : ∀ i, 0 < means i) (hGaps : ∀ i, 0 ≤ gaps i)
    (hBound : ∀ i, (∫ x, g x * Real.log (L i x) ∂μ) / mass μ g ≤
      Real.log (means i) - gaps i) :
    (mass μ g / ∏ i, means i) * cubicCorrection (∑ i, gaps i) ≤
      ∫ x, g x / ∏ i, L i x ∂μ := by
  have h := weighted_probability_log_jensen μ g L
    (fun i => Real.log (means i) - gaps i) hgMeas hgInt hg0 hm hL0 hLog hRecip hBound
  have hp : 0 < ∏ i, means i := Finset.prod_pos (fun i hi => hMeans i)
  have hlog : Real.log (∏ i, means i) = ∑ i, Real.log (means i) :=
    Real.log_prod (fun i hi => (hMeans i).ne')
  rw [Finset.sum_sub_distrib, ← hlog, neg_sub, Real.exp_sub, Real.exp_log hp] at h
  have hT : 0 ≤ ∑ i, gaps i := Finset.sum_nonneg (fun i hi => hGaps i)
  calc
    _ ≤ (mass μ g / ∏ i, means i) * Real.exp (∑ i, gaps i) :=
      mul_le_mul_of_nonneg_left (cubicCorrection_le_exp hT) (div_nonneg hm.le hp.le)
    _ = mass μ g * (Real.exp (∑ i, gaps i) / ∏ i, means i) := by ring
    _ ≤ _ := h

/-- Original normalization: factor4 is retained, with no Chen quarter or
ordered-slot factorial inserted. -/
theorem weighted_log_gap_cubic_lower_four
    (μ : Measure α) (g : α → ℝ) (L : ι → α → ℝ) (means gaps : ι → ℝ)
    (hgMeas : Measurable g) (hgInt : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g)
    (hL0 : ∀ᵐ x ∂μ, ∀ i, 0 < L i x)
    (hLog : ∀ i, Integrable (fun x => g x * Real.log (L i x)) μ)
    (hRecip : Integrable (fun x => g x / ∏ i, L i x) μ)
    (hMeans : ∀ i, 0 < means i) (hGaps : ∀ i, 0 ≤ gaps i)
    (hBound : ∀ i, (∫ x, g x * Real.log (L i x) ∂μ) / mass μ g ≤
      Real.log (means i) - gaps i) :
    (4 * mass μ g / ∏ i, means i) * cubicCorrection (∑ i, gaps i) ≤
      ∫ x, 4 * g x / ∏ i, L i x ∂μ := by
  have h := mul_le_mul_of_nonneg_left
    (weighted_log_gap_cubic_lower μ g L means gaps hgMeas hgInt hg0 hm hL0 hLog hRecip
      hMeans hGaps hBound) (by norm_num : (0 : ℝ) ≤ 4)
  have he : (∫ x, 4 * g x / ∏ i, L i x ∂μ) =
      4 * ∫ x, g x / ∏ i, L i x ∂μ := by
    simpa only [mul_div_assoc] using integral_const_mul 4 (fun x => g x / ∏ i, L i x)
  rw [he]
  nlinarith

/-! An actual finite-dimensional affine-cell receiver.  A closed simplex is
one such compact measurable cell; its volume/moments remain external data. -/

def affineScalar {d : ℕ} (c : ℝ) (a : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  c + ∑ k, a k * x k

theorem continuous_affineScalar {d : ℕ} (c : ℝ) (a : Fin d → ℝ) :
    Continuous (affineScalar c a) := by
  apply continuous_const.add
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (continuous_apply k)

theorem compact_affine_cell_log_jensen {d : ℕ}
    (D : Set (Fin d → ℝ)) (hD : IsCompact D) (hDMeas : MeasurableSet D)
    (gc : ℝ) (ga : Fin d → ℝ) (Lc : ι → ℝ) (La : ι → Fin d → ℝ) (B : ι → ℝ)
    (hg0 : ∀ x ∈ D, 0 ≤ affineScalar gc ga x)
    (hL0 : ∀ x ∈ D, ∀ i, 0 < affineScalar (Lc i) (La i) x)
    (hm : 0 < ∫ x in D, affineScalar gc ga x)
    (hBound : ∀ i,
      (∫ x in D, affineScalar gc ga x * Real.log (affineScalar (Lc i) (La i) x)) /
        (∫ x in D, affineScalar gc ga x) ≤ B i) :
    (∫ x in D, affineScalar gc ga x) * Real.exp (-∑ i, B i) ≤
      ∫ x in D, affineScalar gc ga x / ∏ i, affineScalar (Lc i) (La i) x := by
  let g := affineScalar gc ga
  let L (i : ι) := affineScalar (Lc i) (La i)
  have hgCont : Continuous g := continuous_affineScalar gc ga
  have hLCont (i : ι) : Continuous (L i) := continuous_affineScalar (Lc i) (La i)
  have hgInt : Integrable g (volume.restrict D) := hgCont.continuousOn.integrableOn_compact hD
  have hgAE : ∀ᵐ x ∂volume.restrict D, 0 ≤ g x := by
    filter_upwards [ae_restrict_mem hDMeas] with x hx
    exact hg0 x hx
  have hLAE : ∀ᵐ x ∂volume.restrict D, ∀ i, 0 < L i x := by
    filter_upwards [ae_restrict_mem hDMeas] with x hx
    exact hL0 x hx
  have hLogInt (i : ι) : Integrable (fun x => g x * Real.log (L i x)) (volume.restrict D) := by
    apply ContinuousOn.integrableOn_compact _ hD
    exact hgCont.continuousOn.mul
      ((hLCont i).continuousOn.log (fun x hx => (hL0 x hx i).ne'))
  have hProd : ContinuousOn (fun x => ∏ i, L i x) D := by
    apply continuousOn_finsetProd
    intro i hi
    exact (hLCont i).continuousOn
  have hRecip : Integrable (fun x => g x / ∏ i, L i x) (volume.restrict D) := by
    apply ContinuousOn.integrableOn_compact _ hD
    exact hgCont.continuousOn.div hProd (fun x hx =>
      (Finset.prod_pos (fun i hi => hL0 x hx i)).ne')
  exact weighted_probability_log_jensen (volume.restrict D) g L B hgCont.measurable
    hgInt hgAE hm hLAE hLogInt hRecip hBound

end

end ImbalancedChen.P2PositiveAffineSimplexLogJensenSourceOnly
