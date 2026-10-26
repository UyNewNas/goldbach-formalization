import ImbalancedChen.P5U7SpatialBuchstabMainTransport
import ImbalancedChen.P5U7SpatialFullCDFInterior

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual full and separate ordered-semiprime spatial product-CDF means.
Positive eta is chosen FIRST from genuine full integral continuity and
actual original-N collar smallness, then N from the supplied mixed native
arithmetic interior mean. The separate ordered-semiprime CDF is obtained
by subtracting the proved ACTUAL prime CDF, with the independent genuine
nested semiprime integral as its constant. No final CDF mean is a premise.
-/
namespace ImbalancedChen
noncomputable section
open Set Filter Topology
open scoped BigOperators
open Classical

/-- Full BOTH-component actual spatial CDF at product cutoff M(N).
Target N, its marked pair, excluded divisors, and factor thresholds remain
unchanged. The literal arithmetic collar is paid before eta is removed. -/
theorem tendsto_p5U7SpatialFullCDF_normalized (M : ℕ → ℕ) (beta : ℝ) (hb : 0 < beta)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range (M N),p5U7ArithmeticProductWeight N m)) atTop
        (𝓝 (beta*p5U7OriginalOmegaIntegral 1)) := by
  rw [← p5U7InteriorOmegaIntegral_zero_eq_original]
  apply Metric.tendsto_nhds.2
  intro epsilon he
  have he3 : 0 < epsilon/3 := by positivity
  have hI := (tendsto_p5U7InteriorOmegaIntegral_eta_zero.const_mul beta).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hnear := Metric.tendsto_nhds.mp hI (epsilon/3) he3
  have hcollar := p5U7ActualComponentCollar_eventually_small (epsilon/3) he3
  have hpos : ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0,0 < eta := self_mem_nhdsWithin
  obtain ⟨eta,heta,hcollar,hnear⟩ := (hpos.and (hcollar.and hnear)).exists
  have hFixed := Metric.tendsto_nhds.mp
    (tendsto_p5U7SpatialInteriorFullMass_normalized M beta eta hb heta hMN hratio) (epsilon/3) he3
  filter_upwards [hMN,hcollar,hFixed] with N hm hc hf
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hgap := p5U7SpatialFullCDF_interior_gap hm eta
  have hgap0 := mul_nonneg hnorm hgap.1
  have hgap1 := (mul_le_mul_of_nonneg_left hgap.2 hnorm).trans_lt hc.2
  rw [Real.dist_eq] at hf hnear ⊢
  have heq : (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range (M N),p5U7ArithmeticProductWeight N m)-beta*p5U7InteriorOmegaIntegral 0 =
      (Real.log (N : ℝ)/(N : ℝ))*
        ((∑ m ∈ Finset.range (M N),p5U7ArithmeticProductWeight N m)-
          p5U7SpatialInteriorFullMass N (M N) eta)+
      ((Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorFullMass N (M N) eta-
        beta*p5U7InteriorOmegaIntegral eta)+
      (beta*p5U7InteriorOmegaIntegral eta-beta*p5U7InteriorOmegaIntegral 0) := by ring
  rw [heq]
  calc
    _ ≤ |(Real.log (N : ℝ)/(N : ℝ))*
          ((∑ m ∈ Finset.range (M N),p5U7ArithmeticProductWeight N m)-
            p5U7SpatialInteriorFullMass N (M N) eta)|+
        |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorFullMass N (M N) eta-
          beta*p5U7InteriorOmegaIntegral eta|+
        |beta*p5U7InteriorOmegaIntegral eta-beta*p5U7InteriorOmegaIntegral 0| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ < epsilon := by
      rw [abs_of_nonneg hgap0]
      linarith only [hgap1,hf,hnear]

/-- Separate ACTUAL ordered-semiprime spatial CDF. The full physical
source is reduced by the correct actual prime component, retaining every
marked product-fibre multiplicity and the repeated terminal-prime wall. -/
theorem tendsto_p5U7SpatialSemiprimeCDF_normalized (M : ℕ → ℕ) (beta : ℝ) (hb : 0 < beta)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range (M N),p5U7ActualSemiprimeProductWeight N m)) atTop
        (𝓝 (beta*p5U7ComponentSemiprimeIntegral)) := by
  have h := (tendsto_p5U7SpatialFullCDF_normalized M beta hb hMN hratio).sub
    (tendsto_p5U7SpatialPrimeCDF_normalized M beta hb hMN hratio)
  rw [p5U7ComponentSemiprimeIntegral_eq_sub]
  convert h using 1
  · funext N
    simp only [p5U7ArithmeticProductWeight_eq_components,Finset.sum_add_distrib]
    ring
  · ring

/-- Literal eta-zero semiprime-kernel form of the same actual spatial
CDF limit. The constant is changed only by the proved integral dictionary. -/
theorem tendsto_p5U7SpatialSemiprimeCDF_zeroIntegral (M : ℕ → ℕ) (beta : ℝ) (hb : 0 < beta)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range (M N),p5U7ActualSemiprimeProductWeight N m)) atTop
        (𝓝 (beta*p5U7SemiprimeLeadingIntegral 0)) := by
  rw [p5U7SemiprimeLeadingIntegral_zero_eq_component]
  exact tendsto_p5U7SpatialSemiprimeCDF_normalized M beta hb hMN hratio

end
end ImbalancedChen
