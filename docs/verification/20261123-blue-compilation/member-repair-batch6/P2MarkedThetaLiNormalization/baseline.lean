import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import ImbalancedChen.NormalizationGrowth
import MathlibNt.SieveTheory.Distribution.BombieriVinogradov

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact conversion between the installed literal-li Theta and the trueLi
normalization, with the SAME finite support, given sigma, singular series,
totient and log(Q/d) kernel. The additive normalization of li changes the
normalizer by an explicit multiple of that kernel, not by a count error.

One N0, chosen using only epsilon, bounds the relative correction for ALL
Q, finite D and original nonnegative sigma satisfying primitive level
positivity. Empty supports and zero total weight are included. There is
no division by family mass, no nonzero-mass assumption, and no count/AP,
positive-product, or enhanced-family supplier in the hypotheses.
-/

namespace ImbalancedChen.P2MarkedThetaLiNormalization

noncomputable section

open Finset Filter Wu2008DoubleSieve
open scoped Classical Topology
open P2EnhancedTwentyOneSameQWeighted (Theta)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The unchanged positive arithmetic mean extracted from installed Theta. -/
def kernelMean (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * wuSingularSeries (d*N) /
    ((Nat.totient d : ℝ)*Real.log (Q/d))

/-- The trueLi version of precisely the same original finite normalizer. -/
def trueTheta (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  4*trueLogarithmicIntegral N*kernelMean N Q D sigma

theorem trueLi_eq_literalLi_add (x : ℝ) :
    trueLogarithmicIntegral x=logarithmicIntegral x+2/Real.log 2 := by
  unfold trueLogarithmicIntegral logarithmicIntegral
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral
  ring

/-- An exact identity, including below-threshold N and empty families. -/
theorem trueTheta_eq_Theta_add (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) :
    trueTheta N Q D sigma=Theta N Q D sigma+
      4*(2/Real.log 2)*kernelMean N Q D sigma := by
  change 4*trueLogarithmicIntegral N*kernelMean N Q D sigma=
    4*logarithmicIntegral N*kernelMean N Q D sigma+
      4*(2/Real.log 2)*kernelMean N Q D sigma
  rw [trueLi_eq_literalLi_add]
  ring

theorem kernelMean_nonneg {N : ℕ} (hN : 0<N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hdpos : ∀d∈D,0<d)
    (hsigma : ∀d∈D,0≤sigma d) (hlevel : ∀d∈D,1<Q/(d:ℝ)) :
    0≤kernelMean N Q D sigma := by
  apply sum_nonneg
  intro d hd
  apply div_nonneg
  · exact mul_nonneg (hsigma d hd)
      (wuSingularSeries_pos (d*N) (Nat.mul_pos (hdpos d hd) hN)).le
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (hlevel d hd)).le

/-- Literal li itself diverges, by the existing elementary N/(2 log N)
lower bound. No prime-count estimate is used in this growth statement. -/
theorem tendsto_literalLi_nat_atTop :
    Tendsto (fun N : ℕ=>logarithmicIntegral N) atTop atTop := by
  have hreal : Tendsto (fun x : ℝ=>x/Real.log x) atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).comp Real.tendsto_log_atTop
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply,Real.exp_log hx,pow_one]
  have hnat : Tendsto (fun N : ℕ=>(N:ℝ)/Real.log N) atTop atTop :=
    hreal.comp tendsto_natCast_atTop_atTop
  have hhalf : Tendsto (fun N : ℕ=>(N:ℝ)/(2*Real.log N)) atTop atTop := by
    have hh := hnat.const_mul_atTop (by norm_num : (0:ℝ)<1/2)
    refine hh.congr' (Eventually.of_forall fun N=>?_)
    change (1/2:ℝ)*((N:ℝ)/Real.log N)=(N:ℝ)/(2*Real.log N)
    ring
  apply tendsto_atTop_mono' atTop _ hhalf
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
  exact box_trueLi_lower hN

/-- Uniform relative normalization transport. The threshold precedes Q,
D and sigma; the primitive positivity gates admit zero-mass families.
All conclusions are multiplicative comparisons of the actual normalizers. -/
theorem uniform_trueTheta_relative_error (epsilon : ℝ) (he : 0<epsilon) :
    ∃N0 : ℕ,4≤N0 ∧ ∀N : ℕ,N0≤N →
      ∀(Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ),
        (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,1<Q/(d:ℝ)) →
        Theta N Q D sigma≤trueTheta N Q D sigma ∧
        trueTheta N Q D sigma≤(1+epsilon)*Theta N Q D sigma ∧
        |trueTheta N Q D sigma-Theta N Q D sigma|≤epsilon*Theta N Q D sigma := by
  have hc : ∀ᶠ N : ℕ in atTop,
      2/Real.log 2≤epsilon*logarithmicIntegral N :=
    (tendsto_literalLi_nat_atTop.const_mul_atTop he).eventually
      (eventually_ge_atTop (2/Real.log 2))
  obtain ⟨T,hT⟩ := eventually_atTop.mp hc
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN Q D sigma hdpos hsigma hlevel
  have hN4 : 4≤N := (le_max_left _ _).trans hN
  have hscalar := hT N ((le_max_right _ _).trans hN)
  have hmean := kernelMean_nonneg (by omega : 0<N) Q D sigma hdpos hsigma hlevel
  have hconstant : 0≤2/Real.log 2 :=
    (div_pos (by norm_num) (Real.log_pos (by norm_num : (1:ℝ)<2))).le
  have hidentity := trueTheta_eq_Theta_add N Q D sigma
  have herror0 : 0≤4*(2/Real.log 2)*kernelMean N Q D sigma := by positivity
  have herror : 4*(2/Real.log 2)*kernelMean N Q D sigma≤
      epsilon*Theta N Q D sigma := by
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hscalar hmean) (by norm_num : (0:ℝ)≤4)
    change 4*(2/Real.log 2)*kernelMean N Q D sigma≤
      epsilon*(4*logarithmicIntegral N*kernelMean N Q D sigma)
    convert hm using 1 <;> ring
  have hdiff : trueTheta N Q D sigma-Theta N Q D sigma=
      4*(2/Real.log 2)*kernelMean N Q D sigma := by linarith only [hidentity]
  refine ⟨by linarith only [hidentity,herror0],?_,?_⟩
  · nlinarith only [hidentity,herror]
  · rw [hdiff,abs_of_nonneg herror0]
    exact herror

end
end ImbalancedChen.P2MarkedThetaLiNormalization
