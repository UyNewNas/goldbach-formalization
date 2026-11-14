import ImbalancedChen.Part3OriginalRegularCumulativeMeasures
import ImbalancedChen.Part3OriginalHolomorphicBothCusps

/-! The three positive forms of the manuscript at its two observing
cusps, with one constant preceding all spectral and arithmetic choices. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularThreeMeasures20261113
open Real Set MeasureTheory Finset
open scoped MatrixGroups UpperHalfPlane InnerProductSpace
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalRegularPacketTest20261113 (Dyadic energy energy_nonneg)
open OriginalRegularBaseCumulative20261113 (baseTerm lineTerm)
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis weights shell)
open OriginalHolomorphicBothCusps20261113 (manuscript_holomorphic_both_cusps)
open OriginalRegularCumulativeMeasures20261113 (manuscript_weight_zero)

/-- Native K-Whittaker coefficients, every incoming channel with
dt/(4π), and all Petersson weights k≥2 with k−1≤K. The holomorphic
form is the positive-frequency form, and the other two are signed. -/
theorem manuscript_regular_three (e : ℝ) (he : 0<e) : ∃ C : ℝ,0<C ∧
    ∀ (q : ℕ) [NeZero q] (one neg : Bool) {K L : ℝ},1≤K → 1/2≤L →
    ∀ (S : Finset ℕ) (a : ℕ→ℂ),Dyadic L S →
      Summable (baseTerm q one neg K S a) ∧
      (∑' i,baseTerm q one neg K S a i)≤C*(K^2+L^(1+e)/(q:ℝ))*energy S a ∧
      IntegrableOn (lineTerm q one neg S a) (Icc (-K) K) ∧
      (∫ t in Icc (-K) K,lineTerm q one neg S a t)≤C*(K^2+L^(1+e)/(q:ℝ))*energy S a ∧
      ∀ (bases : ∀ j,WeightBasis q j),
        (∑ j∈weights K,shell q j one S a (bases j))≤C*(K^2+L^(1+e)/(q:ℝ))*energy S a := by
  obtain ⟨D,d0,Z⟩ := manuscript_weight_zero e he
  obtain ⟨H,h0,W⟩ := manuscript_holomorphic_both_cusps e he
  refine ⟨max D H,d0.trans_le (le_max_left _ _),?_⟩
  intro q inst one neg K L k1 hL S a bd
  have lp : 0≤L := by linarith only [hL]
  have R : 0≤K^2+L^(1+e)/(q:ℝ) := add_nonneg (sq_nonneg K) (div_nonneg (rpow_nonneg lp _) (Nat.cast_nonneg q))
  have pay {A : ℝ} (h : A≤max D H) := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h R) (energy_nonneg S a)
  obtain ⟨summ,dis,inte,line⟩ := Z q one neg k1 hL S a bd
  exact ⟨summ,dis.trans (pay (le_max_left _ _)),inte,line.trans (pay (le_max_left _ _)),
    fun bases => (W q one k1 hL S a bd bases).trans (pay (le_max_right _ _))⟩

end ImbalancedChen.Part3.OriginalRegularThreeMeasures20261113
end
