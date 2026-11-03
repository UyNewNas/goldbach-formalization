import ImbalancedChen.P2GammaSelectedPhysicalTheta

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
A genuine relative-Theta consequence of the previous ACTUAL joint theorem,
on a displayed quantitative reciprocal-mass domain. The absolute supplier
is invoked at height one and higher log accuracy. Exact homogeneity lets
height vary AFTER the common threshold, including arbitrarily small height.
This does not assert that every positive family satisfies the mass floor.
-/
namespace ImbalancedChen.P2GammaSelectedRelativeLogSaving
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaSelectedPhysicalTheta P2GammaRankScaledUpperLogSaving
open P2GammaRankScaledUpperSource P2GammaActualUpperLowRankReduction
open MathlibNt.SieveTheory.SingularSeries
open P5OriginalU5CausalFinite (pairSupport)

/-- The actual selected rank-k remainder, on the original physical carrier. -/
def rankResidual (N : ℕ) (kappa nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap k : ℕ) (S : Finset Pair) (sigma : Pair → ℝ) : ℝ :=
  selectedResidual N (physicalUpperModuli N nu epsilon retain cap)
    (rankUpperRho N nu epsilon retain cap k) ((N : ℝ)^(1-kappa)) S sigma

/-- ALL later amplitudes are permitted. This strengthens the quantifier
order of a fixed-height use, without assuming a new analytic estimate. -/
theorem eventually_selected_rank_height_logAccuracy (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (S : Finset Pair), S ⊆ pairSupport N →
      ∀ height : ℝ,0 < height → ∀ sigma : Pair → ℝ,
      (∀ t ∈ S,0 ≤ sigma t ∧ sigma t ≤ height) →
      |rankResidual N kappa nu epsilon retain cap k S sigma| ≤
        eta*height*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_rank_physical_logAccuracy 1 (by norm_num) A
    kappa hk0 hk eta heta] with N hN
  intro k nu epsilon hnu hgap retain cap S hS height hheight sigma hs
  let w := selectedWeight S (fun t => sigma t/height)
  have hw : ∀ t ∈ pairSupport N,0 ≤ w t ∧ w t ≤ 1 := by
    intro t ht
    by_cases htS : t ∈ S
    · simp only [w,selectedWeight,if_pos htS]
      exact ⟨div_nonneg (hs t htS).1 hheight.le,
        (div_le_one hheight).mpr (hs t htS).2⟩
    · simp only [w,selectedWeight,if_neg htS]; norm_num
  have h := hN k nu epsilon hnu hgap retain cap w hw
  have hsmall : |rankResidual N kappa nu epsilon retain cap k S
      (fun t => sigma t/height)| ≤ eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
    rw [rankResidual,selectedResidual_eq_original hS]
    exact h
  have heq : rankResidual N kappa nu epsilon retain cap k S sigma =
      height*rankResidual N kappa nu epsilon retain cap k S (fun t => sigma t/height) := by
    unfold rankResidual
    rw [← selectedResidual_smul]
    congr 1
    funext t
    field_simp [hheight.ne'] <;> ring
  rw [heq,abs_mul,abs_of_pos hheight]
  exact (mul_le_mul_of_nonneg_left hsmall hheight.le).trans_eq (by ring)

/-- Exact payment algebra: r logarithms pay the reciprocal-mass floor,
and TWO MORE pay the original Theta normalization. -/
theorem relative_budget {N : ℕ} {ell height mass theta E eta lambda : ℝ}
    (A r : ℕ) (hell : 0 < ell) (heta : 0 ≤ eta)
    (hE : |E| ≤ (eta*(2*liuUniversalProduct)*lambda)*height*(N : ℝ)/ell^(A+r+2))
    (hm : lambda*height/ell^r ≤ mass)
    (htheta : (2*liuUniversalProduct*(N : ℝ)/ell^2)*mass ≤ theta) :
    |E| ≤ eta*theta/ell^A := by
  have hU := liuUniversalProduct_pos
  calc
    _ ≤ (eta*(2*liuUniversalProduct)*lambda)*height*(N : ℝ)/ell^(A+r+2) := hE
    _ = (eta/ell^A)*((2*liuUniversalProduct*(N : ℝ)/ell^2)*
        (lambda*height/ell^r)) := by
      simp only [pow_add]
      field_simp [hell.ne'] <;> ring
    _ ≤ (eta/ell^A)*((2*liuUniversalProduct*(N : ℝ)/ell^2)*mass) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)
    _ ≤ (eta/ell^A)*theta := mul_le_mul_of_nonneg_left htheta (by positivity)
    _ = _ := by ring

/-- True same-Q relative error for the actual selected nonempty rank lane.
The mass hypothesis is explicit, scale-invariant, and NOT implied by
Theta>0. Only levels on S are required; unselected pairs impose no Q test.
The zero-mass alternative is settled without dividing by Theta or height.
-/
theorem eventually_selected_rank_relative (A r : ℕ) (lambda : ℝ) (hlambda : 0 < lambda)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (S : Finset Pair), S ⊆ pairSupport N →
      ∀ (Qphys height : ℝ),0 < height → ∀ sigma : Pair → ℝ,
      (∀ t ∈ S,0 ≤ sigma t ∧ sigma t ≤ height) →
      (∀ t ∈ S,1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧
        Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N) →
      (reciprocalMass S sigma = 0 ∨
        lambda*height/(Real.log (N : ℝ))^r ≤ reciprocalMass S sigma) →
      |rankResidual N kappa nu epsilon retain cap k S sigma| ≤
        eta*selectedTheta N Qphys S sigma/(Real.log (N : ℝ))^A := by
  have htol : 0 < eta*(2*liuUniversalProduct)*lambda := by
    have hU := liuUniversalProduct_pos
    positivity
  filter_upwards [eventually_selected_rank_height_logAccuracy (A+r+2) kappa hk0 hk
    (eta*(2*liuUniversalProduct)*lambda) htol,
    eventually_ge_atTop (4 : ℕ)] with N habs hN
  intro k nu epsilon hnu hgap retain cap S hS Qphys height hheight sigma hs hQ hmass
  have hs0 : ∀ t ∈ S,0 ≤ sigma t := fun t ht => (hs t ht).1
  rcases hmass with hz | hmass
  · have hweights := (reciprocalMass_zero_iff S sigma hS hs0).mp hz
    have herror : rankResidual N kappa nu epsilon retain cap k S sigma = 0 :=
      selectedResidual_zero N _ _ _ S sigma hweights
    have htzero := (selectedTheta_zero_iff hN Qphys S sigma hS hs0 hQ).mpr hz
    simp only [herror,abs_zero,htzero,mul_zero,zero_div,le_refl]
  · have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact relative_budget A r hlog heta.le
      (habs k nu epsilon hnu hgap retain cap S hS height hheight sigma hs)
      hmass (selectedTheta_lower hN Qphys S sigma hS hs0 hQ)

/-- The nondegenerate branch really has positive physical Theta, including
when its amplitude tends to zero with N. -/
theorem selectedTheta_pos_of_mass_floor {N : ℕ} (hN : 4 ≤ N)
    (Qphys height lambda : ℝ) (hh : 0 < height) (hl : 0 < lambda)
    (r : ℕ) (S : Finset Pair) (sigma : Pair → ℝ) (hS : S ⊆ pairSupport N)
    (hs : ∀ t ∈ S,0 ≤ sigma t)
    (hQ : ∀ t ∈ S,1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧ Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N)
    (hm : lambda*height/(Real.log (N : ℝ))^r ≤ reciprocalMass S sigma) :
    0 < selectedTheta N Qphys S sigma := by
  have hU := liuUniversalProduct_pos
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass : 0 < reciprocalMass S sigma := (by positivity :
    0 < lambda*height/(Real.log (N : ℝ))^r).trans_le hm
  exact (by positivity : 0 < (2*liuUniversalProduct*(N : ℝ)/(Real.log (N : ℝ))^2)*
    reciprocalMass S sigma).trans_le (selectedTheta_lower hN Qphys S sigma hS hs hQ)

end
end ImbalancedChen.P2GammaSelectedRelativeLogSaving
