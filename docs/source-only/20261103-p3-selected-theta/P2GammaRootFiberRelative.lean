import ImbalancedChen.P2GammaSelectedRelativeLogSaving

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
A concrete selected family with ONE actual original rootQ. The filter
preserves an arbitrary keep predicate, the old pair labels and their weights.
It does not claim that a missing causal policy produces this entire family,
or that all original pairs survive the common-Q and residual-domain tests.
Its complementary source is retained by an exact partition identity.
-/
namespace ImbalancedChen.P2GammaRootFiberRelative
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaSelectedPhysicalTheta P2GammaSelectedRelativeLogSaving
open P2GammaRankScaledUpperSource P2GammaRankScaledUpperLogSaving
open P2GammaActualUpperLowRankReduction P2GammaJointRetainedReduction
open P2GammaRetainedSameRhoMother
open P2OriginalU5SmallPartnerRootPayment (rootQ)
open P5OriginalU5CausalFinite (pairSupport)

/-- An ACTUAL root-level fibre with the exact physical residual tests.
No q, conductor, character or error-sign parameter is used in this filter. -/
def rootFiber (N : ℕ) (Qphys : ℝ) (keep : Pair → Prop) : Finset Pair :=
  (pairSupport N).filter (fun t => keep t ∧ rootQ N t = Qphys ∧
    1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧ Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N)

theorem rootFiber_subset (N : ℕ) (Qphys : ℝ) (keep : Pair → Prop) :
    rootFiber N Qphys keep ⊆ pairSupport N := Finset.filter_subset _ _

theorem rootFiber_data {N : ℕ} {Qphys : ℝ} {keep : Pair → Prop} {t : Pair}
    (ht : t ∈ rootFiber N Qphys keep) :
    t ∈ pairSupport N ∧ keep t ∧ rootQ N t = Qphys ∧
      1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧ Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N :=
  Finset.mem_filter.mp ht

/-- Every nonzero extended weight belongs to the literal old-pair source,
passes keep, and uses the same physical rootQ and residual domain. -/
theorem active_rootFiber_weight {N : ℕ} {Qphys : ℝ} {keep : Pair → Prop}
    (sigma : Pair → ℝ) {t : Pair}
    (ht : selectedWeight (rootFiber N Qphys keep) sigma t ≠ 0) :
    t ∈ pairSupport N ∧ keep t ∧ rootQ N t = Qphys ∧
      1 < Qphys/((t.1*t.2 : ℕ) : ℝ) ∧ Qphys/((t.1*t.2 : ℕ) : ℝ) ≤ N := by
  have hm : t ∈ rootFiber N Qphys keep := by
    by_contra hn
    exact ht (by simp only [selectedWeight,if_neg hn])
  exact rootFiber_data hm

/-- Source-preserving physical substitution, for any later finite count,
integral test or arithmetic kernel depending on the original rootQ. -/
theorem rootFiber_physical_test (N : ℕ) (Qphys : ℝ) (keep : Pair → Prop)
    (sigma : Pair → ℝ) (F : ℝ → Pair → ℝ) :
    (∑ t ∈ rootFiber N Qphys keep,sigma t * F (rootQ N t) t) =
      ∑ t ∈ rootFiber N Qphys keep,sigma t * F Qphys t := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [(rootFiber_data ht).2.2.1]

/-- All original nonselected pairs remain in an explicit complementary
term. A common-Q filter is not a proof of coverage of the whole source. -/
theorem rootFiber_residual_partition (N : ℕ) (Qphys : ℝ) (keep : Pair → Prop)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) (sigma : Pair → ℝ) :
    selectedResidual N moduli rho T (pairSupport N) sigma =
      selectedResidual N moduli rho T (rootFiber N Qphys keep) sigma +
        selectedResidual N moduli rho T (pairSupport N \ rootFiber N Qphys keep) sigma :=
  selectedResidual_partition (rootFiber_subset N Qphys keep) moduli rho T sigma

/-- No common-Q identity or Theta comparison is supplied by the caller:
the selected family and existing physical normalizer supply both. The
quantitative mass alternative remains EXPLICIT and must still be proved
for the desired causal strategy; mere positivity does not discharge it. -/
theorem eventually_rootFiber_rank_relative (A r : ℕ) (lambda : ℝ) (hlambda : 0 < lambda)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Qphys height : ℝ),0 < height →
      ∀ (keep : Pair → Prop) (sigma : Pair → ℝ),
      (∀ t ∈ rootFiber N Qphys keep,0 ≤ sigma t ∧ sigma t ≤ height) →
      (reciprocalMass (rootFiber N Qphys keep) sigma = 0 ∨
        lambda*height/(Real.log (N : ℝ))^r ≤ reciprocalMass (rootFiber N Qphys keep) sigma) →
      |rankResidual N kappa nu epsilon retain cap k (rootFiber N Qphys keep) sigma| ≤
        eta*selectedTheta N Qphys (rootFiber N Qphys keep) sigma/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_selected_rank_relative A r lambda hlambda kappa hk0 hk eta heta]
    with N hN
  intro k nu epsilon hnu hgap retain cap Qphys height hh keep sigma hs hm
  exact hN k nu epsilon hnu hgap retain cap (rootFiber N Qphys keep)
    (rootFiber_subset N Qphys keep) Qphys height hh sigma hs
    (fun t ht => (rootFiber_data ht).2.2.2) hm

theorem selectedGamma_rank_split {N : ℕ} {S : Finset Pair} (hS : S ⊆ pairSupport N)
    (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap k : ℕ) (moduli : Finset ℕ)
    (sigma : Pair → ℝ) :
    selectedGamma N moduli (fullUpperRho N nu epsilon retain cap) S sigma =
      selectedGamma N moduli (rankUpperRho N nu epsilon retain cap k) S sigma +
        selectedGamma N moduli (rankRemainder N nu epsilon retain cap k) S sigma := by
  simp only [selectedGamma_eq_original hS]
  exact originalJointGamma_rank_split N nu epsilon retain cap k moduli (selectedWeight S sigma)

/-- Actual compact upper policy, original physical carrier, unchanged high
branch and empty lane. This is a relative estimate only on the explicitly
constructed root fibre and its quantitative nondegenerate mass domain. -/
theorem eventually_actualCompact_rootFiber_relative (A r : ℕ)
    (lambda : ℝ) (hlambda : 0 < lambda) (kappa : ℝ)
    (hk0 : 0 < kappa) (hk : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (e h : ℝ) (m cap : ℕ) (Qphys height : ℝ),0 < height →
      ∀ (keep : Pair → Prop) (sigma : Pair → ℝ),
      (∀ t ∈ rootFiber N Qphys keep,0 ≤ sigma t ∧ sigma t ≤ height) →
      (reciprocalMass (rootFiber N Qphys keep) sigma = 0 ∨
        lambda*height/(Real.log (N : ℝ))^r ≤ reciprocalMass (rootFiber N Qphys keep) sigma) →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      let moduli := physicalUpperModuli N nu epsilon retain cap
      let S := rootFiber N Qphys keep
      |selectedGamma N moduli (fullUpperRho N nu epsilon retain cap) S sigma -
        selectedGamma N moduli (rankRemainder N nu epsilon retain cap k) S sigma -
        selectedEmpty N moduli (rankUpperRho N nu epsilon retain cap k)
          ((N : ℝ)^(1-kappa)) S sigma| ≤
        eta*selectedTheta N Qphys S sigma/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_rootFiber_rank_relative A r lambda hlambda kappa hk0 hk eta heta]
    with N hN
  intro k nu epsilon hnu hgap e h m cap Qphys height hh keep sigma hs hm
  dsimp only
  rw [selectedGamma_rank_split (rootFiber_subset N Qphys keep),add_sub_cancel_right]
  exact hN k nu epsilon hnu hgap
    (actualExtendedThirdCompactUpperPolicy e h m N false) cap Qphys height hh keep sigma hs hm

/-- A primitive way to discharge the quantitative mass input, when an
actual subfamily with pointwise weight and reciprocal-density witnesses
has been supplied. No such witness is invented for the missing strategy. -/
theorem rootFiber_mass_floor_of_subfamily {N : ℕ} (hN : 2 ≤ N)
    (Qphys : ℝ) (keep : Pair → Prop) (U : Finset Pair)
    (hU : U ⊆ rootFiber N Qphys keep) (sigma : Pair → ℝ)
    (hs : ∀ t ∈ rootFiber N Qphys keep,0 ≤ sigma t)
    (a height lambda : ℝ) (ha : 0 < a) (hh : 0 ≤ height) (r : ℕ)
    (hweight : ∀ t ∈ U,a*height ≤ sigma t)
    (hm : lambda/(a*(Real.log (N : ℝ))^r) ≤
      ∑ t ∈ U,1/((t.1*t.2 : ℕ) : ℝ)) :
    lambda*height/(Real.log (N : ℝ))^r ≤ reciprocalMass (rootFiber N Qphys keep) sigma := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ = a*height*(lambda/(a*(Real.log (N : ℝ))^r)) := by
      field_simp [ha.ne',hlog.ne'] <;> ring
    _ ≤ a*height*(∑ t ∈ U,1/((t.1*t.2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg ha.le hh)
    _ ≤ _ := reciprocalMass_of_subfamily hU sigma hs a height hweight

end
end ImbalancedChen.P2GammaRootFiberRelative
