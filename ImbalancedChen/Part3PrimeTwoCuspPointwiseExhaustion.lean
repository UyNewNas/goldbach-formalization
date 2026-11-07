import ImbalancedChen.Part3PrimeTwoCuspCompactTruncation
import ImbalancedChen.Part3ActualParabolicHighSeedLocalFinite

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every actual orbit has bounded normalized cusp heights. Integral c=0
decks preserve height; c!=0 gives height <=1/Im(z). Apply this bound both
to z and W_p z to obtain a pointwise monotone compact exhaustion of the
FULL quotient by the literal complements of its two strict cusp tails.
No conull-carrier restriction or all-cusps compactness premise is used. -/

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.ActualParabolicHighSeedLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0ActualHighCuspTail20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactTruncation20261026b

namespace ImbalancedChen.Part3.PrimeTwoCuspPointwiseExhaustion20261026b

def representativeHeightBound (z : UpperHalfPlane) : ℝ := max z.im z.im⁻¹

/-- A genuine uniform bound over ALL actual Gamma0 decks of a fixed
point, derived from integer lower-left arithmetic and parabolic action. -/
theorem gamma0_height_le_representative_bound (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    (γ • z).im ≤ representativeHeightBound z := by
  by_cases hc : (γ : SL(2, ℤ)) 1 0 = 0
  · obtain ⟨k, hk⟩ := parabolic_action_integer N (⟨γ, hc⟩ : gammaInfinity N)
    have he : γ • z = translate k z := hk z
    rw [he, translate_im]
    exact le_max_left _ _
  · have hb := im_smul_mul_im_le_one (γ : SL(2, ℤ)) hc z
    have hd : (γ • z).im ≤ z.im⁻¹ := by
      simpa only [one_div] using (le_div_iff₀ z.im_pos).mpr hb
    exact hd.trans (le_max_right _ _)

theorem not_mem_infinityHigh_of_bound_le (N : ℕ) (z : UpperHalfPlane)
    (Y : ℝ) (hY : representativeHeightBound z ≤ Y) :
    orbitProjection N z ∉ infinityHighNeighborhood N Y := by
  rintro ⟨w, hw, he⟩
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact he)
  have hb := gamma0_height_le_representative_bound N γ z
  rw [hγ] at hb
  exact (not_lt_of_ge (hb.trans hY)) hw

theorem not_mem_zeroHigh_of_fricke_bound_le (p : ℕ) (hp : p.Prime)
    (z : UpperHalfPlane) (Y : ℝ)
    (hY : representativeHeightBound (frickeSL p hp.pos • z) ≤ Y) :
    orbitProjection p z ∉ zeroHighNeighborhood p hp Y := by
  rintro ⟨w, hw, he⟩
  have h := congrArg (quotientFricke p hp.pos) he
  have hproj : orbitProjection p w = orbitProjection p (frickeSL p hp.pos • z) := by
    simpa only [quotientFricke_projection, frickeSL_action_involutive p hp.pos] using h
  exact not_mem_infinityHigh_of_bound_le p (frickeSL p hp.pos • z) Y hY ⟨w, hw, hproj⟩

/-- The explicit finite threshold uses both original normalized charts. -/
theorem projection_mem_truncation_of_two_bounds (p : ℕ) (hp : p.Prime)
    (z : UpperHalfPlane) (Y : ℝ)
    (h∞ : representativeHeightBound z ≤ Y)
    (h₀ : representativeHeightBound (frickeSL p hp.pos • z) ≤ Y) :
    orbitProjection p z ∈ twoCuspTruncation p hp Y := by
  rintro (h | h)
  · exact not_mem_infinityHigh_of_bound_le p z Y h∞ h
  · exact not_mem_zeroHigh_of_fricke_bound_le p hp z Y h₀ h

theorem twoCuspTruncation_mono (p : ℕ) (hp : p.Prime) :
    Monotone (twoCuspTruncation p hp) := by
  intro Y Z hYZ q hq
  rintro (⟨w, hw, he⟩ | ⟨w, hw, he⟩)
  · exact hq (Or.inl ⟨w, hYZ.trans_lt hw, he⟩)
  · exact hq (Or.inr ⟨w, hYZ.trans_lt hw, he⟩)

/-- Every quotient point, including the exceptional boundary orbits of
any reduced-carrier construction, eventually belongs to these cores. -/
theorem eventually_mem_twoCuspTruncation (p : ℕ) (hp : p.Prime)
    (q : Gamma0OrbitSpace p) :
    ∀ᶠ Y : ℝ in atTop, q ∈ twoCuspTruncation p hp Y := by
  refine Quotient.inductionOn q (fun z => ?_)
  filter_upwards [eventually_ge_atTop (representativeHeightBound z),
    eventually_ge_atTop (representativeHeightBound (frickeSL p hp.pos • z))] with Y h∞ h₀
  exact projection_mem_truncation_of_two_bounds p hp z Y h∞ h₀

theorem twoCuspTruncation_iUnion_eq_univ (p : ℕ) (hp : p.Prime) :
    (⋃ Y : ℝ, twoCuspTruncation p hp (max 1 Y)) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨Y, hY⟩ := (eventually_mem_twoCuspTruncation p hp q).exists
  exact mem_iUnion.mpr ⟨Y, twoCuspTruncation_mono p hp (le_max_right 1 Y) hY⟩

/-- The exhausting family consists of actual compact subsets throughout. -/
theorem normalized_two_cusp_compact_exhaustion (p : ℕ) [NeZero p] (hp : p.Prime) :
    (∀ Y : ℝ, IsCompact (twoCuspTruncation p hp (max 1 Y))) ∧
      (⋃ Y : ℝ, twoCuspTruncation p hp (max 1 Y)) = univ :=
  ⟨fun Y => twoCuspTruncation_isCompact p hp (max 1 Y) (le_max_left _ _),
    twoCuspTruncation_iUnion_eq_univ p hp⟩

end ImbalancedChen.Part3.PrimeTwoCuspPointwiseExhaustion20261026b
