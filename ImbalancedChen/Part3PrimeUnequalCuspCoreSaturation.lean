import ImbalancedChen.Part3PrimeTwoCuspPointwiseExhaustion
import ImbalancedChen.Part3Gamma0TruncatedCosetMeasure
import ImbalancedChen.Part3LevelOldformFrickeIdentity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The FULL finite-coset truncated carrier has actual orbit image exactly
the complement of infinity height>T and normalized zero height>T/p,
for T>=p prime. This is a saturation statement about the full carrier;
the canonical reduced quotientCore is treated separately. -/

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups Pointwise
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.LevelOldformFricke20261026a
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.Gamma0ModularFiniteCoverMeasure20261025a
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualModularCutoffCompactSupport20261025a
open ImbalancedChen.Part3.PrimeTwoCuspPointwiseExhaustion20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b
open ImbalancedChen.Part3.PrimeStandardCosets20261026b
open ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
open ImbalancedChen.Part3.PrimeTopFrickeMatrix20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b

namespace ImbalancedChen.Part3.PrimeUnequalCuspCoreSaturation20261026b

def unequalCuspTruncation (p : ℕ) (hp : p.Prime) (T : ℝ) : Set (Gamma0OrbitSpace p) :=
  (infinityHighNeighborhood p T ∪ zeroHighNeighborhood p hp (T / (p : ℝ)))ᶜ

/-- The normalized Fricke height is the actual integral S-height divided
by the level, before any quotient or cusp representatives are chosen. -/
theorem fricke_height_eq_S_height_div (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    (frickeSL N hN • z).im = (ModularGroup.S • z).im / (N : ℝ) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : ((frickeSL N hN • z : UpperHalfPlane) : ℂ) =
      ((ModularGroup.S • z : UpperHalfPlane) : ℂ) / (N : ℝ) := by
    rw [fricke_action_coe, UpperHalfPlane.modular_S_smul]
    simp only [Complex.ofReal_natCast]
    field_simp [hNC, z.ne_zero]
    <;> ring
  simpa only [Complex.div_ofReal_im] using congrArg Complex.im he

/-- T>=2 and the actual modular-cell height floor suffice; no maximal
height theorem or unproved fundamental-domain denominator bound is used. -/
theorem integral_height_le_truncation (T : ℝ) (hT : 2 ≤ T)
    (w : UpperHalfPlane) (hw : w ∈ truncatedModularFD T) (g : SL(2, ℤ)) :
    (g • w).im ≤ T := by
  have hfloor : (1 : ℝ) / 2 < w.im := modularFD_half_lt_im hw.1
  have hinv : w.im⁻¹ < 2 := by
    rw [inv_lt_iff₀ w.im_pos]
    linarith
  have hcap : representativeHeightBound w ≤ T := max_le hw.2 (hinv.le.trans hT)
  exact (gamma0_height_le_representative_bound 1 (levelOneMatrix g) w).trans hcap

theorem fricke_integral_height_le_truncation_div (N : ℕ) (hN : 0 < N)
    (T : ℝ) (hT : 2 ≤ T) (w : UpperHalfPlane)
    (hw : w ∈ truncatedModularFD T) (g : SL(2, ℤ)) :
    (frickeSL N hN • (g • w)).im ≤ T / (N : ℝ) := by
  rw [fricke_height_eq_S_height_div]
  have hg := integral_height_le_truncation T hT w hw (ModularGroup.S * g)
  rw [mul_smul] at hg
  exact div_le_div_of_nonneg_right hg (by exact_mod_cast hN.le)

/-- Every actual orbit in a LOW full carrier cell avoids both uneven
tails. The second exclusion retains the actual 1/p Fricke factor. -/
theorem full_truncated_carrier_avoids_unequal_tails (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) (hT : (p : ℝ) ≤ T) :
    quotientTruncatedCarrier p T ⊆ unequalCuspTruncation p hp T := by
  have h2T : (2 : ℝ) ≤ T := (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p).trans hT
  rintro q ⟨z, hz, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz
  obtain ⟨w, hw, rfl⟩ := hj
  rintro (⟨v, hv, he⟩ | ⟨v, hv, he⟩)
  · obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact he)
    have ha : ((γ : SL(2, ℤ)) * inverseClassRep p j) • w = v := by
      simpa only [mul_smul] using hγ
    have hb := integral_height_le_truncation T h2T w hw
      ((γ : SL(2, ℤ)) * inverseClassRep p j)
    rw [ha] at hb
    exact (not_lt_of_ge hb) hv
  · obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact he)
    have ha : frickeSL p hp.pos • (((γ : SL(2, ℤ)) * inverseClassRep p j) • w) = v := by
      rw [mul_smul]
      change frickeSL p hp.pos • (γ • (inverseClassRep p j • w)) = v
      rw [hγ, frickeSL_action_involutive p hp.pos]
    have hb := fricke_integral_height_le_truncation_div p hp.pos T h2T w hw
      ((γ : SL(2, ℤ)) * inverseClassRep p j)
    rw [ha] at hb
    exact (not_lt_of_ge hb) hv

/-- The prime section has TWO genuinely different normalized heights. -/
theorem prime_standard_high_mem_unequal_tails (p : ℕ) (hp : p.Prime)
    (T : ℝ) (j : Branch p) (w : UpperHalfPlane) (hw : T < w.im) :
    orbitProjection p (standardRepresentative p j • w) ∈
      infinityHighNeighborhood p T ∪ zeroHighNeighborhood p hp (T / (p : ℝ)) := by
  cases j with
  | none =>
      exact Or.inl ⟨w, hw, by simp only [standardRepresentative, one_smul]⟩
  | some r =>
      apply Or.inr
      refine ⟨branchSL p hp.pos (some r) • w, ?_, ?_⟩
      · change T / (p : ℝ) < (branchSL p hp.pos (some r) • w).im
        rw [finite_branch_height]
        exact div_lt_div_of_pos_right hw (by exact_mod_cast hp.pos)
      · exact congrArg (orbitProjection p) (standardRepresentative_some_action p hp r w).symm

theorem unequal_truncation_subset_full_carrier (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) :
    unequalCuspTruncation p hp T ⊆ quotientTruncatedCarrier p T := by
  intro q
  refine Quotient.inductionOn q (fun z hz => ?_)
  obtain ⟨γ, hγ⟩ := exists_gamma0_smul_mem_carrier p z
  obtain ⟨a, ha⟩ := mem_iUnion.mp hγ
  obtain ⟨w, hw, hweq⟩ := ha
  obtain ⟨j, hj⟩ := (standardClassEquiv p hp).surjective a
  have hwT : w.im ≤ T := by
    by_contra h
    have ht := prime_standard_high_mem_unequal_tails p hp T j w (lt_of_not_ge h)
    have he : orbitProjection p z = orbitProjection p (standardRepresentative p j • w) := by
      calc
        _ = orbitProjection p (γ • z) := (orbitProjection_smul p γ z).symm
        _ = orbitProjection p (inverseClassRep p a • w) := congrArg (orbitProjection p) hweq.symm
        _ = _ := by rw [← hj]; exact canonical_prime_section_projection p j w
    apply hz
    rwa [he]
  exact ⟨γ • z, mem_iUnion.mpr ⟨a, w, ⟨hw, hwT⟩, hweq⟩, orbitProjection_smul p γ z⟩

/-- Exact saturation for the FULL carrier; no pointwise reduced-section
identity is asserted here. T=p (zero normalized height one) is included. -/
theorem full_truncated_carrier_eq_unequal_truncation (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) (hT : (p : ℝ) ≤ T) :
    quotientTruncatedCarrier p T = unequalCuspTruncation p hp T :=
  Subset.antisymm (full_truncated_carrier_avoids_unequal_tails p hp T hT)
    (unequal_truncation_subset_full_carrier p hp T)

end ImbalancedChen.Part3.PrimeUnequalCuspCoreSaturation20261026b
