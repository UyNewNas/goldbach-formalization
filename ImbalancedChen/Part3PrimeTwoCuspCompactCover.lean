import ImbalancedChen.Part3PrimeExplicitCosetGreenTrace
import ImbalancedChen.Part3PrimeHighCuspQuotientSeparation
import ImbalancedChen.Part3ActualModularCutoffCompactSupport

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The complement of the TWO actual normalized strict cusp neighborhoods
has a lift in the existing full finite-coset compact carrier at height pY.
The full modular reduction and actual prime section comparison supply
the cover, including every boundary orbit. No reduced-carrier or
almost-everywhere exhaustion is substituted for this pointwise claim. -/

noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups Pointwise
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualModularCutoffCompactSupport20261025a
open ImbalancedChen.Part3.PrimeStandardCosets20261026b
open ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
open ImbalancedChen.Part3.PrimeTopFrickeMatrix20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b

namespace ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b

def twoCuspTruncation (p : ℕ) (hp : p.Prime) (Y : ℝ) : Set (Gamma0OrbitSpace p) :=
  (infinityHighNeighborhood p Y ∪ zeroHighNeighborhood p hp Y)ᶜ

/-- The chosen inverse quotient section and the explicit prime section
give the SAME actual orbit, by an exhibited Gamma0 matrix. -/
theorem canonical_prime_section_projection (p : ℕ) [NeZero p]
    (j : Branch p) (w : UpperHalfPlane) :
    orbitProjection p (inverseClassRep p (standardClass p j) • w) =
      orbitProjection p (standardRepresentative p j • w) := by
  rw [← standardSectionGamma_mul_rep p j, mul_smul]
  exact orbitProjection_smul p (standardSectionGamma p j) _

/-- Above pY the identity branch is high at infinity and each of the p
finite branches is high in the width-normalized Fricke chart at zero.
The finite branch height is literally Im(w)/p. -/
theorem prime_standard_high_mem_two_tails (p : ℕ) (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (j : Branch p) (w : UpperHalfPlane)
    (hw : (p : ℝ) * Y < w.im) :
    orbitProjection p (standardRepresentative p j • w) ∈
      infinityHighNeighborhood p Y ∪ zeroHighNeighborhood p hp Y := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  cases j with
  | none =>
      apply Or.inl
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hY0 : 0 ≤ Y := le_trans (by norm_num) hY
      have hYp : Y ≤ (p : ℝ) * Y := by nlinarith
      refine ⟨w, hYp.trans_lt hw, ?_⟩
      simp only [standardRepresentative, one_smul]
  | some r =>
      apply Or.inr
      refine ⟨branchSL p hp.pos (some r) • w, ?_, ?_⟩
      · change Y < (branchSL p hp.pos (some r) • w).im
        rw [finite_branch_height]
        exact (lt_div_iff₀ hpR).mpr (by simpa only [mul_comm] using hw)
      · exact congrArg (orbitProjection p) (standardRepresentative_some_action p hp r w).symm

/-- An actual Gamma0 translate of EVERY point outside the two tails
lies in the full compact finite-coset carrier truncated at pY. -/
theorem outside_two_tails_compact_gamma_cover (p : ℕ) [NeZero p]
    (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (z : UpperHalfPlane)
    (hz : orbitProjection p z ∈ twoCuspTruncation p hp Y) :
    ∃ γ : CongruenceSubgroup.Gamma0 p,
      γ • z ∈ truncatedGammaCarrier p ((p : ℝ) * Y) := by
  obtain ⟨γ, hγ⟩ := exists_gamma0_smul_mem_carrier p z
  obtain ⟨q, hq⟩ := mem_iUnion.mp hγ
  obtain ⟨w, hw, hweq⟩ := hq
  obtain ⟨j, hj⟩ := (standardClassEquiv p hp).surjective q
  have hwheight : w.im ≤ (p : ℝ) * Y := by
    by_contra h
    have ht := prime_standard_high_mem_two_tails p hp Y hY j w (lt_of_not_ge h)
    have heq : orbitProjection p z = orbitProjection p (standardRepresentative p j • w) := by
      calc
        orbitProjection p z = orbitProjection p (γ • z) := (orbitProjection_smul p γ z).symm
        _ = orbitProjection p (inverseClassRep p q • w) := congrArg (orbitProjection p) hweq.symm
        _ = orbitProjection p (standardRepresentative p j • w) := by
          rw [← hj]
          exact canonical_prime_section_projection p j w
    apply hz
    rwa [heq]
  refine ⟨γ, mem_iUnion.mpr ⟨q, ?_⟩⟩
  exact ⟨w, ⟨hw, hwheight⟩, hweq⟩

/-- Genuine pointwise quotient cover, rather than an almost-everywhere
statement about the reduced carrier. -/
theorem twoCuspTruncation_subset_compact_carrier (p : ℕ) [NeZero p]
    (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    twoCuspTruncation p hp Y ⊆ quotientTruncatedCarrier p ((p : ℝ) * Y) := by
  intro q
  refine Quotient.inductionOn q (fun z hz => ?_)
  obtain ⟨γ, hγ⟩ := outside_two_tails_compact_gamma_cover p hp Y hY z hz
  exact ⟨γ • z, hγ, orbitProjection_smul p γ z⟩

end ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b
