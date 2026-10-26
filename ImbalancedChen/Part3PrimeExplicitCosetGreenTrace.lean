import ImbalancedChen.Part3PrimeTopFrickeMatrixIdentity
import ImbalancedChen.Part3Gamma0FiniteCosetGreenTrace

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The ORIGINAL finite current trace is reindexed into its literal prime
left-coset representatives I and S*T^r. The relative Gamma0 matrix between
the chosen quotient section and this explicit section is constructed from
quotient equality. Actual function invariance, before differentiation,
then identifies their Green forms. Each finite branch becomes the genuine
Fricke pullback at B_r z=(z+r)/p with tangent v/p. Neither current
invariance nor an explicit-section trace identity is an input. No held
standard-cell side theorem, cusp classification or spectral measure is used.
-/

noncomputable section
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.PrimeStandardCosets20261026b
open ImbalancedChen.Part3.PrimeTopFrickeMatrix20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
open ImbalancedChen.Part3.Gamma0FiniteCosetGreenTrace20261026b
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

/-- Actual section-changing matrix, in Gamma0 by the original quotient relation. -/
def standardSectionGamma (p : ℕ) [NeZero p] (j : Branch p) :
    CongruenceSubgroup.Gamma0 p :=
  ⟨inverseClassRep p (standardClass p j) * (standardRepresentative p j)⁻¹, by
    have hq : (QuotientGroup.mk (Quotient.out (standardClass p j)) : gamma0Classes p) =
        QuotientGroup.mk ((standardRepresentative p j)⁻¹) :=
      Quotient.out_eq' (standardClass p j)
    simpa only [inverseClassRep] using QuotientGroup.eq.mp hq⟩

theorem standardSectionGamma_mul_rep (p : ℕ) [NeZero p] (j : Branch p) :
    (standardSectionGamma p j : SL(2, ℤ)) * standardRepresentative p j =
      inverseClassRep p (standardClass p j) := by
  change (inverseClassRep p (standardClass p j) * (standardRepresentative p j)⁻¹) *
    standardRepresentative p j = _
  group

/-- The local FIELD identity supplies both value and derivative equality. -/
theorem canonical_pulledField_eq_standard_eventually (p : ℕ) [NeZero p]
    (j : Branch p) (F : ℂ → ℂ)
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z) (z : UpperHalfPlane) :
    pulledField (inverseClassRep p (standardClass p j)) F =ᶠ[𝓝 (z : ℂ)]
      pulledField (standardRepresentative p j) F := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  let W : UpperHalfPlane := ⟨w, hw⟩
  change pulledField _ F (W : ℂ) = pulledField _ F (W : ℂ)
  simp only [pulledField, slMap_eq_action, realSL_action_int]
  have h := hFI (standardSectionGamma p j) (standardRepresentative p j • W)
  change F (((standardSectionGamma p j : SL(2, ℤ)) •
    (standardRepresentative p j • W) : UpperHalfPlane) : ℂ) = _ at h
  rw [← mul_smul, standardSectionGamma_mul_rep] at h
  exact h

theorem traceTerm_standardClass (p : ℕ) [NeZero p] (F G : ℂ → ℂ)
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (j : Branch p) (z : UpperHalfPlane) (v : ℂ) :
    traceTerm p F G (standardClass p j) z v =
      greenOneForm (pulledField (standardRepresentative p j) F)
        (pulledField (standardRepresentative p j) G) z v :=
  greenOneForm_congr_of_eventuallyEq _ _ _ _ (z : ℂ) v
    (canonical_pulledField_eq_standard_eventually p j F hFI z)
    (canonical_pulledField_eq_standard_eventually p j G hGI z)

/-- Finite reindexing of the ORIGINAL trace, rather than a new trace definition. -/
theorem greenTrace_standard_expansion (p : ℕ) [NeZero p] (hp : p.Prime)
    (F G : ℂ → ℂ)
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (z : UpperHalfPlane) (v : ℂ) :
    greenTrace p F G z v =
      ∑ j : Branch p, greenOneForm (pulledField (standardRepresentative p j) F)
        (pulledField (standardRepresentative p j) G) z v := by
  unfold greenTrace
  calc
    _ = ∑ j : Branch p, traceTerm p F G (standardClass p j) z v :=
      ((standardClassEquiv p hp).sum_comp (fun q => traceTerm p F G q z v)).symm
    _ = _ := Finset.sum_congr rfl (fun j hj => traceTerm_standardClass p F G hFI hGI j z v)

/-- Literal pullback by the actual normalized Fricke matrix. -/
def frickeField (N : ℕ) (hN : 0 < N) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  F (slMap (frickeSL N hN) w)

theorem frickeField_differentiableAt (N : ℕ) (hN : 0 < N) (F : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (z : UpperHalfPlane) : DifferentiableAt ℝ (frickeField N hN F) (z : ℂ) := by
  have hFm : DifferentiableAt ℝ F (slMap (frickeSL N hN) z) := by
    simpa only [slMap_eq_action] using hF (frickeSL N hN • z)
  exact hFm.comp (z : ℂ) (slMap_hasFDerivAt (frickeSL N hN) z).differentiableAt

theorem standard_current_none (p : ℕ) (F G : ℂ → ℂ) (z : UpperHalfPlane) (v : ℂ) :
    greenOneForm (pulledField (standardRepresentative p none) F)
      (pulledField (standardRepresentative p none) G) z v = greenOneForm F G z v := by
  apply greenOneForm_congr_of_eventuallyEq
  · filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    change F (slMap (realSL (1 : SL(2, ℤ))) ((⟨w, hw⟩ : UpperHalfPlane) : ℂ)) = F w
    simp only [slMap_eq_action, realSL_action_int, one_smul]
  · filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    change G (slMap (realSL (1 : SL(2, ℤ))) ((⟨w, hw⟩ : UpperHalfPlane) : ℂ)) = G w
    simp only [slMap_eq_action, realSL_action_int, one_smul]

/-- Exact finite-channel covariance, with the affine tangent 1/p retained. -/
theorem standard_current_some (p : ℕ) (hp : p.Prime) (r : ZMod p)
    (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (z : UpperHalfPlane) (v : ℂ) :
    greenOneForm (pulledField (standardRepresentative p (some r)) F)
      (pulledField (standardRepresentative p (some r)) G) z v =
      greenOneForm (frickeField p hp.pos F) (frickeField p hp.pos G)
        (branchSL p hp.pos (some r) • z) ((1 / (p : ℂ)) * v) := by
  have hFe : pulledField (standardRepresentative p (some r)) F =ᶠ[𝓝 (z : ℂ)]
      (fun w => frickeField p hp.pos F (slMap (branchSL p hp.pos (some r)) w)) := by
    filter_upwards [standardMap_eq_fricke_branch_eventually p hp r z] with w hw
    exact congrArg F hw
  have hGe : pulledField (standardRepresentative p (some r)) G =ᶠ[𝓝 (z : ℂ)]
      (fun w => frickeField p hp.pos G (slMap (branchSL p hp.pos (some r)) w)) := by
    filter_upwards [standardMap_eq_fricke_branch_eventually p hp r z] with w hw
    exact congrArg G hw
  have hFD : DifferentiableAt ℝ (frickeField p hp.pos F)
      (slMap (branchSL p hp.pos (some r)) z) := by
    simpa only [slMap_eq_action] using
      frickeField_differentiableAt p hp.pos F hF (branchSL p hp.pos (some r) • z)
  have hGD : DifferentiableAt ℝ (frickeField p hp.pos G)
      (slMap (branchSL p hp.pos (some r)) z) := by
    simpa only [slMap_eq_action] using
      frickeField_differentiableAt p hp.pos G hG (branchSL p hp.pos (some r) • z)
  calc
    _ = greenOneForm
        (fun w => frickeField p hp.pos F (slMap (branchSL p hp.pos (some r)) w))
        (fun w => frickeField p hp.pos G (slMap (branchSL p hp.pos (some r)) w)) z v :=
      greenOneForm_congr_of_eventuallyEq _ _ _ _ (z : ℂ) v hFe hGe
    _ = _ := by
      simpa only [slMap_eq_action, slFactor_finite_branch] using
        greenOneForm_slMap_pullback (branchSL p hp.pos (some r)) z _ _ hFD hGD v

/-- Both genuine physical channels in the ORIGINAL finite trace. -/
theorem greenTrace_two_channel_pointwise (p : ℕ) [NeZero p] (hp : p.Prime)
    (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 p, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (z : UpperHalfPlane) (v : ℂ) :
    greenTrace p F G z v = greenOneForm F G z v +
      ∑ r : ZMod p, greenOneForm (frickeField p hp.pos F) (frickeField p hp.pos G)
        (branchSL p hp.pos (some r) • z) ((1 / (p : ℂ)) * v) := by
  rw [greenTrace_standard_expansion p hp F G hFI hGI, Fintype.sum_option]
  rw [standard_current_none]
  congr 1
  exact Finset.sum_congr rfl (fun r hr => standard_current_some p hp r F G hF hG z v)

/-- Actual completed Gamma0 fields discharge every analytic and automorphy input. -/
theorem actualCompletedGreenTrace_two_channel_pointwise (p : ℕ) [NeZero p]
    (hp : p.Prime) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p)
    (z : UpperHalfPlane) (v : ℂ) :
    actualCompletedGreenTrace p s u z v =
      greenOneForm (completedComplexField p s) (completedComplexField p u) z v +
      ∑ r : ZMod p, greenOneForm (frickeField p hp.pos (completedComplexField p s))
        (frickeField p hp.pos (completedComplexField p u))
        (branchSL p hp.pos (some r) • z) ((1 / (p : ℂ)) * v) :=
  greenTrace_two_channel_pointwise p hp _ _
    (fun z => (completedComplexField_contDiffAt p s z).differentiableAt (by simp))
    (fun z => (completedComplexField_contDiffAt p u z).differentiableAt (by simp))
    (completedComplexField_Gamma0_invariant p hp.pos s hs)
    (completedComplexField_Gamma0_invariant p hp.pos u hu) z v

end ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
