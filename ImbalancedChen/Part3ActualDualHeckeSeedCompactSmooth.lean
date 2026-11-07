import ImbalancedChen.Part3ActualCompactSeedHeckeReindex
import ImbalancedChen.Part3ActualClassicalHeckeMaass
import ImbalancedChen.Part3ActualCompactSeedMaassJoin

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The CORRECT dual Hecke seed is genuinely compact and natively C-infinity.
The normalized REAL inverse branches have the literal affine coordinate
maps z/p and p*z-b, proved from the actual original branch actions. A
finite union of actual forward images of the original compact support
contains the transformed support. Smoothness is native chart composition,
not a supplied compactness/regularity premise about the transformed seed.
Its original H L1 integrability is consequently derived. Native graph
membership/physical Hecke representative identification remain consumers.
-/

namespace ImbalancedChen.Part3.ActualDualHeckeSeedCompactSmooth20261026b
noncomputable section
open Set Filter MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators Topology
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualCompactSeedHeckeReindex20261026b ActualClassicalHeckeMaass20261026b
open Gamma0CompactTensorPoincareC2Core20261025a ActualCompactSeedMaassJoin20261025a
open MaassWeakOperatorCore20261024zz CanonicalPlanarL2UnitarySourceOnly

variable (p : ℕ) (hp : p.Prime)

def dualBranchScale : Branch p → ℝ
  | none => (p : ℝ)⁻¹
  | some _ => p

def dualBranchShift : Branch p → ℝ
  | none => 0
  | some b => -(b.val : ℝ)

theorem inverse_none_coe (z : ℍ) :
    (((branchSL p hp.pos none)⁻¹ • z : ℍ) : ℂ) = (z : ℂ)/(p : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := branchSL_none_coe p hp.pos ((branchSL p hp.pos none)⁻¹ • z)
  rw [smul_inv_smul] at h
  apply (eq_div_iff hpC).mpr
  exact (mul_comm _ _).trans h.symm

theorem inverse_some_coe (b : ZMod p) (z : ℍ) :
    (((branchSL p hp.pos (some b))⁻¹ • z : ℍ) : ℂ) = (p : ℂ)*(z : ℂ)-(b.val : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := branchSL_some_coe p hp.pos b ((branchSL p hp.pos (some b))⁻¹ • z)
  rw [smul_inv_smul] at h
  have hmul := (eq_div_iff hpC).mp h
  linear_combination -hmul

theorem dualBranchScale_pos (j : Branch p) : 0 < dualBranchScale p j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  cases j <;> simp only [dualBranchScale]
  · exact inv_pos.mpr hpR
  · exact hpR

/-- Literal real physical coordinate maps of the inverse branches. -/
theorem inverse_branch_chart (j : Branch p) (z : ℍ) :
    (((branchSL p hp.pos j)⁻¹ • z).re,((branchSL p hp.pos j)⁻¹ • z).im) =
      affineBranch (dualBranchScale p j) (dualBranchShift p j) (z.re,z.im) := by
  cases j with
  | none =>
    apply Prod.ext
    · have hx : ((branchSL p hp.pos none)⁻¹ • z).re = z.re/(p : ℝ) := by
        simpa only [← Complex.ofReal_natCast,Complex.div_ofReal_re] using
          congrArg Complex.re (inverse_none_coe p hp z)
      simpa [affineBranch,dualBranchScale,dualBranchShift,div_eq_mul_inv,mul_comm] using hx
    · have hy : ((branchSL p hp.pos none)⁻¹ • z).im = z.im/(p : ℝ) := by
        simpa only [← Complex.ofReal_natCast,Complex.div_ofReal_im] using
          congrArg Complex.im (inverse_none_coe p hp z)
      simpa [affineBranch,dualBranchScale,dualBranchShift,div_eq_mul_inv,mul_comm] using hy
  | some b =>
    apply Prod.ext
    · simpa [affineBranch,dualBranchScale,dualBranchShift,sub_eq_add_neg] using
        congrArg Complex.re (inverse_some_coe p hp b z)
    · simpa [affineBranch,dualBranchScale,dualBranchShift] using
        congrArg Complex.im (inverse_some_coe p hp b z)

theorem extendUpper_inverse_branch (f : ℍ → ℂ) (j : Branch p) {q : ℝ × ℝ} (hq : 0 < q.2) :
    extendUpper (fun z => f ((branchSL p hp.pos j)⁻¹ • z)) q =
      extendUpper f (affineBranch (dualBranchScale p j) (dualBranchShift p j) q) := by
  rw [extendUpper_chartLift _ q hq]
  have hchart : (((branchSL p hp.pos j)⁻¹ • chartLift q).re,
      ((branchSL p hp.pos j)⁻¹ • chartLift q).im) =
      affineBranch (dualBranchScale p j) (dualBranchShift p j) q := by
    simpa only [chartLift_of_positive hq,complexOfPair] using inverse_branch_chart p hp j (chartLift q)
  rw [← hchart,extendUpper_pair]

theorem inverse_branch_nativeCinfty (f : ℍ → ℂ)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) (j : Branch p) :
    ContDiffOn ℝ ∞ (extendUpper (fun z => f ((branchSL p hp.pos j)⁻¹ • z))) positiveChart := by
  have hcomp := hf.comp (show ContDiffOn ℝ ∞
    (affineBranch (dualBranchScale p j) (dualBranchShift p j)) positiveChart by
      unfold affineBranch
      fun_prop) (affineBranch_mapsTo (dualBranchScale_pos p hp j) (dualBranchShift p j))
  apply hcomp.congr
  intro q hq
  exact extendUpper_inverse_branch p hp f j hq

def dualSeedCarrier (K : Set ℍ) : Set ℍ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  ⋃ j : Branch p, (fun z : ℍ => branchSL p hp.pos j • z) '' K

theorem dualSeedCarrier_compact {K : Set ℍ} (hK : IsCompact K) : IsCompact (dualSeedCarrier p hp K) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact isCompact_iUnion (fun j => hK.image (continuous_const_smul (branchSL p hp.pos j)))

theorem dualHeckeSeed_support_subset (f : ℍ → ℂ) {K : Set ℍ} (hs : Function.support f ⊆ K) :
    Function.support (dualHeckeSeed p hp f) ⊆ dualSeedCarrier p hp K := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro z hz
  by_contra hout
  have hzero (j : Branch p) : f ((branchSL p hp.pos j)⁻¹ • z)=0 := by
    by_contra hn
    apply hout
    exact mem_iUnion.mpr ⟨j,((branchSL p hp.pos j)⁻¹ • z),hs hn,smul_inv_smul _ _⟩
  apply hz
  simp [dualHeckeSeed,hzero]

theorem dualHeckeSeed_hasCompactSupport (f : ℍ → ℂ) (hfc : HasCompactSupport f) :
    HasCompactSupport (dualHeckeSeed p hp f) :=
  HasCompactSupport.of_support_subset_isCompact (dualSeedCarrier_compact p hp hfc)
    (dualHeckeSeed_support_subset p hp f (subset_tsupport f))

/-- Native smoothness of the actual finite transformed seed. -/
theorem dualHeckeSeed_nativeCinfty (f : ℍ → ℂ)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ContDiffOn ℝ ∞ (extendUpper (dualHeckeSeed p hp f)) positiveChart := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hsum := (ContDiffOn.sum (s := (Finset.univ : Finset (Branch p)))
    (fun j hj => inverse_branch_nativeCinfty p hp f hf j)).const_smul (Real.sqrt (p : ℝ) : ℂ)⁻¹
  apply hsum.congr
  intro q hq
  rw [extendUpper_chartLift _ q hq]
  simp only [dualHeckeSeed]
  simp_rw [extendUpper_chartLift _ q hq]

theorem dualHeckeSeed_integrable (f : ℍ → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    Integrable (dualHeckeSeed p hp f) (volume : Measure ℍ) :=
  (native_C2_continuous _ ((dualHeckeSeed_nativeCinfty p hp f hf).of_le (by simp))).integrable_of_hasCompactSupport
    (dualHeckeSeed_hasCompactSupport p hp f hfc)

end
end ImbalancedChen.Part3.ActualDualHeckeSeedCompactSmooth20261026b

