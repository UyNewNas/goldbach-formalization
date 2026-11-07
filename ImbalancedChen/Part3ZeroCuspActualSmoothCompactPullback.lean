import ImbalancedChen.Part3InfinityZeroActualFiniteGeometricAssembly
import ImbalancedChen.Part3ActualCompactSeedMaassJoin

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The literal normalized zero-cusp matrix is real, and need not be an
integral modular matrix. Its actual rational real chart is C-infinity on
the positive chart, by the genuine nonzero Mobius denominator. Compact
support is transported through its actual involutive action on H. Thus
native compact smooth H seeds have native compact smooth zero-cusp
pullbacks. No sigma0 Maass/Dirichlet covariance or domain is assumed.
-/

noncomputable section

namespace ImbalancedChen.Part3.ZeroCuspActualSmoothCompactPullback20261026b

open Set Filter Matrix Matrix.SpecialLinearGroup
open scoped UpperHalfPlane
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.InfinityZeroActualFiniteGeometricAssembly20261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

/-- Real matrix coordinates of the existing literal zeroSL action. -/
def zeroRealMobius (N : ℕ) (hN : 0 < N) (p : ℝ × ℝ) : ℂ :=
  UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) (complexOfPair p) /
    UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) (complexOfPair p)

def zeroRealChart (N : ℕ) (hN : 0 < N) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((zeroRealMobius N hN p).re, (zeroRealMobius N hN p).im)

theorem zeroReal_denom_ne_zero (N : ℕ) (hN : 0 < N)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) (complexOfPair p) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ (zeroSL N hN))
    (⟨complexOfPair p, hp⟩ : UpperHalfPlane)

theorem zeroRealChart_contDiffAt (N : ℕ) (hN : 0 < N)
    {p : ℝ × ℝ} (hp : 0 < p.2) : ContDiffAt ℝ ∞ (zeroRealChart N hN) p := by
  have hc : ContDiff ℝ ∞ complexOfPair := by
    have heq : complexOfPair =
        (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
      funext q
      ext <;> simp [complexOfPair]
    rw [heq]
    fun_prop
  have hn : ContDiff ℝ ∞ (fun q =>
      UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) (complexOfPair q)) := by
    unfold UpperHalfPlane.num
    exact (contDiff_const.mul hc).add contDiff_const
  have hd : ContDiff ℝ ∞ (fun q =>
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) (complexOfPair q)) := by
    unfold UpperHalfPlane.denom
    exact (contDiff_const.mul hc).add contDiff_const
  have hm : ContDiffAt ℝ ∞ (zeroRealMobius N hN) p :=
    hn.contDiffAt.div hd.contDiffAt (zeroReal_denom_ne_zero N hN hp)
  exact ((Complex.reCLM.contDiff.contDiffAt).comp p hm).prodMk
    ((Complex.imCLM.contDiff.contDiffAt).comp p hm)

theorem zeroRealChart_eq_actual (N : ℕ) (hN : 0 < N)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    zeroRealChart N hN p = ((zeroSL N hN • chartLift p).re, (zeroSL N hN • chartLift p).im) := by
  rw [chartLift_of_positive hp]
  let z : UpperHalfPlane := ⟨complexOfPair p, hp⟩
  have hcoe : ((zeroSL N hN • z : UpperHalfPlane) : ℂ) = zeroRealMobius N hN p := by
    change (((SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) • z : UpperHalfPlane) : ℂ) = _
    exact UpperHalfPlane.coe_smul_of_det_pos (by simp) z
  exact Prod.ext (congrArg Complex.re hcoe.symm) (congrArg Complex.im hcoe.symm)

theorem zeroRealChart_mapsTo_positive (N : ℕ) (hN : 0 < N) :
    MapsTo (zeroRealChart N hN) positiveChart positiveChart := by
  intro p hp
  change 0 < (zeroRealChart N hN p).2
  rw [zeroRealChart_eq_actual N hN hp]
  exact (zeroSL N hN • chartLift p).im_pos

def zeroSeedPullback (N : ℕ) (hN : 0 < N) (f : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) : ℂ := f (zeroSL N hN • z)

theorem zeroSL_action_involutive (N : ℕ) (hN : 0 < N) :
    Function.Involutive (fun z : UpperHalfPlane => zeroSL N hN • z) := by
  simpa only [zeroSL_eq_frickeSL] using frickeSL_action_involutive N hN

theorem zeroSL_action_continuous (N : ℕ) (hN : 0 < N) :
    Continuous (fun z : UpperHalfPlane => zeroSL N hN • z) := by
  change Continuous (fun z : UpperHalfPlane => (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) • z)
  exact continuous_const_smul _

theorem zeroSeedPullback_support_subset (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (K : Set UpperHalfPlane) (hs : Function.support f ⊆ K) :
    Function.support (zeroSeedPullback N hN f) ⊆ (fun z => zeroSL N hN • z) '' K := by
  intro z hz
  refine ⟨zeroSL N hN • z, hs hz, ?_⟩
  exact zeroSL_action_involutive N hN z

theorem zeroSeedPullback_hasCompactSupport (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f) :
    HasCompactSupport (zeroSeedPullback N hN f) :=
  HasCompactSupport.of_support_subset_isCompact
    (hfc.image (zeroSL_action_continuous N hN))
    (zeroSeedPullback_support_subset N hN f (tsupport f) (subset_tsupport f))

theorem extendUpper_zeroSeedPullback (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) {p : ℝ × ℝ} (hp : 0 < p.2) :
    extendUpper (zeroSeedPullback N hN f) p = extendUpper f (zeroRealChart N hN p) := by
  rw [extendUpper_chartLift _ p hp, zeroRealChart_eq_actual N hN hp, extendUpper_pair]
  rfl

/-- Genuine native C-infinity of the real zero-chart pullback, not an
integral-matrix surrogate or a supplied transformed-smoothness contract. -/
theorem zeroSeedPullback_nativeCinfty (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ContDiffOn ℝ ∞ (extendUpper (zeroSeedPullback N hN f)) positiveChart := by
  have hchart : ContDiffOn ℝ ∞ (zeroRealChart N hN) positiveChart := by
    intro p hp
    exact (zeroRealChart_contDiffAt N hN hp).contDiffWithinAt
  have hcomp := hf.comp hchart (zeroRealChart_mapsTo_positive N hN)
  apply hcomp.congr
  intro p hp
  exact extendUpper_zeroSeedPullback N hN f hp

end ImbalancedChen.Part3.ZeroCuspActualSmoothCompactPullback20261026b
