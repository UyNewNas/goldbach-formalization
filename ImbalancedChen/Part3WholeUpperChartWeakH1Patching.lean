import ImbalancedChen.Part3CountableLocalWeakGradientPatching
import ImbalancedChen.Part3Gamma0WholeSeedAdjointWeakEquation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A single pair of ordinary weak gradients of the actual automorphic
pullback on the WHOLE upper chart. Every compact positive-height set has
local L2 value and gradients; every compact smooth upper-chart test is
legal. The proved countable open rectangle cover, native compact directed
cover lemma, and local uniqueness patch independently extracted jets.
The actual final endpoint obtains its raw whole-H seed identity from the
frozen genuine unfolding/adjoint supplier. No global ordinary L2 bound,
global quotient form membership or spectral claim is inferred. -/

namespace ImbalancedChen.Part3.WholeUpperChartWeakH1Patching20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ProductConvolutionSecondDerivatives20261026a
open Gamma0CompactDefectMollifier20261026a Gamma0ActualSmoothQuotientCore20261025a
open PlanarLocalWeakGradientExtraction20261026b ActualPullbackLocalH1Transfer20261026b
open LocalL2WeakGradientUniqueness20261026b CountableLocalWeakGradientPatching20261026b
open WholeSeedTestsRectangleLocalH120261026b
open Gamma0ActualMinimalShiftRange20261025a Gamma0WholeSeedAdjointWeakEquation20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

def chartRectangle (n : ℕ) : Set Plane :=
  Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
    Ioo (mollifierRadius (n + 1)) ((n : ℝ) + 1)

theorem chartRectangle_open (n : ℕ) : IsOpen (chartRectangle n) := isOpen_Ioo.prod isOpen_Ioo

theorem chartRectangle_mono : Monotone chartRectangle := by
  intro n m hnm p hp
  have hcast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hr : mollifierRadius (m + 1) ≤ mollifierRadius (n + 1) := by
    unfold mollifierRadius
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hnm 1) 1
  exact ⟨⟨by linarith [hp.1.1], hp.1.2.trans_le hcast⟩,
    ⟨hr.trans_lt hp.2.1, hp.2.2.trans_le hcast⟩⟩

theorem chartRectangle_cover : (⋃ n : ℕ, chartRectangle n) = upperChart := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact (mollifierRadius_pos (n + 1)).trans hn.2.1
  · intro hp
    have hy : 0 < p.2 := hp
    obtain ⟨k, hk⟩ := exists_nat_gt (max |p.1| p.2)
    have ht : Tendsto mollifierRadius atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨m, hm⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hy))
    let n := max k m
    have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left k m
    have hmn : m ≤ n + 1 := (le_max_right k m).trans (Nat.le_succ n)
    have hr := hm (n + 1) hmn
    have hx : |p.1| < (n : ℝ) + 1 := by linarith [le_max_left |p.1| p.2]
    have hy' : p.2 < (n : ℝ) + 1 := by linarith [le_max_right |p.1| p.2]
    exact mem_iUnion.mpr ⟨n, ⟨abs_lt.mp hx, hr, hy'⟩⟩

theorem compact_subset_chartRectangle {K : Set Plane} (hK : IsCompact K)
    (hpos : K ⊆ upperChart) : ∃ n : ℕ, K ⊆ chartRectangle n :=
  hK.elim_directed_cover chartRectangle chartRectangle_open
    (by simpa only [chartRectangle_cover] using hpos)
    (fun n m => ⟨max n m, chartRectangle_mono (le_max_left _ _),
      chartRectangle_mono (le_max_right _ _)⟩)

/-- Actual whole-upper-chart H1_loc, with literal gradient functions and
all compact smooth tests; this does not demand global ordinary L2. -/
def HasUpperChartWeakH1 (F : Plane → ℂ) : Prop :=
  ∃ Gx Gy : Plane → ℂ,
    (∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp F 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gx 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gy 2 ((volume : Measure Plane).restrict K)) ∧
    (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p) * Gx p) = -(∫ p, star (directional xDirection ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * Gy p) = -(∫ p, star (directional yDirection ψ p) * F p)))

theorem upperChart_H1_of_whole_seed_tests (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hraw : WholeSeedAdjointTests N f) :
    HasUpperChartWeakH1 (actualPlanePullback N f) := by
  let F := actualPlanePullback N f
  have hclosed (n : ℕ) : HasCoordinateLocalH1On
      (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
        Icc (mollifierRadius (n + 1)) ((n : ℝ) + 1)) F := by
    have hLR : -((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hr : mollifierRadius (n + 1) ≤ (n : ℝ) + 1 := by
      have hsmall : mollifierRadius (n + 1) ≤ 1 := by
        unfold mollifierRadius
        simpa only [one_div_one] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
            (by have hn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
                linarith)
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      exact hsmall.trans hn
    exact rectangle_localH1_of_whole_seed_tests N f hraw _ _ _ _ hLR hr
      (mollifierRadius_pos (n + 1))
  have hsub (n : ℕ) : chartRectangle n ⊆
      Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
        Icc (mollifierRadius (n + 1)) ((n : ℝ) + 1) := fun p hp =>
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2.1.le, hp.2.2.le⟩
  choose gx gy hgrad using (fun n => (hclosed n).2)
  have hF (n : ℕ) : MemLp F 2 ((volume : Measure Plane).restrict (chartRectangle n)) :=
    (hclosed n).1.mono_measure (Measure.restrict_mono_set volume (hsub n))
  have hopen (n : ℕ) : IsLocalWeakGradientOn (chartRectangle n) F (gx n) (gy n) :=
    fun ψ hψ hc hs => hgrad n ψ hψ hc (hs.trans (hsub n))
  obtain ⟨Gx, Gy, hpatch⟩ := exists_patched_local_weak_gradient chartRectangle
    chartRectangle_open F hF gx gy hopen
  refine ⟨Gx, Gy, ?_, ?_⟩
  · intro K hK hpos
    obtain ⟨n, hn⟩ := compact_subset_chartRectangle hK hpos
    have hm := Measure.restrict_mono_set (volume : Measure Plane) hn
    exact ⟨(hpatch n).1.mono_measure hm, (hpatch n).2.1.mono_measure hm,
      (hpatch n).2.2.1.mono_measure hm⟩
  · intro ψ hψ hc hs
    obtain ⟨n, hn⟩ := compact_subset_chartRectangle hc hs
    exact (hpatch n).2.2.2 ψ hψ hc hn

/-- Actual minimal-adjoint deficiency vectors are H1_loc on the entire
upper chart. The whole-H raw seed identity is derived from the genuine
quotient unfolding supplier, including points crossing carrier seams. -/
theorem actual_defect_whole_upperChart_H1 (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) :
    HasUpperChartWeakH1 (actualPlanePullback N f) :=
  upperChart_H1_of_whole_seed_tests N f
    (fun s => actual_defect_whole_finite_seed_tests N f hf s)

/-- Direct actual rectangle endpoint without caller localization,
cutoff, small-kernel tail, raw test identity, gradient or PDE premises. -/
theorem actual_defect_every_positive_rectangle_H1 (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (L R c d : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hc : 0 < c) :
    HasCoordinateLocalH1On (Icc L R ×ˢ Icc c d) (actualPlanePullback N f) :=
  rectangle_localH1_of_whole_seed_tests N f
    (fun s => actual_defect_whole_finite_seed_tests N f hf s) L R c d hLR hcd hc

end
end ImbalancedChen.Part3.WholeUpperChartWeakH1Patching20261026b
