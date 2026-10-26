import ImbalancedChen.Part3CompletedEisensteinSpatialMaass
import ImbalancedChen.Part3CompletedActualEisensteinIdentity
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

All spatial orders of the actual continued Fourier expression. The proof
does not infer smoothness from C2. For each finite order, the genuine
Frechet derivative of momentSum(j,k) is the fixed bounded linear lift of
momentSum(j+1,k) and momentSum(j,k+1). Induction therefore proves every finite
order of ContDiffOn, using the actual uniform summable derivative bounds
already supplied before the spatial point. Passing through contDiffOn_infty
gives C-infinity. Explicit recursively iterated real derivatives also equal
the actual mixed-moment series for every j,k.

The completed central constant is retained as its true sqrt(y) log(y)
analytic-limit expression. The final global log-height chart theorem is
about completedActualEisenstein from the separate physical-continuation
identity module; its reconstruction and automorphy are not reproved here.
-/

namespace ImbalancedChen.Part3.ContinuedFourierSpatialSmooth

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.ContinuedFourierSpatialMoments
open ImbalancedChen.Part3.ContinuedFourierMomentSeriesCalculus
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.CompletedEisensteinCentralHeight
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

/-- Genuine arbitrary finite spatial regularity from the shifted-moment
Frechet derivative, rather than from a fixed finite regularity theorem. -/
theorem momentSum_contDiffOn_nat (r j k : ℕ) (s : ℂ) :
    ContDiffOn ℝ (r : ℕ∞ω) (fun p : ℝ × ℝ => momentSum j k s p.2 p.1) upperChart := by
  induction r generalizing j k with
  | zero => exact contDiffOn_zero.mpr (momentSum_continuousOn j k s)
  | succ r ih =>
      have hG : ContDiffOn ℝ (r : ℕ∞ω) (sumGradient j k s) upperChart :=
        (firstLift.contDiff.comp_contDiffOn (ih (j + 1) k)).add
          (secondLift.contDiff.comp_contDiffOn (ih j (k + 1)))
      have hc : ContDiffOn ℝ ((r : ℕ∞ω) + 1)
          (fun p : ℝ × ℝ => momentSum j k s p.2 p.1) upperChart := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          (n := (r : ℕ∞ω)) upperChart_isOpen.uniqueDiffOn).2
        refine ⟨?_, sumGradient j k s, hG, ?_⟩
        · intro h
          simp at h
        · intro p hp
          exact (momentSum_hasFDerivAt j k s p.1 p.2 hp).hasFDerivWithinAt
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hc

theorem momentSum_contDiffOn_infty (j k : ℕ) (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => momentSum j k s p.2 p.1) upperChart := by
  apply contDiffOn_infty.mpr
  intro r
  exact momentSum_contDiffOn_nat r j k s

/-- Recursively iterated actual horizontal derivatives on the real chart. -/
def horizontalDerivs : ℕ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)
  | 0, F => F
  | j + 1, F => fun p => deriv (fun t : ℝ => horizontalDerivs j F (t, p.2)) p.1

def verticalDerivs : ℕ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)
  | 0, F => F
  | k + 1, F => fun p => deriv (fun t : ℝ => verticalDerivs k F (p.1, t)) p.2

theorem horizontalDerivs_momentSum (j : ℕ) (s : ℂ) (x y : ℝ) (hy : 0 < y) :
    horizontalDerivs j (fun p : ℝ × ℝ => momentSum 0 0 s p.2 p.1) (x, y) =
      momentSum j 0 s y x := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
      change deriv (fun t : ℝ => horizontalDerivs j
        (fun p : ℝ × ℝ => momentSum 0 0 s p.2 p.1) (t, y)) x = _
      have heq : (fun t : ℝ => horizontalDerivs j
          (fun p : ℝ × ℝ => momentSum 0 0 s p.2 p.1) (t, y)) =
          (fun t => momentSum j 0 s y t) := funext fun t => ih t y hy
      rw [heq]
      exact (momentSum_hasDerivAt_x j 0 s y x hy).deriv

/-- Every actual mixed derivative is the literal corresponding infinite
qMoment/phase series; its local uniform summable bound is spatialMajorant. -/
theorem mixedDerivs_eq_actual_series (j k : ℕ) (s : ℂ) (x y : ℝ) (hy : 0 < y) :
    verticalDerivs k
      (horizontalDerivs j (fun p : ℝ × ℝ => momentSum 0 0 s p.2 p.1)) (x, y) =
        ∑' n : ℕ, spatialMomentTerm j k n s y x := by
  induction k generalizing x y with
  | zero => exact horizontalDerivs_momentSum j s x y hy
  | succ k ih =>
      change deriv (fun t : ℝ => verticalDerivs k
        (horizontalDerivs j (fun p : ℝ × ℝ => momentSum 0 0 s p.2 p.1)) (x, t)) y = _
      have hevent : (fun t : ℝ => verticalDerivs k
          (horizontalDerivs j (fun p : ℝ × ℝ => momentSum 0 0 s p.2 p.1)) (x, t))
          =ᶠ[𝓝 y] (fun t => momentSum j k s t x) := by
        filter_upwards [Ioi_mem_nhds hy] with t ht
        exact ih x t ht
      exact ((momentSum_hasDerivAt_y j k s y x hy).congr_of_eventuallyEq hevent).deriv

theorem weightedKernel_contDiffOn_infty (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => weightedKernel s p.2 p.1) upperChart := by
  have hp := momentSum_contDiffOn_infty 0 0 s
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (-p.1, p.2)) := by fun_prop
  have hn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => momentSum 0 0 s p.2 (-p.1)) upperChart :=
    hp.comp hmap.contDiffOn (fun p hp => hp)
  have hsqrt : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt p.2) upperChart :=
    contDiffOn_snd.sqrt (fun p hp => ne_of_gt hp)
  have hroot : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Real.sqrt p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt
  apply ((hroot.const_mul (2 : ℂ)).mul (hp.add hn)).congr
  intro p hp
  rw [weightedKernel, ← signedMomentSum_zero_zero_eq_actual s p.2 p.1 hp]
  simp only [signedMomentSum, pow_zero, one_mul]

theorem heightPower_contDiffOn_infty (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ) ^ s) upperChart := by
  have hlogR : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.log p.2) upperChart :=
    contDiffOn_snd.log (fun p hp => ne_of_gt hp)
  have hlog : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Real.log p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlogR
  apply (hlog.mul_const s).cexp.congr
  intro p hp
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hp)),
    ← Complex.ofReal_log (le_of_lt hp)]

theorem centralHeight_contDiffOn_infty :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => centralHeight p.2) upperChart := by
  have hsqrt : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt p.2) upperChart :=
    contDiffOn_snd.sqrt (fun p hp => ne_of_gt hp)
  have hroot : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Real.sqrt p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt
  have hlogR : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.log p.2) upperChart :=
    contDiffOn_snd.log (fun p hp => ne_of_gt hp)
  have hlog : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Real.log p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlogR
  simpa only [centralHeight, root0_eq_sqrt] using
    (hroot.const_mul centralScalar).add (hroot.mul hlog)

theorem completedConstant_contDiffOn_infty (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => completedConstant p.2 s) upperChart := by
  by_cases hh : s = 1 / 2
  · subst s
    apply centralHeight_contDiffOn_infty.congr
    intro p hp
    exact completedConstant_half p.2 hp
  · apply (((heightPower_contDiffOn_infty s).const_mul (completedRiemannZeta (2 * s))).add
      ((heightPower_contDiffOn_infty (1 - s)).const_mul (completedRiemannZeta (2 * s - 1)))).congr
    intro p hp
    exact completedConstant_eq_raw p.2 s hh

/-- Actual full continued Fourier expression, with its genuine central
value, is smooth in both spatial variables to all orders. -/
theorem completedEisensteinFourier_contDiffOn_infty (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => completedEisensteinFourier s p.2 p.1) upperChart := by
  simpa only [completedEisensteinFourier, weightedKernel] using
    (completedConstant_contDiffOn_infty s).add (weightedKernel_contDiffOn_infty s)

/-- A global smooth real chart of the actual continued physical object;
positive height is exp(p.2), so there is no extraneous totalized boundary. -/
def actualLogHeightChart (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  completedActualEisenstein s (horizontalPoint (Real.exp p.2) (Real.exp_pos p.2) p.1)

theorem completedActualEisenstein_logHeight_smooth
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) : ContDiff ℝ ∞ (actualLogHeightChart s) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1, Real.exp p.2)) := by fun_prop
  have hc : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => completedEisensteinFourier s (Real.exp p.2) p.1) univ :=
    (completedEisensteinFourier_contDiffOn_infty s).comp hmap.contDiffOn
      (fun p hp => Real.exp_pos p.2)
  exact contDiffOn_univ.mp hc

end

end ImbalancedChen.Part3.ContinuedFourierSpatialSmooth
