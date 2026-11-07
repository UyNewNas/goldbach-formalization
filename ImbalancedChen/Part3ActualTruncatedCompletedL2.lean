import ImbalancedChen.Part3ActualCompletedTwoCuspTruncation
import ImbalancedChen.Part3ActualTwoCuspHeightRemainders
import ImbalancedChen.Part3PrimeTwoCuspCompactTruncation
import Mathlib.MeasureTheory.Function.L2Space

/-! Original canonical quotient L2 membership of the actual sharp
two-cusp truncated completed Eisenstein field. Both native tail estimates
are consumed with their exact finite coefficient masses. Compactness of
the full complementary quotient core and continuity of the original
completed field give its remaining bound. Actual finite quotient volume
then proves MemLp2 and constructs the genuine native L2 representative.
No tail/L2 hypothesis, smooth cutoff, spectral expansion or completeness
assumption is introduced. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a
open ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactTruncation20261026b
open ImbalancedChen.Part3.ActualCompletedTwoCuspTruncation20261026b

namespace ImbalancedChen.Part3.ActualTruncatedCompletedL220261026b

/-- The actual normalized cusp coordinates retain their original
exponential rate and the exact finite physical coefficient mass. -/
theorem truncatedCompleted_high_bound (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) (M : ℕ) (hM : |s.re| ≤ (M : ℝ))
    (b : Bool) (z : UpperHalfPlane) (hz : Y < z.im) :
    ‖truncatedCompleted p hp Y hY s hs
        (orbitProjection p (if b then frickeSL p hp.pos • z else z))‖ ≤
      (physicalCuspMass p hp.pos s b * cuspTailConstant M) *
        Real.exp (-(Real.pi / 2) * z.im) := by
  have hz1 : 1 ≤ z.im := le_trans hY hz.le
  have hb := actual_native_two_cusp_remainder_bound p hp.pos M hM hs.1 hs.2.1 b z hz1
  cases b
  · change ‖truncatedCompleted p hp Y hY s hs (orbitProjection p z)‖ ≤ _
    rw [truncatedCompleted_infinity p hp Y hY s hs z hz]
    simpa only [Bool.false_eq_true, if_false, physicalCuspConstant] using hb
  · change ‖truncatedCompleted p hp Y hY s hs
      (orbitProjection p (frickeSL p hp.pos • z))‖ ≤ _
    rw [truncatedCompleted_zero p hp Y hY s hs z hz]
    simpa only [Bool.true_eq_true, if_true, physicalCuspConstant] using hb

/-- A derived global bound on the actual function, using the full
pointwise compact complement. No a.e. cusp-cover assertion is needed. -/
theorem truncatedCompleted_global_bound (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖truncatedCompleted p hp Y hY s hs q‖ ≤ C := by
  obtain ⟨M, hM⟩ := exists_nat_ge |s.re|
  obtain ⟨K, hK⟩ := (twoCuspTruncation_isCompact p hp Y hY).exists_bound_of_continuousOn
    (quotientCompleted_continuous p hp.pos s hs).continuousOn
  let A₀ := physicalCuspMass p hp.pos s false * cuspTailConstant M
  let A₁ := physicalCuspMass p hp.pos s true * cuspTailConstant M
  have hA₀ : 0 ≤ A₀ := mul_nonneg (physicalCuspMass_nonneg p hp.pos s false)
    (cuspTailConstant_pos M).le
  have hA₁ : 0 ≤ A₁ := mul_nonneg (physicalCuspMass_nonneg p hp.pos s true)
    (cuspTailConstant_pos M).le
  refine ⟨max K 0 + A₀ + A₁, by positivity, ?_⟩
  intro q
  have hexp (z : UpperHalfPlane) : Real.exp (-(Real.pi / 2) * z.im) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) z.im_pos.le
  by_cases hi : q ∈ infinityHighNeighborhood p Y
  · obtain ⟨z, hz, rfl⟩ := hi
    have hb := truncatedCompleted_high_bound p hp Y hY s hs M hM false z hz
    simp only [Bool.false_eq_true, if_false] at hb
    have he : A₀ * Real.exp (-(Real.pi / 2) * z.im) ≤ A₀ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hexp z) hA₀
    exact (hb.trans he).trans (by linarith [le_max_right K 0])
  · by_cases hz : q ∈ zeroHighNeighborhood p hp Y
    · obtain ⟨z, hz, rfl⟩ := hz
      have hb := truncatedCompleted_high_bound p hp Y hY s hs M hM true z hz
      simp only [Bool.true_eq_true, if_true] at hb
      have he : A₁ * Real.exp (-(Real.pi / 2) * z.im) ≤ A₁ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hexp z) hA₁
      exact (hb.trans he).trans (by linarith [le_max_right K 0])
    · have hcore : q ∈ twoCuspTruncation p hp Y := by
        rintro (hq | hq)
        · exact hi hq
        · exact hz hq
      rw [truncatedCompleted_on_core p hp Y hY s hs q hcore]
      exact (hK q hcore).trans (by linarith [le_max_left K 0])

/-- Genuine canonical quotient square integrability. The finite volume
is the ORIGINAL carrier pushforward, never a substitute cusp measure. -/
theorem truncatedCompleted_memLp_two (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    MemLp (truncatedCompleted p hp Y hY s hs) 2 (carrierPushforward p) := by
  letI : IsFiniteMeasure (carrierPushforward p) := ⟨carrierPushforward_finite p⟩
  obtain ⟨C, _, hC⟩ := truncatedCompleted_global_bound p hp Y hY s hs
  exact MemLp.of_bound (truncatedCompleted_measurable p hp Y hY s hs).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

def truncatedCompletedL2 (p : ℕ) [NeZero p] (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) : Lp ℂ 2 (carrierPushforward p) :=
  (truncatedCompleted_memLp_two p hp Y hY s hs).toLp (truncatedCompleted p hp Y hY s hs)

theorem truncatedCompletedL2_coeFn (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    (truncatedCompletedL2 p hp Y hY s hs : Gamma0OrbitSpace p → ℂ) =ᵐ[carrierPushforward p]
      truncatedCompleted p hp Y hY s hs :=
  (truncatedCompleted_memLp_two p hp Y hY s hs).coeFn_toLp

theorem truncatedCompleted_integrable (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    Integrable (truncatedCompleted p hp Y hY s hs) (carrierPushforward p) := by
  letI : IsFiniteMeasure (carrierPushforward p) := ⟨carrierPushforward_finite p⟩
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (truncatedCompleted_memLp_two p hp Y hY s hs)

end ImbalancedChen.Part3.ActualTruncatedCompletedL220261026b
