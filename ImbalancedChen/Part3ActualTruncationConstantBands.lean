import ImbalancedChen.Part3ActualTruncatedCompletedL2
import ImbalancedChen.Part3PrimeCommonHeightAnnulusConversion
import ImbalancedChen.Part3ActualStrictZeroTailMeasure

/-! Genuine annular constant terms between two actual truncation heights.
The signed level difference is identified pointwise with the two literal
constant bands. Individual bands are actual native L2 functions, obtained
by measurable restriction of that derived L2 difference, not by assuming
square integrability of either full high-cusp constant lift.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b
open ImbalancedChen.Part3.StrictInfinityHighIndicator20261026b
open ImbalancedChen.Part3.PrimeCommonHeightAnnulusConversion20261026b
open ImbalancedChen.Part3.ActualStrictZeroTailMeasure20261026b
open ImbalancedChen.Part3.ActualHighCuspRadialLifts20261026b
open ImbalancedChen.Part3.ActualCompletedTwoCuspTruncation20261026b
open ImbalancedChen.Part3.ActualTruncatedCompletedL220261026b
open ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a

namespace ImbalancedChen.Part3.ActualTruncationConstantBands20261026b

def cuspProjection (p : ℕ) (hp : p.Prime) (b : Bool) (z : UpperHalfPlane) :
    Gamma0OrbitSpace p := orbitProjection p (if b then frickeSL p hp.pos • z else z)

def cuspTail (p : ℕ) (hp : p.Prime) (Y : ℝ) (b : Bool) : Set (Gamma0OrbitSpace p) :=
  if b then zeroHighNeighborhood p hp Y else infinityHighNeighborhood p Y

def cuspAnnulus (p : ℕ) (hp : p.Prime) (Y Z : ℝ) (b : Bool) : Set (Gamma0OrbitSpace p) :=
  cuspTail p hp Y b \ cuspTail p hp Z b

def cuspConstantLift (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) (b : Bool) :
    Gamma0OrbitSpace p → ℂ :=
  if b then zeroConstantLift p hp Y hY s else infinityConstantLift p Y hY s

def cuspConstantBand (p : ℕ) (hp : p.Prime) (Y Z : ℝ) (hY : 1 ≤ Y) (hZ : 1 ≤ Z)
    (s : ℂ) (b : Bool) : Gamma0OrbitSpace p → ℂ :=
  cuspConstantLift p hp Y hY s b - cuspConstantLift p hp Z hZ s b

theorem cuspProjection_measurable (p : ℕ) (hp : p.Prime) (b : Bool) :
    Measurable (cuspProjection p hp b) := by
  cases b
  · exact orbitProjection_measurable p
  · exact (orbitProjection_measurable p).comp
      (continuous_const_smul (frickeSL p hp.pos)).measurable

theorem cuspTail_measurable (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (b : Bool) :
    MeasurableSet (cuspTail p hp Y b) := by
  cases b
  · exact infinityHighNeighborhood_measurable p Y hY
  · exact zeroHighNeighborhood_measurable p hp Y hY

theorem cuspTail_antitone (p : ℕ) (hp : p.Prime) (b : Bool) :
    Antitone (fun Y => cuspTail p hp Y b) := by
  intro Y Z hYZ
  cases b <;> rintro q ⟨z, hz, rfl⟩ <;> exact ⟨z, hYZ.trans_lt hz, rfl⟩

theorem cuspAnnulus_measurable (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool) : MeasurableSet (cuspAnnulus p hp Y Z b) :=
  (cuspTail_measurable p hp Y hY b).diff (cuspTail_measurable p hp Z (hY.trans hYZ) b)

theorem cuspAnnuli_disjoint (p : ℕ) (hp : p.Prime) (Y Z : ℝ) (hY : 1 ≤ Y) :
    Disjoint (cuspAnnulus p hp Y Z false) (cuspAnnulus p hp Y Z true) :=
  (prime_high_neighborhoods_disjoint hp Y hY).mono sdiff_subset sdiff_subset

theorem cuspProjection_mem_higher_iff (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool) (z : UpperHalfPlane) (hz : Y < z.im) :
    cuspProjection p hp b z ∈ cuspTail p hp Z b ↔ Z < z.im := by
  cases b
  · constructor
    · rintro ⟨w, hw, he⟩
      obtain ⟨n, hn⟩ := (high_projection_eq_iff_translation p Y hY z w hz
        (hYZ.trans_lt hw)).mp he.symm
      simpa only [hn, translate_im] using hw
    · intro h
      exact ⟨z, h, rfl⟩
  · constructor
    · rintro ⟨w, hw, he⟩
      obtain ⟨n, hn⟩ := (fricke_high_projection_eq_iff_translation p hp.pos Y hY z w hz
        (hYZ.trans_lt hw)).mp he.symm
      simpa only [hn, translate_im] using hw
    · intro h
      exact ⟨z, h, rfl⟩

theorem cuspConstantLift_measurable (p : ℕ) (hp : p.Prime) (Y : ℝ)
    (hY : 1 ≤ Y) (s : ℂ) (b : Bool) : Measurable (cuspConstantLift p hp Y hY s b) := by
  cases b
  · exact infinityConstantLift_measurable p Y hY s
  · exact zeroConstantLift_measurable p hp Y hY s

theorem cuspConstantLift_high (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (b : Bool) (z : UpperHalfPlane) (hz : Y < z.im) :
    cuspConstantLift p hp Y hY s b (cuspProjection p hp b z) =
      physicalCuspConstant p s b z.im := by
  cases b
  · exact (infinityRadialLift_high p Y hY _ z hz).trans (positiveProfile_pos _ _ z.im_pos)
  · exact (zeroRadialLift_high p hp Y hY _ z hz).trans (positiveProfile_pos _ _ z.im_pos)

theorem cuspConstantLift_off (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (b : Bool) (q : Gamma0OrbitSpace p) (hq : q ∉ cuspTail p hp Y b) :
    cuspConstantLift p hp Y hY s b q = 0 := by
  cases b
  · exact infinityRadialLift_off p Y hY _ q hq
  · exact zeroRadialLift_off p hp Y hY _ q hq

theorem cuspTail_surjective (p : ℕ) (hp : p.Prime) (Y : ℝ) (b : Bool)
    (q : Gamma0OrbitSpace p) (hq : q ∈ cuspTail p hp Y b) :
    ∃ z : UpperHalfPlane, Y < z.im ∧ cuspProjection p hp b z = q := by
  cases b <;> exact hq

theorem cuspConstantBand_measurable (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (s : ℂ) (b : Bool) :
    Measurable (cuspConstantBand p hp Y Z hY hZ s b) :=
  (cuspConstantLift_measurable p hp Y hY s b).sub
    (cuspConstantLift_measurable p hp Z hZ s b)

theorem cuspConstantBand_high (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (b : Bool)
    (z : UpperHalfPlane) (hz : Y < z.im) (hzZ : z.im ≤ Z) :
    cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b (cuspProjection p hp b z) =
      physicalCuspConstant p s b z.im := by
  have hoff : cuspProjection p hp b z ∉ cuspTail p hp Z b := by
    rw [cuspProjection_mem_higher_iff p hp Y Z hY hYZ b z hz]
    exact not_lt.mpr hzZ
  change cuspConstantLift p hp Y hY s b _ - cuspConstantLift p hp Z (hY.trans hYZ) s b _ = _
  rw [cuspConstantLift_high p hp Y hY s b z hz,
    cuspConstantLift_off p hp Z (hY.trans hYZ) s b _ hoff, sub_zero]

theorem cuspConstantBand_off (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (b : Bool)
    (q : Gamma0OrbitSpace p) (hq : q ∉ cuspAnnulus p hp Y Z b) :
    cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q = 0 := by
  by_cases hz : q ∈ cuspTail p hp Z b
  · obtain ⟨z, hz, rfl⟩ := cuspTail_surjective p hp Z b q hz
    change cuspConstantLift p hp Y hY s b _ - cuspConstantLift p hp Z (hY.trans hYZ) s b _ = 0
    rw [cuspConstantLift_high p hp Y hY s b z (hYZ.trans_lt hz),
      cuspConstantLift_high p hp Z (hY.trans hYZ) s b z hz, sub_self]
  · have hy : q ∉ cuspTail p hp Y b := fun hy => hq ⟨hy, hz⟩
    change cuspConstantLift p hp Y hY s b q - cuspConstantLift p hp Z (hY.trans hYZ) s b q = 0
    rw [cuspConstantLift_off p hp Y hY s b q hy,
      cuspConstantLift_off p hp Z (hY.trans hYZ) s b q hz, sub_self]

theorem cuspConstantBand_on (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (b : Bool)
    (q : Gamma0OrbitSpace p) (hq : q ∈ cuspAnnulus p hp Y Z b) :
    cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q = cuspConstantLift p hp Y hY s b q := by
  change cuspConstantLift p hp Y hY s b q - cuspConstantLift p hp Z (hY.trans hYZ) s b q = _
  rw [cuspConstantLift_off p hp Z (hY.trans hYZ) s b q hq.2, sub_zero]

/-- Increasing the cutoff restores precisely the two actual constant
bands. The identity is of literal quotient functions, at every point. -/
theorem truncation_level_difference (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    truncatedCompleted p hp Z hZ s hs - truncatedCompleted p hp Y hY s hs =
      cuspConstantBand p hp Y Z hY hZ s false + cuspConstantBand p hp Y Z hY hZ s true := by
  funext q
  change (_ - _ - _) - (_ - _ - _) = (_ - _) + (_ - _)
  ring

/-- Each individual cusp band is an actual measurable restriction of
the derived global L2 level difference; no full constant lift L2 input. -/
theorem cuspConstantBand_eq_indicator_difference (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) (b : Bool) :
    cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b =
      (cuspAnnulus p hp Y Z b).indicator
        (truncatedCompleted p hp Z (hY.trans hYZ) s hs - truncatedCompleted p hp Y hY s hs) := by
  classical
  rw [truncation_level_difference]
  funext q
  by_cases hq : q ∈ cuspAnnulus p hp Y Z b
  · rw [indicator_of_mem hq]
    cases b
    · have ho : q ∉ cuspAnnulus p hp Y Z true := fun h =>
        (Set.disjoint_left.mp (cuspAnnuli_disjoint p hp Y Z hY)) hq h
      simp only [Pi.add_apply, cuspConstantBand_off p hp Y Z hY hYZ s true q ho, add_zero]
    · have ho : q ∉ cuspAnnulus p hp Y Z false := fun h =>
        (Set.disjoint_left.mp (cuspAnnuli_disjoint p hp Y Z hY)) h hq
      simp only [Pi.add_apply, cuspConstantBand_off p hp Y Z hY hYZ s false q ho, zero_add]
  · rw [indicator_of_notMem hq, cuspConstantBand_off p hp Y Z hY hYZ s b q hq]

theorem cuspConstantBand_memLp_two (p : ℕ) [NeZero p] (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) (b : Bool) :
    MemLp (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b) 2 (carrierPushforward p) := by
  rw [cuspConstantBand_eq_indicator_difference p hp Y Z hY hYZ s hs b]
  exact ((truncatedCompleted_memLp_two p hp Z (hY.trans hYZ) s hs).sub
    (truncatedCompleted_memLp_two p hp Y hY s hs)).indicator
      (cuspAnnulus_measurable p hp Y Z hY hYZ b)

def cuspConstantBandL2 (p : ℕ) [NeZero p] (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) (b : Bool) :
    Lp ℂ 2 (carrierPushforward p) :=
  (cuspConstantBand_memLp_two p hp Y Z hY hYZ s hs b).toLp
    (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b)

theorem cuspConstantBandL2_coeFn (p : ℕ) [NeZero p] (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) (b : Bool) :
    (cuspConstantBandL2 p hp Y Z hY hYZ s hs b : Gamma0OrbitSpace p → ℂ) =ᵐ[carrierPushforward p]
      cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b :=
  (cuspConstantBand_memLp_two p hp Y Z hY hYZ s hs b).coeFn_toLp

theorem truncation_L2_level_difference (p : ℕ) [NeZero p] (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    truncatedCompletedL2 p hp Z (hY.trans hYZ) s hs - truncatedCompletedL2 p hp Y hY s hs =
      cuspConstantBandL2 p hp Y Z hY hYZ s hs false + cuspConstantBandL2 p hp Y Z hY hYZ s hs true := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (truncatedCompletedL2 p hp Z (hY.trans hYZ) s hs)
      (truncatedCompletedL2 p hp Y hY s hs),
    Lp.coeFn_add (cuspConstantBandL2 p hp Y Z hY hYZ s hs false)
      (cuspConstantBandL2 p hp Y Z hY hYZ s hs true),
    truncatedCompletedL2_coeFn p hp Z (hY.trans hYZ) s hs,
    truncatedCompletedL2_coeFn p hp Y hY s hs,
    cuspConstantBandL2_coeFn p hp Y Z hY hYZ s hs false,
    cuspConstantBandL2_coeFn p hp Y Z hY hYZ s hs true] with q hsub hadd hvalZ hvalY h0 h1
  rw [hsub, hadd, Pi.sub_apply, Pi.add_apply, hvalZ, hvalY, h0, h1]
  exact congrFun (truncation_level_difference p hp Y Z hY (hY.trans hYZ) s hs) q

end ImbalancedChen.Part3.ActualTruncationConstantBands20261026b
