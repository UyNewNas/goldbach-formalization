import ImbalancedChen.P5ZU1011OriginalSixteenU10FullHarmonic
import ImbalancedChen.P5ZU1011OriginalPairedFixedMaskHarmonic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The actual joint U10+retained-U11 source has one ORIGINAL sixteen-policy
nonlinear harmonic mean. U10's entire low-fourth band is unmasked; U11's
full high-fourth band retains the SAME literal E complement. Exact native
union/disjointness and real integral gluing occur before the two proved
band limits are added. This is not a claim that the previous U11-only
mean was already a joint mean, nor a minimum of separately averaged policies.
Only fixed actual adopted row families receive mask limit theorems here.
Arbitrary E is admitted in the finite source identity only. Original
cardinality-to-kernel, physical AP and H248 licences remain separate.
-/

namespace ImbalancedChen.P5Z.U1011OriginalJointHarmonic

noncomputable section
open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenNativeHarmonic
open Certificates.PairedV2

abbrev Row := FullMask.Row

def actualMinimum : LogFour → ℝ := U1011OriginalSixteenStateKernel.actualMinimum
def weighted (v : LogFour) : ℝ := actualMinimum v*harmonicDensity v

def nativeJoint (N : ℕ) (E : ℕ×ℕ → Prop) (f : LogFour → ℝ) : ℝ :=
  ∑ t ∈ P5U1011JointOverlap.jointSelector N E, f (coordinates N t)/(Nat.totient (fullPrefix t) : ℝ)

/-- Exact same-E native joint identity. Low-fourth labels are never
masked; the complete original high-fourth interval keeps exactly ¬E. -/
theorem nativeJoint_eq_native10_add_native11 {N : ℕ} (hN : 1<N)
    (E : ℕ×ℕ → Prop) (f : LogFour → ℝ) :
    nativeJoint N E f=U1011OriginalSixteenU10Geometry.native10 N f+nativeHarmonicSum N E f := by
  have hNr : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hHD : (N : ℝ)^(19/125 : ℝ)≤(N : ℝ)^(59/250 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  simpa only [nativeJoint,P5U1011JointOverlap.jointSelector,
    U1011OriginalSixteenU10Geometry.native10,P5U10OriginalMean.selector,nativeHarmonicSum,U11Adaptive.source] using
    sum_chenY1011JointPrimeSelector N ((N : ℝ)^(417/5000 : ℝ))
      ((N : ℝ)^(19/125 : ℝ)) ((N : ℝ)^(59/250 : ℝ)) E hHD
      (fun t => f (coordinates N t)/(Nat.totient (fullPrefix t) : ℝ))

def jointDomain (S : Finset Row) : Set LogFour := U1011OriginalSixteenU10Geometry.domain10 ∪
  originalDomain (U1011OriginalPairedFixedMaskHarmonic.outerUnion S)
def jointIntegral (S : Finset Row) : ℝ := ∫ v in jointDomain S,weighted v

theorem domain10_disjoint_originalDomain (mask : Set (ℝ×ℝ)) :
    Disjoint U1011OriginalSixteenU10Geometry.domain10 (originalDomain mask) := by
  apply Set.disjoint_left.mpr
  intro v h10 h11
  exact (not_lt_of_ge h11.2.2.2.2.1) h10.2.2.2.2

theorem integrableOn_weighted_D10 : IntegrableOn weighted U1011OriginalSixteenU10Geometry.domain10 := by
  have hi := integrable_finsetSum (Finset.univ : Finset U1011OriginalSixteenU10FullHarmonic.State)
    (fun s _ => U1011OriginalSixteenU10FullHarmonic.integrable_piece_weighted_indicator s)
  have heq : (fun v => ∑ s : U1011OriginalSixteenU10FullHarmonic.State,
      (U1011OriginalSixteenU10FullHarmonic.piece s).indicator weighted v)=
      U1011OriginalSixteenU10Geometry.domain10.indicator weighted := by
    funext v
    exact U1011OriginalSixteenU10FullHarmonic.sum_piece_weighted_indicator v
  rw [heq] at hi
  exact (integrable_indicator_iff U1011OriginalSixteenU10Geometry.measurableSet_domain10).1 hi

theorem integrableOn_weighted_D11 (mask : Set (ℝ×ℝ)) : IntegrableOn weighted (originalDomain mask) := by
  apply U1011OriginalSixteenFullHarmonic.integrableOn_actual_weighted.mono_set
  intro v hv
  exact ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,hv.2.2.2.2.2.1,by simp⟩

theorem jointIntegral_eq_band_sum (S : Finset Row) :
    jointIntegral S=U1011OriginalSixteenU10FullHarmonic.integral10+
      ∫ v in originalDomain (U1011OriginalPairedFixedMaskHarmonic.outerUnion S),weighted v := by
  have hD11 : MeasurableSet (originalDomain (U1011OriginalPairedFixedMaskHarmonic.outerUnion S)) := by
    rw [U1011OriginalPairedFixedMaskHarmonic.originalDomain_outerUnion]
    exact U1011OriginalPairedFixedMaskHarmonic.measurableSet_keptDomain S
  exact setIntegral_union (domain10_disjoint_originalDomain _) hD11
    integrableOn_weighted_D10 (integrableOn_weighted_D11 _)

/-- Full native joint harmonic limit for a STATIC subfamily of the actual
17572 adopted rows. Both band limits are direct proved original16 suppliers;
there is no hMean or local-cell-mean input. -/
theorem tendsto_nativeJoint_staticRows (S : Finset Row) :
    Tendsto (fun N : ℕ => nativeJoint N
      (U1011OriginalPairedRowPrimeTests.nativeMask
        (U1011OriginalPairedFixedMaskHarmonic.outerUnion S) N) actualMinimum)
      atTop (𝓝 (jointIntegral S)) := by
  have h10 := U1011OriginalSixteenU10FullHarmonic.tendsto_native10
  have h11 := U1011OriginalPairedFixedMaskHarmonic.tendsto_native_staticRows S
  have ht := h10.add h11
  have heq : (fun N : ℕ => U1011OriginalSixteenU10Geometry.native10 N actualMinimum+
      nativeHarmonicSum N (U1011OriginalPairedRowPrimeTests.nativeMask
        (U1011OriginalPairedFixedMaskHarmonic.outerUnion S) N) actualMinimum) =ᶠ[atTop]
      (fun N : ℕ => nativeJoint N (U1011OriginalPairedRowPrimeTests.nativeMask
        (U1011OriginalPairedFixedMaskHarmonic.outerUnion S) N) actualMinimum) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact (nativeJoint_eq_native10_add_native11 hN _ _).symm
  rw [jointIntegral_eq_band_sum]
  exact ht.congr' heq

/-- The truly joint UNMASKED source includes all U10 low-band labels as
well as all U11 high-band labels. This is stronger than U11-only mean. -/
theorem tendsto_nativeJoint_unmasked :
    Tendsto (fun N : ℕ => nativeJoint N (fun _ => False) actualMinimum) atTop
      (𝓝 (jointIntegral ∅)) := by
  have houter : U1011OriginalPairedFixedMaskHarmonic.outerUnion (∅ : Finset Row)=∅ := by
    simp [U1011OriginalPairedFixedMaskHarmonic.outerUnion]
  have hE (N : ℕ) : U1011OriginalPairedRowPrimeTests.nativeMask
      (U1011OriginalPairedFixedMaskHarmonic.outerUnion (∅ : Finset Row)) N=(fun _ => False) := by
    funext p
    simp [houter,U1011OriginalPairedRowPrimeTests.nativeMask]
  simpa only [hE] using tendsto_nativeJoint_staticRows (∅ : Finset Row)

theorem tendsto_nativeJoint_actual_adopted_mask :
    Tendsto (fun N : ℕ => nativeJoint N (FullMask.P1E0E1.deletionMask (N : ℝ)) actualMinimum)
      atTop (𝓝 (jointIntegral (Finset.univ : Finset Row))) := by
  simpa only [U1011OriginalPairedFixedMaskHarmonic.outerUnion_all,
    U1011OriginalPairedRowPrimeTests.nativeMask_actual_adopted] using
    tendsto_nativeJoint_staticRows (Finset.univ : Finset Row)

theorem tendsto_nativeJoint_actual_e0_mask :
    Tendsto (fun N : ℕ => nativeJoint N (FullMask.P1E0E1.e0DeletionMask (N : ℝ)) actualMinimum)
      atTop (𝓝 (jointIntegral U1011OriginalPairedFixedMaskHarmonic.e0Rows)) := by
  simpa only [U1011OriginalPairedFixedMaskHarmonic.outerUnion_e0,
    U1011OriginalPairedRowPrimeTests.nativeMask,FullMask.P1E0E1.e0DeletionMask] using
    tendsto_nativeJoint_staticRows U1011OriginalPairedFixedMaskHarmonic.e0Rows

theorem tendsto_nativeJoint_actual_e1_mask :
    Tendsto (fun N : ℕ => nativeJoint N (FullMask.P1E0E1.e1DeletionMask (N : ℝ)) actualMinimum)
      atTop (𝓝 (jointIntegral U1011OriginalPairedFixedMaskHarmonic.e1Rows)) := by
  simpa only [U1011OriginalPairedFixedMaskHarmonic.outerUnion_e1,
    U1011OriginalPairedRowPrimeTests.nativeMask,FullMask.P1E0E1.e1DeletionMask] using
    tendsto_nativeJoint_staticRows U1011OriginalPairedFixedMaskHarmonic.e1Rows

end
end ImbalancedChen.P5Z.U1011OriginalJointHarmonic

