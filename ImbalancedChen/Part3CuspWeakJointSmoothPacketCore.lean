import ImbalancedChen.Part3JointSmoothPacketHeightDensity
import ImbalancedChen.Part3CuspGeneralWeakGraphClosure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every genuine physical horizontal weak pair of zero horizontal mean on
a positive tail has a SINGLE sequence of actual jointly-C-infinity
finite Fourier packets converging in BOTH physical graph norms.

The proof retains the stronger smooth packet core throughout finite
Fourier reconstruction and height exhaustion, then selects a metric
diagonal sequence. Each packet has one compact positive height support
shared by its modes and both literal first derivatives. For arbitrary
unbounded-height input these compact supports may expand with n. There
is no assertion of vertical derivative convergence without vertical
weak regularity of the input.
-/
namespace ImbalancedChen.Part3.CuspWeakJointSmoothPacketCore20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a ActualZeroMeanCylinderFourierUnitary20261026a
open ActualCylinderFiniteFourierProjection20261026b
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open CuspPhysicalWeakTailModes20261026b CuspWeakCylinderFourierModes20261026b
open CuspPhysicalHeightExhaustion20261026b CuspHeightCutoffFourierModes20261026b
open CuspPhysicalFourierProjectionIdentification20261026b CuspPhysicalCutoffRealization20261026b
open CuspUpperBandMixedFourierConvergence20261026b CuspGeneralWeakGraphClosure20261026b
open FiniteHeightModeGraphClosure20261026b JointSmoothFiniteCuspPackets20261026b
open JointSmoothPacketHeightDensity20261026b CommonHeightSmoothApproximation20261026b
attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem raw_ac_weighted : rawCylinderMeasure ≪ cylinderMeasure := by
  have hh : (volume : Measure PositiveHeight) ≪ heightMeasure :=
    withDensity_absolutelyContinuous'
      heightDensity_continuous.measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun y => ENNReal.coe_ne_zero.mpr (heightDensity_pos y).ne')
  exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl hh

private theorem localized_support (K : Set PositiveHeight) (hK : MeasurableSet K)
    (F : CylinderL2) :
    ∀ᵐ z ∂cylinderMeasure, z.2 ∉ K → heightLocalizedCylinder K hK F z = 0 := by
  filter_upwards [indicatorVector_ae (univ ×ˢ K) (MeasurableSet.univ.prod hK) F] with z hz
  intro hnot
  simpa [heightLocalizedCylinder, hnot] using hz

/-- The finite Fourier net lands in the stronger closure of ACTUAL
jointly smooth packets, and hence so does its mixed-norm compact limit. -/
theorem compact_localized_pair_mem_smoothPacketCore_closure {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) (hmean : F ∈ zeroMeanCylinder) :
    (valueTailMap a (heightLocalizedCylinder {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
      (((isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)).measurableSet) F),
     bandDerivativeMap a B (hA.trans_le hAB)
      (heightLocalizedCylinder {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
        (((isClosed_le continuous_const continuous_subtype_val).inter
          (isClosed_le continuous_subtype_val continuous_const)).measurableSet) G))
      ∈ closure (smoothPacketCore a) := by
  classical
  let K : Set PositiveHeight := {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
  have hK : MeasurableSet K :=
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).measurableSet
  have hGmean : G ∈ zeroMeanCylinder := by
    change cylinderCoefficient 0 G = 0
    rw [weak_cylinder_coefficient hweak 0]
    simp [modeFrequency]
  have ht := mixed_finiteFourierProjection_tendsto a B (hA.trans_le hAB)
    ⟨heightLocalizedCylinder K hK F, heightLocalizedCylinder_zero_mean K hK hmean⟩
    ⟨heightLocalizedCylinder K hK G, heightLocalizedCylinder_zero_mean K hK hGmean⟩
  apply isClosed_closure.mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  let hr := compact_localizedProfile_raw_memLp (A := A) (hA.trans_le hAB) F
  have heq :
      (valueTailMap a (finiteFourierProjection s (heightLocalizedCylinder K hK F)),
       bandDerivativeMap a B (hA.trans_le hAB)
        (finiteFourierProjection s (heightLocalizedCylinder K hK G))) =
      indexedCoefficientPair a s (localizedProfile K F) (localizedProfile_memLp K hK F) hr := by
    apply Prod.ext
    · apply Lp.ext
      exact (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
        (by simpa only [one_smul] using
          (Measure.restrict_le_self : functionMeasure a ≤ cylinderMeasure)) _).trans
          (localized_projection_value_ae a s K hK F hr).symm
    · have hs := finiteFourierProjection_preserves_height_support K hK s
        (heightLocalizedCylinder K hK G) (localized_support K hK G)
      have hsRaw := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq
        (raw_ac_weighted.ae_eq hs)
      apply Lp.ext
      filter_upwards [bandDerivativeMap_ae a B (hA.trans_le hAB)
        (finiteFourierProjection s (heightLocalizedCylinder K hK G)),
        localized_projection_derivative_ae a s K hK hweak hr, hsRaw]
          with z hmap hpair hs
      rw [hmap]
      by_cases hu : z ∈ upperCylinder B
      · simpa [hu] using hpair.symm
      · have hzK : z.2 ∉ K := fun hk => hu ⟨mem_univ _, hk.2⟩
        rw [hs hzK] at hpair
        simp [hu, hpair]
  rw [heq]
  have he : indexedCoefficientPair a s (localizedProfile K F)
      (localizedProfile_memLp K hK F) hr =
      finiteCoefficientPair a (s.image ((↑) : NonzeroMode → ℤ))
        (localizedProfile K F) (localizedProfile_memLp K hK F) hr := by
    unfold indexedCoefficientPair finiteCoefficientPair
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact Subtype.ext hxy
  rw [he]
  apply finiteCoefficientPair_mem_smoothPacketCore_closure hA hAB
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact n.property
  · intro k y hy
    by_contra hnot
    exact hy (by simp [localizedProfile, K, hnot])

private theorem value_map_tailValue (a : ℝ) (u : FunctionL2 a) :
    valueTailMap a (tailValue a u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
      (by simpa only [one_smul] using
        (Measure.restrict_le_self : functionMeasure a ≤ cylinderMeasure)) (tailValue a u),
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq (tailValue_ae a u),
    ae_restrict_mem (strictCylinderTail_measurable a)] with z hmap hv hz
  simp only [hmap, hv, indicator_of_mem hz]

private theorem derivative_map_tailDerivative {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (d : DerivativeL2 a) (hs : ∀ᵐ z ∂derivativeMeasure a, z ∉ upperCylinder B → d z = 0) :
    bandDerivativeMap a B hB (tailDerivative a ha d) = d := by
  have hd := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq
    (raw_ac_weighted.ae_eq (tailDerivative_ae a ha d))
  apply Lp.ext
  filter_upwards [bandDerivativeMap_ae a B hB (tailDerivative a ha d), hd, hs,
    ae_restrict_mem (strictCylinderTail_measurable a)] with z hmap hd hs hz
  rw [hmap]
  by_cases hu : z ∈ upperCylinder B
  · simp [hu, hd, hz]
  · simp [hu, hs hu]

/-- Genuine weak testing and actual horizontal zero mean imply density
of the jointly smooth finite Fourier core in the physical mixed norm. -/
theorem weak_pair_mem_smoothPacketCore_closure {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative 1 a u d)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    (u, d) ∈ closure (smoothPacketCore a) := by
  have hnative : HasWeakWeightedCylinderDerivative (tailValue a u) (tailDerivative a ha d) := by
    simpa only [Complex.ofReal_one, one_smul] using physical_tail_native_weak ha hweak
  have hF : tailValue a u ∈ zeroMeanCylinder := by
    apply (mem_zeroMeanCylinder_iff _).mpr
    have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
        ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
        tailValue a u (p.2, p.1) = (strictCylinderTail a).indicator u (p.2, p.1) :=
      (Measure.measurePreserving_swap.quasiMeasurePreserving).ae (tailValue_ae a u)
    filter_upwards [ae_ae_of_ae_prod hswap, hmean] with y hy hm
    rw [integral_congr_ae hy]
    by_cases hay : a < (y : ℝ)
    · simpa [strictCylinderTail, strictHeightTail, hay] using hm hay
    · simp [strictCylinderTail, strictHeightTail, hay]
  have hcut (n : ℕ) : physicalHeightCutoff a n (u, d) ∈ closure (smoothPacketCore a) := by
    have hB : 0 < a + (n : ℝ) + 1 := by positivity
    have hAB : a ≤ a + (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (R := ℝ) n]
    have hc := compact_localized_pair_mem_smoothPacketCore_closure (a := a)
      ha hAB hnative hF
    have hdSupport : ∀ᵐ z ∂derivativeMeasure a,
        z ∉ upperCylinder (a + (n : ℝ) + 1) → (physicalHeightCutoff a n (u, d)).2 z = 0 := by
      filter_upwards [indicatorVector_ae (cylinderHeightBand a n)
        (cylinderHeightBand_measurable a n) d] with z hz
      intro hu
      have hnot : z ∉ cylinderHeightBand a n := fun hband => hu ⟨mem_univ _, hband.2.2⟩
      simpa [physicalHeightCutoff, hnot] using hz
    rw [← physicalHeightCutoff_value_realization a n (u, d),
      ← physicalHeightCutoff_derivative_realization ha n (u, d),
      value_map_tailValue, derivative_map_tailDerivative ha hB _ hdSupport] at hc
    exact hc
  exact isClosed_closure.mem_of_tendsto (physicalHeightCutoff_tendsto a (u, d))
    (Eventually.of_forall hcut)

/-- The metric diagonal gives ONE sequence, rather than nested height,
Fourier and smoothing limits. Every term retains all explicit joint
smoothness, zero-mean and compact positive-support data of SmoothPacket. -/
theorem weak_pair_joint_smooth_packet_sequence {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative 1 a u d)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    ∃ P : ℕ → SmoothPacket,
      (∀ n, dist ((P n).coordinates a) (u, d) < tolerance n) ∧
      Tendsto (fun n => (P n).coordinates a) atTop (𝓝 (u, d)) := by
  classical
  have hc := weak_pair_mem_smoothPacketCore_closure ha hweak hmean
  have hp (n : ℕ) : ∃ P : SmoothPacket, dist (P.coordinates a) (u, d) < tolerance n := by
    obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hc (tolerance n) (tolerance_pos n)
    obtain ⟨P, rfl⟩ := hq
    exact ⟨P, by simpa only [dist_comm] using hdist⟩
  choose P hP using hp
  refine ⟨P, hP, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hP n).le) tolerance_tendsto

end
end ImbalancedChen.Part3.CuspWeakJointSmoothPacketCore20261026b
