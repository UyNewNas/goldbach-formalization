import ImbalancedChen.Part3JointSmoothFiniteCuspPackets
import ImbalancedChen.Part3CuspPhysicalFourierProjectionIdentification

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite compact-height Fourier graph data are approximated by actual
jointly-C-infinity packets, with explicit vertical as well as horizontal
derivatives. Their native mixed-L2 coordinates equal the literal finite
coefficient sums. One common positive compact height support works for
every approximating packet. This retains data discarded by the earlier
classical-graph-only finite-mode inclusion.
-/
namespace ImbalancedChen.Part3.JointSmoothPacketHeightDensity20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z ClosedHorizontalCuspTail20261026a
open CuspZeroMeanSmoothApproximationSourceOnly SeparatedWeakCuspGraphApproximation20261026a
open CommonHeightSmoothApproximation20261026b PhysicalHeightCommonSmoothing20261026b
open FiniteHeightModeGraphClosure20261026b JointSmoothFiniteCuspPackets20261026b
open CuspPhysicalFourierProjectionIdentification20261026b
attribute [local instance] Measure.Subtype.measureSpace
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

theorem packet_heightSupport_compact (P : SmoothPacket) :
    IsCompact {y : PositiveHeight | (y : ℝ) ∈ P.heightSupport} := by
  apply Subtype.isCompact_iff.mpr
  have he : ((↑) : PositiveHeight → ℝ) ''
      {y : PositiveHeight | (y : ℝ) ∈ P.heightSupport} = P.heightSupport := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, P.positive_heightSupport hy⟩, hy, rfl⟩
  rwa [he]

theorem packet_profile_memLp (P : SmoothPacket) (k : ℤ)
    (μ : Measure PositiveHeight) [IsFiniteMeasureOnCompacts μ] :
    MemLp (fun y : PositiveHeight => P.profile k (y : ℝ)) 2 μ := by
  apply ((P.smooth_profile k).continuous.comp continuous_subtype_val).memLp_of_hasCompactSupport
  apply (packet_heightSupport_compact P).of_isClosed_subset isClosed_tsupport
  apply closure_minimal _
    (P.compact_heightSupport.isClosed.preimage continuous_subtype_val)
  intro y hy
  exact P.profile_support k (subset_tsupport _ hy)

private theorem native_sum_ae {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) (v : ι → Lp ℂ 2 μ) (f : ι → α → ℂ)
    (h : ∀ i ∈ s, (v i : α → ℂ) =ᵐ[μ] f i) :
    ((∑ i ∈ s, v i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 μ
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (v i) (∑ j ∈ s, v j),
        h i (Finset.mem_insert_self i s), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
        with x hx hi hs
      simpa only [Pi.add_apply, hi, hs] using hx

/-- Exact native identification of the new smooth packet with the actual
physical finite coefficient reconstruction, in both quotient spaces. -/
theorem packet_coordinates_eq_finiteCoefficientPair (P : SmoothPacket) (a : ℝ)
    (hw : ∀ k, MemLp (fun y : PositiveHeight => P.profile k (y : ℝ)) 2 heightMeasure)
    (hr : ∀ k, MemLp (fun y : PositiveHeight => P.profile k (y : ℝ)) 2
      (volume : Measure PositiveHeight)) :
    P.coordinates a = finiteCoefficientPair a P.modes
      (fun k y => P.profile k (y : ℝ)) hw hr := by
  apply Prod.ext
  · apply Lp.ext
    have h := native_sum_ae P.modes
      (fun k => (coefficientPair a k (fun y => P.profile k (y : ℝ)) (hw k) (hr k)).1)
      (fun k z => AddCircle.fourier k z.1 * P.profile k (z.2 : ℝ))
      (fun k hk => coefficientPair_value_ae a k _ (hw k) (hr k))
    exact (P.value_memLp a).coeFn_toLp.trans (by
      simpa only [finiteCoefficientPair, Prod.fst_sum, SmoothPacket.value] using h.symm)
  · apply Lp.ext
    have h := native_sum_ae P.modes
      (fun k => (coefficientPair a k (fun y => P.profile k (y : ℝ)) (hw k) (hr k)).2)
      (fun k z => frequency k * AddCircle.fourier k z.1 * P.profile k (z.2 : ℝ))
      (fun k hk => coefficientPair_derivative_ae a k _ (hw k) (hr k))
    exact (P.dx_memLp a).coeFn_toLp.trans (by
      simpa only [finiteCoefficientPair, Prod.snd_sum, SmoothPacket.dx] using h.symm)

/-- A sequence of genuine smooth packets, all with the same positive
compact height support, approximates a finite weak Fourier graph pair. -/
theorem finiteCoefficientPair_smooth_packet_sequence {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (s : Finset ℤ) (hzero : ∀ k ∈ s, k ≠ 0)
    (f : ℤ → PositiveHeight → ℂ)
    (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight))
    (hs : ∀ k, Function.support (f k) ⊆ {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}) :
    ∃ P : ℕ → SmoothPacket,
      (∀ n, (P n).heightSupport = Icc (A / 2) (B + A / 2)) ∧
      Tendsto (fun n => (P n).coordinates a) atTop
        (𝓝 (finiteCoefficientPair a s f hw hr)) := by
  classical
  obtain ⟨g, hg⟩ := exists_physical_common_height_sequence hA hAB f hw hr hs
  let P (n : ℕ) : SmoothPacket :=
    { modes := s
      modes_nonzero := hzero
      profile := g n
      smooth_profile := fun k => (hg n k).1
      heightSupport := Icc (A / 2) (B + A / 2)
      compact_heightSupport := isCompact_Icc
      positive_heightSupport := fun y hy => lt_of_lt_of_le (half_pos hA) hy.1
      profile_support := fun k => (hg n k).2.2.1 }
  have hgw (n : ℕ) (k : ℤ) := (hg n k).2.2.2.1
  have hgr (n : ℕ) (k : ℤ) := (hg n k).2.2.2.2.1
  have hc (k : ℤ) : Tendsto (fun n => coefficientPair a k
      (fun y => g n k (y : ℝ)) (hgw n k) (hgr n k)) atTop
        (𝓝 (coefficientPair a k (f k) (hw k) (hr k))) := by
    have hv := toLp_tendsto_of_tolerance
      ((hw k).mono_measure (Measure.restrict_le_self (s := CuspZeroMeanEnergyOnlyTail20261025a.strictHeightTail a)))
      (fun n => (hgw n k).mono_measure Measure.restrict_le_self)
      (fun n => (eLpNorm_restrict_le _ _ _ _).trans (hg n k).2.2.2.2.2.1)
    have hd := toLp_tendsto_of_tolerance
      ((hr k).mono_measure (Measure.restrict_le_self (s := CuspZeroMeanEnergyOnlyTail20261025a.strictHeightTail a)))
      (fun n => (hgr n k).mono_measure Measure.restrict_le_self)
      (fun n => (eLpNorm_restrict_le _ _ _ _).trans (hg n k).2.2.2.2.2.2)
    exact (tensorVector_tendsto_right (functionHeightMeasure a) (functionMeasure a)
      (functionMeasure_product a) (AddCircle.fourierLp 2 k) hv).prodMk_nhds
      (tensorVector_tendsto_right (derivativeHeightMeasure a) (derivativeMeasure a)
        (derivativeMeasure_product a) (frequency k • AddCircle.fourierLp 2 k) hd)
  refine ⟨P, fun n => rfl, ?_⟩
  have he (n : ℕ) : (P n).coordinates a = finiteCoefficientPair a s
      (fun k y => g n k (y : ℝ)) (hgw n) (hgr n) :=
    packet_coordinates_eq_finiteCoefficientPair (P n) a (hgw n) (hgr n)
  have ht := tendsto_finsetSum s (fun k hk => hc k)
  simpa only [he, finiteCoefficientPair] using ht

theorem finiteCoefficientPair_mem_smoothPacketCore_closure {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (s : Finset ℤ) (hzero : ∀ k ∈ s, k ≠ 0)
    (f : ℤ → PositiveHeight → ℂ)
    (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight))
    (hs : ∀ k, Function.support (f k) ⊆ {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}) :
    finiteCoefficientPair a s f hw hr ∈ closure (smoothPacketCore a) := by
  obtain ⟨P, hs, ht⟩ := finiteCoefficientPair_smooth_packet_sequence hA hAB s hzero f hw hr hs
  exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall fun n => subset_closure ⟨P n, rfl⟩)

end
end ImbalancedChen.Part3.JointSmoothPacketHeightDensity20261026b
