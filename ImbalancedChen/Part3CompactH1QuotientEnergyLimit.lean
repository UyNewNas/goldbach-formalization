import ImbalancedChen.Part3LocalH1TensorDifferenceABI
import ImbalancedChen.Part3GammaFiniteSeedCoordinateH1Budget

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Genuine compact H1 seed approximation produces a Cauchy sequence in the
ACTUAL Gamma quotient energy norm, and hence a vector in EnergyCompletion.
The common compact support and positive floor are fixed before the seed
and its pairwise differences. Native planar first-jet convergence, actual
finite subtraction, and the proved quantitative energy transfer are used;
no Cauchy, form-domain, periodization-continuity or completion-limit premise
is assumed. Identification with raw nonsmooth periodization is separate.
-/
namespace ImbalancedChen.Part3.CompactH1QuotientEnergyLimit20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a CompactProductKernelSixJet20261025a
open SupportedH1FiniteTensorDensity20261026a ProductKernelL2TranslationAverage20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGlobalOverlap20261025a Gamma0CompactGreenProductL120261025a
open Gamma0ActualEnergyCompletion20261025a
open GammaFiniteSeedCoordinateH1Budget20261026b
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open UpperRectangleMollifierGeometry20261026b

abbrev TensorJet := Fin 3 → ProductKernelL2TranslationAverage20261026a.PlaneL2

theorem jet_norm_sq_integral {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (i : Fin 3) :
    ‖smoothJetClass hF hc i‖^2 = ∫ p, ‖partialJet (firstIndex i) F p‖^2 := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(partial_memLp hF hc (firstIndex i)).coeFn_toLp] with p hp
  rw [hp]

def energyTransferSq (N : ℕ) (L R a b : ℝ) : ℝ :=
  (compactOverlapBound N (upperRectangle L R a b) : ℝ) * ((a⁻¹)^2 + 2)

theorem energyTransferSq_nonneg (N : ℕ) (L R a b : ℝ) : 0 ≤ energyTransferSq N L R a b := by
  unfold energyTransferSq
  positivity

/-- Quantitative actual energy transfer stated in terms of the NATIVE
three-component planar L2 jet norm. One constant applies to every family
and every append/subtract family inside the same allowed rectangle. -/
theorem finiteFamily_energy_norm_sq_le (N : ℕ) [NeZero N] {n : ℕ}
    (T : Fin n → SmoothCompactTensor) (L R a b : ℝ) (ha : 0 < a)
    (hc : HasCompactSupport (finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor)))
    (hs : ∀ i, tsupport (T i).horizontal ⊆ Ioo L R ∧ tsupport (T i).vertical ⊆ Ioo a b) :
    ‖familyEnergyCore N T‖^2 ≤ energyTransferSq N L R a b *
      ‖smoothJetClass (finiteSmoothChart_contDiff Finset.univ T) hc‖^2 := by
  let F := finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hF : ContDiff ℝ ∞ F := finiteSmoothChart_contDiff Finset.univ T
  let V : TensorJet := smoothJetClass hF hc
  have hsK : finiteCompactTensorSupportK Finset.univ (fun i => (T i).toCompactTensor) ⊆
      upperRectangle L R a b := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨⟨((hs i).1 hi.1).1.le,((hs i).1 hi.1).2.le⟩,
      ⟨((hs i).2 hi.2).1.le,((hs i).2 hi.2).2.le⟩⟩
  have hb := finite_seed_coordinate_energy_bound N (⟨n,T⟩ : SmoothSeed)
    (upperRectangle_isCompact L R a b ha) hsK ha (fun z hz => hz.2.1)
  have hmass : (∫ p, ‖F p‖^2) = ‖V 0‖^2 := by
    rw [jet_norm_sq_integral hF hc]
    rfl
  have hx (p : Plane) : partialJet (firstIndex 1) F p = sliceDx F p := by
    rw [partialJet_eq_mixedJet hF]
    change directional ex F p = sliceDx F p
    exact ProductConvolutionSecondDerivatives20261026a.directional_x_eq_slice hF p
  have hy (p : Plane) : partialJet (firstIndex 2) F p = sliceDy F p := by
    rw [partialJet_eq_mixedJet hF]
    change directional ey F p = sliceDy F p
    exact ProductConvolutionSecondDerivatives20261026a.directional_y_eq_slice hF p
  have hi (i : Fin 3) : Integrable (fun p => ‖partialJet (firstIndex i) F p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (partial_memLp hF hc (firstIndex i)).aestronglyMeasurable).mp
      (partial_memLp hF hc (firstIndex i))
  have hgrad : (∫ p, coordinateGradientSq F p) = ‖V 1‖^2 + ‖V 2‖^2 := by
    have heq : coordinateGradientSq F = fun p =>
        ‖partialJet (firstIndex 1) F p‖^2 + ‖partialJet (firstIndex 2) F p‖^2 := by
      funext p
      rw [hx p,hy p]
      rfl
    rw [heq,integral_add (hi 1) (hi 2),← jet_norm_sq_integral hF hc 1,
      ← jet_norm_sq_integral hF hc 2]
  change ‖familyEnergyCore N T‖^2 ≤
    (compactOverlapBound N (upperRectangle L R a b) : ℝ) *
      ((a⁻¹)^2 * (∫ p, ‖F p‖^2) + ∫ p, coordinateGradientSq F p) at hb
  rw [hmass,hgrad] at hb
  have hcoord (i : Fin 3) : ‖V i‖^2 ≤ ‖V‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_le_pi_norm V i)
  have hsum : (a⁻¹)^2 * ‖V 0‖^2 + (‖V 1‖^2 + ‖V 2‖^2) ≤ ((a⁻¹)^2 + 2) * ‖V‖^2 := by
    calc
      _ ≤ (a⁻¹)^2 * ‖V‖^2 + (‖V‖^2 + ‖V‖^2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hcoord 0) (sq_nonneg _))
          (add_le_add (hcoord 1) (hcoord 2))
      _ = _ := by ring
  exact hb.trans (by
    simpa only [energyTransferSq,mul_assoc] using
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (compactOverlapBound N (upperRectangle L R a b))))

/-- Pairwise ACTUAL energy differences are controlled by their ACTUAL
native planar jet differences. The difference is rendered in the
original finite seed ABI before applying the common-support estimate. -/
theorem normalized_energy_difference_bound (N : ℕ) [NeZero N]
    {J : CompactH1Jet} {L R a b : ℝ} (P : NormalizedH1TensorSequence J L R a b)
    (ha : 0 < a) (j k : ℕ) :
    ‖familyEnergyCore N (P.tensors j) - familyEnergyCore N (P.tensors k)‖^2 ≤
      energyTransferSq N L R a b *
        ‖smoothJetClass (finiteSmoothChart_contDiff Finset.univ (P.tensors j)) (P.compact j) -
          smoothJetClass (finiteSmoothChart_contDiff Finset.univ (P.tensors k)) (P.compact k)‖^2 := by
  have hs := differenceTensors_factor_supports (P.tensors j) (P.tensors k) L R a b
    (fun i => ⟨P.horizontal_support j i,P.vertical_support j i⟩)
    (fun i => ⟨P.horizontal_support k i,P.vertical_support k i⟩)
  have h := finiteFamily_energy_norm_sq_le N (differenceTensors (P.tensors j) (P.tensors k))
    L R a b ha (differenceTensors_compact _ _ (P.compact j) (P.compact k)) hs
  rw [differenceTensors_energyCore,differenceTensors_jet] at h
  exact h

/-- The H1 approximation sequence is proved Cauchy in the original
quotient EnergyCompletion; this is not a desired-form-membership input. -/
theorem normalized_energy_cauchy (N : ℕ) [NeZero N]
    {J : CompactH1Jet} {L R a b : ℝ} (P : NormalizedH1TensorSequence J L R a b)
    (ha : 0 < a) :
    CauchySeq (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) := by
  let V (k : ℕ) : TensorJet :=
    smoothJetClass (finiteSmoothChart_contDiff Finset.univ (P.tensors k)) (P.compact k)
  let B := energyTransferSq N L R a b
  have hB : 0 ≤ B := energyTransferSq_nonneg N L R a b
  have hB1 : 0 < B + 1 := by linarith
  have hnorm (j k : ℕ) :
      ‖familyEnergyCore N (P.tensors j) - familyEnergyCore N (P.tensors k)‖ ≤ (B+1)*‖V j - V k‖ := by
    have hs := normalized_energy_difference_bound N P ha j k
    have hcoef : B ≤ (B+1)^2 := by nlinarith [sq_nonneg B]
    have hsq : ‖familyEnergyCore N (P.tensors j) - familyEnergyCore N (P.tensors k)‖^2 ≤
        ((B+1)*‖V j - V k‖)^2 := by
      calc
        _ ≤ B * ‖V j - V k‖^2 := hs
        _ ≤ (B+1)^2 * ‖V j - V k‖^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ = _ := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB1.le (norm_nonneg _))).mp hsq
  have hvc : CauchySeq V := P.jet_tendsto.cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := Metric.cauchySeq_iff.mp hvc (ε/(B+1)) (div_pos hε hB1)
  refine ⟨K,fun j hj k hk => ?_⟩
  calc
    _ = ‖familyEnergyCore N (P.tensors j) - familyEnergyCore N (P.tensors k)‖ := by
      rw [dist_eq_norm,← map_sub,coreEmbedding_norm]
    _ ≤ (B+1)*‖V j - V k‖ := hnorm j k
    _ < (B+1)*(ε/(B+1)) := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hK j hj k hk) hB1
    _ = ε := by field_simp [ne_of_gt hB1]

/-- A genuine actual energy vector and its physical quotient L2 limit
are both obtained from the proved Cauchy sequence. Raw nonsmooth
periodization is not substituted for that physical limit without a
separate proved L2 transport theorem. -/
theorem normalized_sequence_energy_limit (N : ℕ) [NeZero N]
    {J : CompactH1Jet} {L R a b : ℝ} (P : NormalizedH1TensorSequence J L R a b)
    (ha : 0 < a) :
    ∃ e : EnergyCompletion N,
      Tendsto (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) atTop (𝓝 e) ∧
      Tendsto (fun k => physicalCore N (familyEnergyCore N (P.tensors k))) atTop
        (𝓝 (physicalProjection N e)) := by
  obtain ⟨e,he⟩ := cauchySeq_tendsto_of_complete (normalized_energy_cauchy N P ha)
  refine ⟨e,he,?_⟩
  have h := ((physicalProjection N).continuous.tendsto e).comp he
  simpa only [physicalProjection_core] using h

/-- No approximating sequence or form vector is among the hypotheses.
A genuine compact H1 seed itself supplies a normalized approximation and
an ACTUAL quotient EnergyCompletion limit. -/
theorem compactH1_has_quotient_energy_limit (N : ℕ) [NeZero N]
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    (hs : tsupport J.value ⊆ openRect L R a b) :
    ∃ (P : NormalizedH1TensorSequence J L R a b) (e : EnergyCompletion N),
      Tendsto (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) atTop (𝓝 e) ∧
      Tendsto (fun k => physicalCore N (familyEnergyCore N (P.tensors k))) atTop
        (𝓝 (physicalProjection N e)) := by
  obtain ⟨P⟩ := exists_normalizedH1TensorSequence J hx hy L R a b ha hLR hab hs
  obtain ⟨e,he,hphysical⟩ := normalized_sequence_energy_limit N P ha
  exact ⟨P,e,he,hphysical⟩

end
end ImbalancedChen.Part3.CompactH1QuotientEnergyLimit20261026b


