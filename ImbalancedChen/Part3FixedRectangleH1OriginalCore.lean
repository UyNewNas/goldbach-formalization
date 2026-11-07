import ImbalancedChen.Part3FixedRectangleH1PeriodizationCoherence
import ImbalancedChen.Part3PlanarFrechetCompactGreen

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original finite smooth tensor jets really belong to the new closed H1
model. Their bounded periodization is EXACTLY the original EnergyCore
embedding. Every fixed-rectangle jet has genuine normalized finite jets
inside one explicit larger rectangle, converging in the native closed
subspace norm; continuity of the new actual map then gives convergence
of the SAME original EnergyCore vectors to its value. No smooth-jet
membership, operator consistency, approximation or energy limit is assumed.
-/
namespace ImbalancedChen.Part3.FixedRectangleH1OriginalCore20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open CompactC2FiniteTensorApproximation20261026a SupportedH1FiniteTensorDensity20261026a
open ProductKernelL2TranslationAverage20261026a WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedL2Transport20261026a GammaCompactSeedGraphTransport20261026a
open GammaCompactWeakSeedPoincareL220261026b GammaCompactWeakSeedL2Continuity20261026b
open CanonicalPlanarL2UnitarySourceOnly Gamma0WholeChartCoordinateWeakEquation20261026b
open UpperRectangleMollifierGeometry20261026b PlanarFrechetCompactGreen20261026b
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open CompactH1CanonicalSeedL220261026b FixedRectangleH1JetSpace20261026b
open FixedRectangleH1EnergyLift20261026b FixedRectangleH1Periodization20261026b
open FixedRectangleH1PeriodizationCoherence20261026b

theorem test_inner_smoothJet {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (i : Fin 3)
    (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    inner ℂ (testClass ψ hψ hψc) (smoothJetClass hF hc i) =
      ∫ p, star (ψ p) * partialJet (firstIndex i) F p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hψc (p := (2 : ℝ≥0∞))).coeFn_toLp,
    (partial_memLp hF hc (firstIndex i)).coeFn_toLp] with p hp hq
  rw [hp,hq]
  simp only [RCLike.inner_apply',Complex.star_def]

/-- Native Frechet integration by parts proves ALL of the closed model's
weak identities for a smooth compact function. -/
theorem smoothJet_mem_weakJets {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : smoothJetClass hF hc ∈ weakJets := by
  intro vertical ψ hψ hψc
  change inner ℂ (testClass ψ hψ hψc) (smoothJetClass hF hc (derivativeIndex vertical)) +
    inner ℂ (testClass (directional (derivativeDirection vertical) ψ)
      (directional_smooth _ hψ) (directional_compact _ hψc)) (smoothJetClass hF hc 0) = 0
  rw [test_inner_smoothJet,test_inner_smoothJet]
  have hd : (fun p => partialJet (firstIndex (derivativeIndex vertical)) F p) =
      directional (derivativeDirection vertical) F := by
    cases vertical <;> funext p <;> rw [partialJet_eq_mixedJet hF] <;> rfl
  have hz : (fun p => partialJet (firstIndex 0) F p) = F := rfl
  simp_rw [hd,hz]
  exact add_eq_zero_iff_eq_neg.mpr (compact_first_green hψc hψ hF (derivativeDirection vertical))

theorem smoothJet_mem_supported {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (L R a b : ℝ) (hs : tsupport F ⊆ rect L R a b) :
    smoothJetClass hF hc ∈ supportedJets (rect L R a b) := by
  intro i
  filter_upwards [(partial_memLp hF hc (firstIndex i)).coeFn_toLp] with p hp
  intro hout
  rw [hp]
  exact image_eq_zero_of_notMem_tsupport
    (fun h => hout (hs (partialJet_tsupport_subset hF (firstIndex i) h)))

def smoothRectangleJet {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (L R a b : ℝ) (hs : tsupport F ⊆ rect L R a b) :
    RectangleJet L R a b :=
  ⟨smoothJetClass hF hc,⟨smoothJet_mem_supported hF hc L R a b hs,smoothJet_mem_weakJets hF hc⟩⟩

def finiteRectangleJet {n : ℕ} (T : Fin n → SmoothCompactTensor)
    (L R a b : ℝ)
    (hs : ∀ i, tsupport (T i).horizontal ⊆ Icc L R ∧ tsupport (T i).vertical ⊆ Icc a b) :
    RectangleJet L R a b :=
  smoothRectangleJet (finiteSmoothChart_contDiff Finset.univ T)
    (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
      (subset_tsupport.trans (finiteTensor_tsupport_rect Finset.univ T L R a b hs)))
    L R a b (finiteTensor_tsupport_rect Finset.univ T L R a b hs)

theorem finiteRectangleJet_seed_ae {n : ℕ} (T : Fin n → SmoothCompactTensor)
    (L R a b : ℝ)
    (hs : ∀ i, tsupport (T i).horizontal ⊆ Icc L R ∧ tsupport (T i).vertical ⊆ Icc a b) :
    seed (finiteRectangleJet T L R a b hs) =ᵐ[(volume : Measure UpperHalfPlane)]
      finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor) := by
  let V := finiteRectangleJet T L R a b hs
  have hp : representative V 0 =ᵐ[(volume : Measure Plane)]
      finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor) := by
    apply (representative_ae V 0).trans
    exact (partial_memLp (finiteSmoothChart_contDiff Finset.univ T) _ (firstIndex 0)).coeFn_toLp
  simpa only [seed,upperSeed,coordinateSeed,chartMap,Complex.measurableEquivRealProd_apply]
    using chartMap_quasiMeasurePreserving.ae_eq hp

/-- Exact consistency with ORIGINAL algebraic EnergyCore vectors, not an
unrelated lift of the same smooth function. -/
theorem periodization_finiteRectangleJet (N : ℕ) [NeZero N] {n : ℕ}
    (T : Fin n → SmoothCompactTensor) (L R a b : ℝ)
    (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ i, tsupport (T i).horizontal ⊆ Icc L R ∧ tsupport (T i).vertical ⊆ Icc a b) :
    periodization N L R a b hLR ha hab (finiteRectangleJet T L R a b hs) =
      coreEmbedding N (familyEnergyCore N T) := by
  let V := finiteRectangleJet T L R a b hs
  let F := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  let K := upperRectangle L R a b
  have hK : IsCompact K := upperRectangle_isCompact L R a b ha
  have hsource : Function.support F ⊆ K := by
    intro z hz
    have hp := (finiteTensor_tsupport_rect Finset.univ T L R a b hs) (subset_tsupport hz)
    exact hp
  have hcF : HasCompactSupport F := HasCompactSupport.of_support_subset_isCompact hK hsource
  have hcont : Continuous F := continuous_finiteCoreFunction _ _
  have hF : MemLp F 2 volume := hcont.memLp_of_hasCompactSupport hcF
  apply physicalProjection_injective N
  rw [physicalProjection_core]
  change physicalProjection N (energyLift N L R a b hLR ha hab V) = physicalCore N (familyEnergyCore N T)
  rw [energyLift_physical]
  have heq := weakSeedL2_congr_ae N (seed V) F (seed_memLp ha V) hF K hK
    (seed_support V) hsource (finiteRectangleJet_seed_ae T L R a b hs)
  change weakSeedL2 N (seed V) (seed_memLp ha V) K hK (seed_support V) = _
  rw [heq,weakSeedL2_eq_seedL2 N F hcont K hK hsource]
  exact compactInput_finiteTensor_eq N T K hK hsource

/-- Every actual normalized family has a typed model jet, including its
DERIVATIVE support and all distributional first-order identities. -/
def normalizedRectangleJet {J : CompactH1Jet} {L R a b : ℝ}
    (P : NormalizedH1TensorSequence J L R a b) (k : ℕ) : RectangleJet L R a b :=
  finiteRectangleJet (P.tensors k) L R a b (fun i =>
    ⟨(P.horizontal_support k i).trans Ioo_subset_Icc_self,
      (P.vertical_support k i).trans Ioo_subset_Icc_self⟩)

theorem normalizedRectangleJet_tendsto {J : CompactH1Jet} {L R a b : ℝ}
    (P : NormalizedH1TensorSequence J L R a b) (v : RectangleJet L R a b)
    (hv : h1JetClass J = v.val) :
    Tendsto (normalizedRectangleJet P) atTop (𝓝 v) := by
  apply tendsto_subtype_rng.2
  simpa only [normalizedRectangleJet,finiteRectangleJet,smoothRectangleJet,hv] using P.jet_tendsto

/-- The genuine finite approximation occurs INSIDE one explicit closed
model. The energy convergence of ORIGINAL core images is then obtained
from continuity and exact operator consistency, not from a supplied limit. -/
theorem exists_original_core_model_approximation (N : ℕ) [NeZero N]
    (L R a b : ℝ) (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (v : RectangleJet L R a b) :
    ∃ (hK : rect L R a b ⊆ rect (L-1) (R+1) (a/2) (b+1))
      (P : NormalizedH1TensorSequence (compactJet v) (L-1) (R+1) (a/2) (b+1)),
      Tendsto (normalizedRectangleJet P) atTop (𝓝 (inclusion hK v)) ∧
      Tendsto (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) atTop
        (𝓝 (periodization N L R a b hLR ha hab v)) := by
  have hLR' : L-1 < R+1 := by linarith
  have hab' : a/2 < b+1 := by linarith
  have ho : rect L R a b ⊆ openRect (L-1) (R+1) (a/2) (b+1) := by
    intro p hp
    constructor <;> constructor <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2]
  have hK : rect L R a b ⊆ rect (L-1) (R+1) (a/2) (b+1) := by
    intro p hp
    exact ⟨⟨(ho hp).1.1.le,(ho hp).1.2.le⟩,⟨(ho hp).2.1.le,(ho hp).2.2.le⟩⟩
  obtain ⟨P⟩ := exists_normalizedH1TensorSequence (compactJet v)
    (representative_compact v 1) (representative_compact v 2)
    (L-1) (R+1) (a/2) (b+1) (half_pos ha) hLR' hab'
    ((representative_support v 0).trans ho)
  have hjet : Tendsto (normalizedRectangleJet P) atTop (𝓝 (inclusion hK v)) :=
    normalizedRectangleJet_tendsto P (inclusion hK v) (compactJet_class v)
  have ht := ((periodization N (L-1) (R+1) (a/2) (b+1) hLR'.le (half_pos ha) hab'.le).continuous.tendsto
    (inclusion hK v)).comp hjet
  have hcore (k : ℕ) : periodization N (L-1) (R+1) (a/2) (b+1)
      hLR'.le (half_pos ha) hab'.le (normalizedRectangleJet P k) =
      coreEmbedding N (familyEnergyCore N (P.tensors k)) :=
    periodization_finiteRectangleJet N (P.tensors k) (L-1) (R+1) (a/2) (b+1)
      hLR'.le (half_pos ha) hab'.le (fun i =>
        ⟨(P.horizontal_support k i).trans Ioo_subset_Icc_self,
          (P.vertical_support k i).trans Ioo_subset_Icc_self⟩)
  have htarget := periodization_inclusion N L R a b (L-1) (R+1) (a/2) (b+1)
    hLR ha hab hLR'.le (half_pos ha) hab'.le hK v
  exact ⟨hK,P,hjet,by simpa only [hcore,htarget] using ht⟩

end
end ImbalancedChen.Part3.FixedRectangleH1OriginalCore20261026b

