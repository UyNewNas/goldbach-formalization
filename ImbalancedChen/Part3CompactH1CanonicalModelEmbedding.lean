import ImbalancedChen.Part3CompactUpperWeakJetPeriodization
import ImbalancedChen.Part3FixedRectangleH1OriginalCore
import ImbalancedChen.Part3PositiveCompactTensorLpApproximation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Raw compact H1 data enter the canonical native weak-jet model without a
caller rectangle or a desired model-membership hypothesis. Literal weak
first derivatives prove the native all-test L2 identities. Compact positive
support of the three components supplies an actual common positive source
rectangle. The canonical linear energy map then has the LITERAL raw-seed
Poincare physical value, with every AE seed change paid by the actual
compact weak-Poincare bound. Original finite core consistency is retained.
-/
namespace ImbalancedChen.Part3.CompactH1CanonicalModelEmbedding20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a SupportedH1FiniteTensorDensity20261026a
open ProductKernelL2TranslationAverage20261026a WeakH1ProductMollifierDerivative20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0SmoothCompactTensorCore20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactWeakSeedPoincareL220261026b CanonicalPlanarL2UnitarySourceOnly
open Gamma0WholeChartCoordinateWeakEquation20261026b UpperRectangleMollifierGeometry20261026b
open PlanarFrechetCompactGreen20261026b PositiveCompactTensorLpApproximation20261025a
open LocalH1Tests20261026b LocalH1TensorDifferenceABI20261026b CompactH1CanonicalSeedL220261026b
open FixedRectangleH1JetSpace20261026b FixedRectangleH1EnergyLift20261026b
open FixedRectangleH1Periodization20261026b FixedRectangleH1OriginalCore20261026b
open CompactUpperWeakJetModel20261026b CompactUpperWeakJetPeriodization20261026b

theorem test_inner_h1Jet (J : CompactH1Jet) (i : Fin 3)
    (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    inner ℂ (testClass ψ hψ hc) (h1JetClass J i) = ∫ p, star (ψ p) * component J i p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hc (p := (2 : ℝ≥0∞))).coeFn_toLp,
    (component_memLp J i).coeFn_toLp] with p hp hq
  rw [hp,hq]
  simp only [RCLike.inner_apply',Complex.star_def]

/-- The distributional weak derivative definition itself proves the
native sesquilinear closed-subspace identities for every compact test. -/
theorem h1Jet_mem_weakJets (J : CompactH1Jet) : h1JetClass J ∈ weakJets := by
  intro vertical ψ hψ hc
  change inner ℂ (testClass ψ hψ hc) (h1JetClass J (derivativeIndex vertical)) +
    inner ℂ (testClass (directional (derivativeDirection vertical) ψ)
      (directional_smooth _ hψ) (directional_compact _ hc)) (h1JetClass J 0) = 0
  rw [test_inner_h1Jet,test_inner_h1Jet]
  have hsc : HasCompactSupport (fun p => star (ψ p)) := hc.comp_left (g := star) (by simp)
  cases vertical
  · change (∫ p, star (ψ p)*J.dx p) + (∫ p, star (directional ex ψ p)*J.value p) = 0
    have hw := J.weak_dx (fun p => star (ψ p)) hψ.star hsc
    simp_rw [directional_star] at hw
    linear_combination hw
  · change (∫ p, star (ψ p)*J.dy p) + (∫ p, star (directional ey ψ p)*J.value p) = 0
    have hw := J.weak_dy (fun p => star (ψ p)) hψ.star hsc
    simp_rw [directional_star] at hw
    linear_combination hw

theorem exists_positive_source (F : Plane → ℂ) (hc : HasCompactSupport F)
    (hp : tsupport F ⊆ {p : Plane | 0 < p.2}) :
    ∃ Q : SourceRectangle, tsupport F ⊆ Q.container := by
  obtain ⟨A,a,b,hA,ha,hab,hs⟩ := compact_positive_support_rectangle F hc hp
  exact ⟨⟨-A,A,a,b,by linarith,ha,hab⟩,hs⟩

/-- A single actual positive rectangle contains all three compact jet
components; it is derived from compactness and the positive chart. -/
theorem exists_compactH1_source (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hp : ∀ i : Fin 3, tsupport (component J i) ⊆ {p : Plane | 0 < p.2}) :
    ∃ Q : SourceRectangle, ∀ i : Fin 3, tsupport (component J i) ⊆ Q.container := by
  obtain ⟨Q0,h0⟩ := exists_positive_source J.value J.value_compact (hp 0)
  obtain ⟨Q1,h1⟩ := exists_positive_source J.dx hx (hp 1)
  obtain ⟨Q2,h2⟩ := exists_positive_source J.dy hy (hp 2)
  refine ⟨(Q0.common Q1).common Q2,?_⟩
  intro i
  fin_cases i
  · exact (h0.trans (Q0.subset_common_left Q1)).trans ((Q0.common Q1).subset_common_left Q2)
  · exact (h1.trans (Q0.subset_common_right Q1)).trans ((Q0.common Q1).subset_common_left Q2)
  · exact h2.trans ((Q0.common Q1).subset_common_right Q2)

theorem h1Jet_mem_supported (J : CompactH1Jet) (Q : SourceRectangle)
    (hs : ∀ i : Fin 3, tsupport (component J i) ⊆ Q.container) :
    h1JetClass J ∈ supportedJets Q.container := by
  intro i
  filter_upwards [(component_memLp J i).coeFn_toLp] with p hp
  intro hout
  rw [hp]
  exact image_eq_zero_of_notMem_tsupport (fun h => hout (hs i h))

/-- No weak-jet domain membership or support rectangle is supplied by
the caller: both are proved from the raw compact H1 data. -/
def modelJet (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hp : ∀ i : Fin 3, tsupport (component J i) ⊆ {p : Plane | 0 < p.2}) : CompactUpperJet :=
  ⟨h1JetClass J,⟨h1Jet_mem_weakJets J,by
    obtain ⟨Q,hQ⟩ := exists_compactH1_source J hx hy hp
    exact ⟨Q,h1Jet_mem_supported J Q hQ⟩⟩⟩

@[simp] theorem modelJet_val (J : CompactH1Jet) (hx : HasCompactSupport J.dx)
    (hy : HasCompactSupport J.dy)
    (hp : ∀ i : Fin 3, tsupport (component J i) ⊆ {p : Plane | 0 < p.2}) :
    (modelJet J hx hy hp).val = h1JetClass J := rfl

/-- Canonical energy value of raw compact H1 data. The model map is the
single already proved complex-linear map, not a new existential lift. -/
def canonicalEnergy (N : ℕ) [NeZero N] (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hp : ∀ i : Fin 3, tsupport (component J i) ⊆ {p : Plane | 0 < p.2}) : EnergyCompletion N :=
  compactPeriodization N (modelJet J hx hy hp)

theorem canonicalEnergy_physical_ae (N : ℕ) [NeZero N] (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hp : ∀ i : Fin 3, tsupport (component J i) ⊆ {p : Plane | 0 < p.2}) :
    (physicalProjection N (canonicalEnergy N J hx hy hp) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperSeed J.value) := by
  obtain ⟨Q,hQ⟩ := exists_compactH1_source J hx hy hp
  let v := modelJet J hx hy hp
  have hv : v.val ∈ supportedJets Q.container := h1Jet_mem_supported J Q hQ
  let u := toRectangle v Q hv
  have hplain : representative u 0 =ᵐ[(volume : Measure Plane)] J.value :=
    (representative_ae u 0).trans J.value_memLp.coeFn_toLp
  have hseed : seed u =ᵐ[(volume : Measure UpperHalfPlane)] upperSeed J.value := by
    simpa only [seed,upperSeed,coordinateSeed,chartMap,Complex.measurableEquivRealProd_apply]
      using chartMap_quasiMeasurePreserving.ae_eq hplain
  have hz : ∀ p : Plane, p.2 < Q.floor → J.value p = 0 := by
    intro p hlow
    exact image_eq_zero_of_notMem_tsupport (fun h => not_lt_of_ge (hQ 0 h).2.1 hlow)
  have hraw : MemLp (upperSeed J.value) 2 (volume : Measure UpperHalfPlane) :=
    upperSeed_memLp J.value_memLp Q.floor_pos hz
  have hsource : Function.support (upperSeed J.value) ⊆
      upperRectangle Q.left Q.right Q.floor Q.ceiling := by
    intro z hz
    exact hQ 0 (subset_tsupport hz)
  let K := upperRectangle Q.left Q.right Q.floor Q.ceiling
  have hK : IsCompact K := upperRectangle_isCompact _ _ _ _ Q.floor_pos
  have heq := weakSeedL2_congr_ae N (seed u) (upperSeed J.value)
    (seed_memLp Q.floor_pos u) hraw K hK (seed_support u) hsource hseed
  have hrawout := weakSeedL2_ae N (upperSeed J.value) hraw K hK hsource
  rw [← heq] at hrawout
  have htrace := (weakSeedL2_ae N (seed u) (seed_memLp Q.floor_pos u) K hK (seed_support u)).symm.trans hrawout
  exact (compactPeriodization_physical_ae N v Q hv).trans htrace

/-- The canonical model map still agrees EXACTLY with the original
finite smooth EnergyCore embedding, in every valid source rectangle. -/
theorem compactPeriodization_original_finite (N : ℕ) [NeZero N] {n : ℕ}
    (T : Fin n → SmoothCompactTensor) (Q : SourceRectangle)
    (hs : ∀ i, tsupport (T i).horizontal ⊆ Icc Q.left Q.right ∧
      tsupport (T i).vertical ⊆ Icc Q.floor Q.ceiling) :
    compactPeriodization N (includeRectangle Q
      (finiteRectangleJet T Q.left Q.right Q.floor Q.ceiling hs)) =
      coreEmbedding N (familyEnergyCore N T) := by
  rw [compactPeriodization_includeRectangle]
  exact periodization_finiteRectangleJet N T Q.left Q.right Q.floor Q.ceiling
    Q.horizontal_order Q.floor_pos Q.vertical_order hs

end
end ImbalancedChen.Part3.CompactH1CanonicalModelEmbedding20261026b
