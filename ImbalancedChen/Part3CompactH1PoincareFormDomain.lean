import ImbalancedChen.Part3CompactH1CanonicalSeedL2
import ImbalancedChen.Part3GammaCompactWeakSeedL2Continuity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The physical projection of the constructed H1 energy limit is the LITERAL
actual Gamma Poincare periodization of the raw compact H1 seed. Canonical
seed convergence and genuine fixed-compact weak Poincare continuity are
proved suppliers. No periodization-continuity or form-membership premise
occurs, and arbitrary compact H1 seeds are not inserted in smoothCore.
-/
namespace ImbalancedChen.Part3.CompactH1PoincareFormDomain20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a ProductKernelL2TranslationAverage20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedL2Transport20261026a GammaCompactSeedGraphTransport20261026a
open GammaCompactWeakSeedPoincareL220261026b GammaCompactWeakSeedL2Continuity20261026b
open Gamma0ActualEnergyCompletion20261025a
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open CompactH1QuotientEnergyLimit20261026b CompactH1CanonicalSeedL220261026b
open UpperRectangleMollifierGeometry20261026b

theorem zero_below_of_rectangle_support {F : Plane → ℂ} {L R a b : ℝ}
    (hs : tsupport F ⊆ openRect L R a b) : ∀ p : Plane, p.2 < a → F p = 0 := by
  intro p hp
  exact image_eq_zero_of_notMem_tsupport (fun h => not_lt_of_ge (hs h).2.1.le hp)

theorem upperSeed_support_rectangle {F : Plane → ℂ} {L R a b : ℝ}
    (hs : tsupport F ⊆ openRect L R a b) :
    Function.support (upperSeed F) ⊆ upperRectangle L R a b := by
  intro z hz
  have hp : (z.re,z.im) ∈ tsupport F := subset_closure hz
  exact ⟨⟨(hs hp).1.1.le,(hs hp).1.2.le⟩,⟨(hs hp).2.1.le,(hs hp).2.2.le⟩⟩

/-- The normalized ordinary H1 approximation converges in canonical
hyperbolic seed L2 as well, by the PROVED fixed-floor comparison. -/
theorem normalized_canonical_seed_tendsto
    {J : CompactH1Jet} {L R a b : ℝ} (P : NormalizedH1TensorSequence J L R a b)
    (ha : 0 < a) (hsJ : tsupport J.value ⊆ openRect L R a b) :
    ∃ (hSeq : ∀ k, MemLp (upperSeed (finiteChartFunction Finset.univ
        (fun i => (P.tensors k i).toCompactTensor))) 2 (volume : Measure UpperHalfPlane))
      (hJ : MemLp (upperSeed J.value) 2 (volume : Measure UpperHalfPlane)),
      Tendsto (fun k => (hSeq k).toLp (upperSeed (finiteChartFunction Finset.univ
        (fun i => (P.tensors k i).toCompactTensor)))) atTop (𝓝 (hJ.toLp (upperSeed J.value))) := by
  let F (k : ℕ) := finiteChartFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor)
  have hF (k : ℕ) : MemLp (F k) 2 volume := partial_memLp
    (finiteSmoothChart_contDiff Finset.univ (P.tensors k)) (P.compact k) (firstIndex 0)
  have hsF (k : ℕ) : tsupport (F k) ⊆ rect L R a b :=
    finiteTensor_tsupport_rect Finset.univ (P.tensors k) L R a b (fun i =>
      ⟨(P.horizontal_support k i).trans Ioo_subset_Icc_self,
        (P.vertical_support k i).trans Ioo_subset_Icc_self⟩)
  have hzF (k : ℕ) : ∀ p : Plane, p.2 < a → F k p = 0 := by
    intro p hp
    exact image_eq_zero_of_notMem_tsupport (fun h => not_lt_of_ge (hsF k h).2.1 hp)
  have hzJ := zero_below_of_rectangle_support hsJ
  let hU (k : ℕ) := upperSeed_memLp (hF k) ha (hzF k)
  let hJ := upperSeed_memLp J.value_memLp ha hzJ
  have hplain : Tendsto (fun k => (hF k).toLp (F k) - J.value_memLp.toLp J.value)
      atTop (𝓝 0) := by
    have h := (tendsto_pi_nhds.mp P.jet_tendsto 0).sub tendsto_const_nhds
    simpa only [sub_self] using h
  have hb (k : ℕ) := upperSeed_sub_norm_sq_le (hF k) J.value_memLp ha (hzF k) hzJ
  have hsq : Tendsto (fun k => ‖(hU k).toLp (upperSeed (F k)) - hJ.toLp (upperSeed J.value)‖^2)
      atTop (𝓝 0) := squeeze_zero (fun k => sq_nonneg _) hb
        (by simpa using tendsto_const_nhds.mul (hplain.norm.pow 2))
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  have hd : Tendsto (fun k => (hU k).toLp (upperSeed (F k)) - hJ.toLp (upperSeed J.value))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hn
  exact ⟨hU,hJ,by simpa only [sub_add_cancel,zero_add] using hd.add tendsto_const_nhds⟩

/-- A raw compact H1 seed has a TRUE actual quotient form vector whose
physical representative is its genuine Poincare periodization. Every
approximation and continuity input is constructed/proved in the chain. -/
theorem compactH1_periodization_has_energy_vector (N : ℕ) [NeZero N]
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    (hsJ : tsupport J.value ⊆ openRect L R a b) :
    ∃ e : EnergyCompletion N,
      ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        complexPoincare N (upperSeed J.value) := by
  obtain ⟨P⟩ := exists_normalizedH1TensorSequence J hx hy L R a b ha hLR hab hsJ
  obtain ⟨hSeq,hJ,hcanonical⟩ := normalized_canonical_seed_tendsto P ha hsJ
  let K := upperRectangle L R a b
  have hK : IsCompact K := upperRectangle_isCompact L R a b ha
  have hJs : Function.support (upperSeed J.value) ⊆ K := upperSeed_support_rectangle hsJ
  have hFs (k : ℕ) : Function.support (upperSeed (finiteChartFunction Finset.univ
      (fun i => (P.tensors k i).toCompactTensor))) ⊆ K := by
    exact (finiteCoreFunction_support_subset Finset.univ
      (fun i => (P.tensors k i).toCompactTensor)).trans (P.common_support k)
  have hquotient := weakSeedL2_tendsto N (upperSeed J.value) hJ
    (fun k => upperSeed (finiteChartFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor)))
    hSeq K hK hJs hFs hcanonical
  have hident (k : ℕ) : weakSeedL2 N
      (upperSeed (finiteChartFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor)))
      (hSeq k) K hK (hFs k) = physicalCore N (familyEnergyCore N (P.tensors k)) := by
    change weakSeedL2 N (finiteCoreFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor))
      (hSeq k) K hK (hFs k) = seedVector N ⟨P.size k,P.tensors k⟩
    rw [weakSeedL2_eq_seedL2 N _ (continuous_finiteCoreFunction _ _) K hK (hFs k)]
    exact compactInput_finiteTensor_eq N (P.tensors k) K hK (hFs k)
  have hphysical : Tendsto (fun k => physicalCore N (familyEnergyCore N (P.tensors k))) atTop
      (𝓝 (weakSeedL2 N (upperSeed J.value) hJ K hK hJs)) := by
    simpa only [hident] using hquotient
  obtain ⟨e,he,hprojection⟩ := normalized_sequence_energy_limit N P ha
  have heq : physicalProjection N e = weakSeedL2 N (upperSeed J.value) hJ K hK hJs :=
    tendsto_nhds_unique hprojection hphysical
  refine ⟨e,?_⟩
  rw [heq]
  exact weakSeedL2_ae N (upperSeed J.value) hJ K hK hJs

/-- The closed-form range statement for any actual quotient L2 vector
with the literal Poincare representative. This is an AE identification,
not an assumed energy/form-domain input. -/
theorem compactH1_periodization_mem_physical_range (N : ℕ) [NeZero N]
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    (hsJ : tsupport J.value ⊆ openRect L R a b)
    (u : QuotientL2 N)
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N (upperSeed J.value)) :
    u ∈ Set.range (physicalProjection N) := by
  obtain ⟨e,he⟩ := compactH1_periodization_has_energy_vector N J hx hy L R a b ha hLR hab hsJ
  exact ⟨e,Lp.ext (he.trans hu.symm)⟩

end
end ImbalancedChen.Part3.CompactH1PoincareFormDomain20261026b

