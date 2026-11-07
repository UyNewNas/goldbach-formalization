import ImbalancedChen.Part3WeakGradientUpperHalfPlaneRigidity
import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp
import ImbalancedChen.Part3CanonicalPlanarL2Unitary

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
Actual quotient L² representatives have unweighted planar L² on every
positive compactly contained rectangle. The proof zero-extends a genuine
compact pullback, uses the proved canonical-to-planar L² transport, and
undoes division by height only on a bounded rectangle. AE planar constancy
also descends to the ORIGINAL quotient measure, not a new measure. -/
namespace ImbalancedChen.Part3.GammaQuotientPlanarLocalL220261026a
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a
open ImbalancedChen.Part3.WeakGradientUpperHalfPlaneRigidity20261026a
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly

def compactUpperBox (a b c d : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc a b ∧ z.im ∈ Icc c d}

theorem compactUpperBox_isCompact (a b c d : ℝ) (hc : 0 < c) :
    IsCompact (compactUpperBox a b c d) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : ((↑) : UpperHalfPlane → ℂ) '' compactUpperBox a b c d =
      (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) '' (Icc a b ×ˢ Icc c d) := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(z.re,z.im),hz,by ext <;> rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨⟨p.1,p.2⟩,lt_of_lt_of_le hc hp.2.1⟩,hp,rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

/-- Literal planar representative of the original quotient vector. -/
def quotientPlanarRepresentative (N : ℕ) [NeZero N]
    (u : Lp ℂ 2 (carrierPushforward N)) : (ℝ × ℝ) → ℂ :=
  chartPullback (fun z => u (orbitProjection N z))

theorem quotientPlanarRepresentative_memLp_rectangle (N : ℕ) [NeZero N]
    (u : Lp ℂ 2 (carrierPushforward N)) (a b c d : ℝ) (hc : 0 < c) :
    MemLp (quotientPlanarRepresentative N u) 2
      (volume.restrict (openRectangle a b c d)) := by
  let K := compactUpperBox a b c d
  let Q := openRectangle a b c d
  let F : UpperHalfPlane → ℂ := fun z => u (orbitProjection N z)
  have hK : IsCompact K := compactUpperBox_isCompact a b c d hc
  have hQ : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
  have hlocal : MemLp F 2 ((volume : Measure UpperHalfPlane).restrict K) :=
    quotientLp_pullback_memLp N hK u
  have hglobal : MemLp (K.indicator F) 2 (volume : Measure UpperHalfPlane) :=
    (memLp_indicator_iff_restrict hK.measurableSet).2 hlocal
  have hforward : MemLp (forwardFunction (K.indicator F)) 2 (volume.restrict Q) :=
    (forwardFunction_memLp hglobal).restrict Q
  have hheight : MemLp (fun p : ℝ × ℝ => p.2) ∞ (volume.restrict Q) := by
    apply memLp_top_of_bound continuous_snd.aestronglyMeasurable d
    filter_upwards [ae_restrict_mem hQ] with p hp
    rw [Real.norm_eq_abs,abs_of_pos (lt_trans hc hp.2.1)]
    exact hp.2.2.le
  have hproduct : MemLp (fun p : ℝ × ℝ => p.2 • forwardFunction (K.indicator F) p)
      2 (volume.restrict Q) := hforward.smul hheight
  apply hproduct.ae_eq
  filter_upwards [ae_restrict_mem hQ] with p hp
  have hy : 0 < p.2 := lt_trans hc hp.2.1
  let z : UpperHalfPlane := ⟨⟨p.1,p.2⟩,hy⟩
  have hzK : z ∈ K := ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩
  change p.2 • forwardFunction (K.indicator F) p = chartPullback F p
  have hpupper : p ∈ upperChart := hy
  simp only [forwardFunction,unweightChart,chartPullback,dif_pos hpupper]
  change p.2 • ((p.2⁻¹ : ℝ) • K.indicator F z) = F z
  rw [Set.indicator_of_mem hzK,smul_smul,mul_inv_cancel₀ (ne_of_gt hy),one_smul]

theorem quotientPlanarRepresentative_memLp_exhaustion (N : ℕ) [NeZero N]
    (u : Lp ℂ 2 (carrierPushforward N)) (n : ℕ) :
    MemLp (quotientPlanarRepresentative N u) 2 (volume.restrict (exhaustionRectangle n)) :=
  quotientPlanarRepresentative_memLp_rectangle N u _ _ _ _
    (one_div_pos.mpr (exhaustionRadius_pos n))

theorem quotientPlanarRepresentative_at_chart (N : ℕ) [NeZero N]
    (u : Lp ℂ 2 (carrierPushforward N)) (z : UpperHalfPlane) :
    quotientPlanarRepresentative N u (chartMap z) = u (orbitProjection N z) :=
  chartPullback_at_upper _ z

/-- Constancy in the positive planar chart descends through the actual
carrier pushforward. No quotient-section or representative regularity is
assumed: Lp's native measurable representative supplies measurable equality. -/
theorem quotient_ae_const_of_planar_ae_const (N : ℕ) [NeZero N]
    (u : Lp ℂ 2 (carrierPushforward N)) (C : ℂ)
    (hC : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      0 < p.2 → quotientPlanarRepresentative N u p = C) :
    ∀ᵐ q ∂carrierPushforward N, u q = C := by
  have hu : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), u (orbitProjection N z) = C := by
    filter_upwards [chartMap_quasiMeasurePreserving.ae hC] with z hz
    simpa only [quotientPlanarRepresentative_at_chart] using hz z.im_pos
  change ∀ᵐ q ∂Measure.map (orbitProjection N)
    ((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)), u q = C
  apply (ae_map_iff (orbitProjection_measurable N).aemeasurable
    (measurableSet_eq_fun u.stronglyMeasurable.measurable measurable_const)).2
  exact ae_restrict_of_ae hu

end
end ImbalancedChen.Part3.GammaQuotientPlanarLocalL220261026a
