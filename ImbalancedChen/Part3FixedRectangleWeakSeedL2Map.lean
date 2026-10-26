import ImbalancedChen.Part3FixedRectangleH1Periodization

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine bounded complex-linear map from ALL ordinary planar L2 to the
actual Gamma quotient L2: insert the fixed positive rectangle indicator,
lift the raw seed to canonical hyperbolic L2, and use actual weak-seed
Poincare periodization. Indicator contraction, the a^-2 height comparison,
and the sharp compact-overlap quotient bound prove its norm estimate.
Native Lp AE add/scalar laws, actual compact weak-Poincare AE congruence,
and genuine compact-seed linearity prove linearity. No gradient, H1,
form membership, seed continuity or output supplier is assumed.
-/
namespace ImbalancedChen.Part3.FixedRectangleWeakSeedL2Map20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a ProductKernelL2TranslationAverage20261026a
open SupportedH1FiniteTensorDensity20261026a CompactH1CanonicalSeedL220261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0CompactGlobalOverlap20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedL2Transport20261026a GammaCompactWeakSeedPoincareL220261026b
open GammaCompactWeakSeedL2Continuity20261026b CanonicalPlanarL2UnitarySourceOnly
open Gamma0WholeChartCoordinateWeakEquation20261026b UpperRectangleMollifierGeometry20261026b
open LocalH1Tests20261026b FixedRectangleH1Periodization20261026b

def indicatorValue (L R a b : ℝ) (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) : Plane → ℂ :=
  (rect L R a b).indicator u

theorem indicatorValue_memLp (L R a b : ℝ) (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    MemLp (indicatorValue L R a b u) 2 (volume : Measure Plane) :=
  (Lp.memLp u).indicator (measurableSet_Icc.prod measurableSet_Icc)

theorem indicatorValue_norm_sq_le (L R a b : ℝ) (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    ‖(indicatorValue_memLp L R a b u).toLp (indicatorValue L R a b u)‖^2 ≤ ‖u‖^2 := by
  rw [toLp_norm_sq]
  have hi : Integrable (fun p => ‖indicatorValue L R a b u p‖^2) :=
    (memLp_two_iff_integrable_sq_norm (indicatorValue_memLp L R a b u).aestronglyMeasurable).mp
      (indicatorValue_memLp L R a b u)
  have hu : Integrable (fun p : Plane => ‖u p‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)
  calc
    _ ≤ ∫ p : Plane, ‖u p‖^2 := integral_mono hi hu (fun p => by
      by_cases hp : p ∈ rect L R a b
      · simp only [indicatorValue,indicator_of_mem hp,le_refl]
      · simp only [indicatorValue,indicator_of_notMem hp,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
        exact sq_nonneg _)
    _ = _ := (norm_sq_integral u).symm

def fixedSeed (L R a b : ℝ) (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    UpperHalfPlane → ℂ := upperSeed (indicatorValue L R a b u)

theorem fixedSeed_memLp (L R a b : ℝ) (ha : 0 < a)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    MemLp (fixedSeed L R a b u) 2 (volume : Measure UpperHalfPlane) := by
  apply upperSeed_memLp (indicatorValue_memLp L R a b u) ha
  intro p hp
  have hn : p ∉ rect L R a b := fun h => not_lt_of_ge h.2.1 hp
  simp only [indicatorValue,indicator_of_notMem hn]

theorem fixedSeed_support (L R a b : ℝ) (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    Function.support (fixedSeed L R a b u) ⊆ upperRectangle L R a b := by
  intro z hz
  by_contra hn
  exact hz (by simp only [fixedSeed,upperSeed,coordinateSeed,indicatorValue,indicator_of_notMem hn])

theorem fixedSeed_norm_sq_le (L R a b : ℝ) (ha : 0 < a)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    ‖(fixedSeed_memLp L R a b ha u).toLp (fixedSeed L R a b u)‖^2 ≤ (a⁻¹)^2 * ‖u‖^2 := by
  have hz : ∀ p : Plane, p.2 < a → indicatorValue L R a b u p = 0 := by
    intro p hp
    have hn : p ∉ rect L R a b := fun h => not_lt_of_ge h.2.1 hp
    simp only [indicatorValue,indicator_of_notMem hn]
  exact (upperSeed_norm_sq_le (indicatorValue_memLp L R a b u) ha hz).trans
    (mul_le_mul_of_nonneg_left (indicatorValue_norm_sq_le L R a b u) (sq_nonneg _))

theorem fixedSeed_sub_ae (L R a b : ℝ)
    (u v : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    fixedSeed L R a b (u-v) =ᵐ[(volume : Measure UpperHalfPlane)]
      fixedSeed L R a b u - fixedSeed L R a b v := by
  have he : indicatorValue L R a b (u-v) =ᵐ[(volume : Measure Plane)]
      indicatorValue L R a b u - indicatorValue L R a b v := by
    filter_upwards [Lp.coeFn_sub u v] with p hp
    by_cases hK : p ∈ rect L R a b
    · simp only [indicatorValue,indicator_of_mem hK,Pi.sub_apply,hp]
    · simp only [indicatorValue,indicator_of_notMem hK,Pi.sub_apply,sub_self]
  simpa only [fixedSeed,upperSeed,coordinateSeed,chartMap,
    Complex.measurableEquivRealProd_apply,Pi.sub_apply] using chartMap_quasiMeasurePreserving.ae_eq he

theorem fixedSeed_smul_ae (L R a b : ℝ) (c : ℂ)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    fixedSeed L R a b (c • u) =ᵐ[(volume : Measure UpperHalfPlane)] c • fixedSeed L R a b u := by
  have he : indicatorValue L R a b (c • u) =ᵐ[(volume : Measure Plane)] c • indicatorValue L R a b u := by
    filter_upwards [Lp.coeFn_smul c u] with p hp
    by_cases hK : p ∈ rect L R a b
    · simp only [indicatorValue,indicator_of_mem hK,Pi.smul_apply,hp]
    · simp only [indicatorValue,indicator_of_notMem hK,Pi.smul_apply,smul_zero]
  simpa only [fixedSeed,upperSeed,coordinateSeed,chartMap,
    Complex.measurableEquivRealProd_apply,Pi.smul_apply] using chartMap_quasiMeasurePreserving.ae_eq he

def quotientValue (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) : QuotientL2 N :=
  weakSeedL2 N (fixedSeed L R a b u) (fixedSeed_memLp L R a b ha u)
    (upperRectangle L R a b) (upperRectangle_isCompact L R a b ha) (fixedSeed_support L R a b u)

theorem quotientValue_sub (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a)
    (u v : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    quotientValue N L R a b ha (u-v) = quotientValue N L R a b ha u - quotientValue N L R a b ha v := by
  calc
    _ = weakSeedL2 N (fixedSeed L R a b u - fixedSeed L R a b v)
        ((fixedSeed_memLp L R a b ha u).sub (fixedSeed_memLp L R a b ha v))
        (upperRectangle L R a b) (upperRectangle_isCompact L R a b ha)
        (sub_support_subset (fixedSeed_support L R a b u) (fixedSeed_support L R a b v)) :=
      weakSeedL2_congr_ae N _ _ _ _ _ _ _ _ (fixedSeed_sub_ae L R a b u v)
    _ = _ := weakSeedL2_sub N _ _ _ _ _ _ _ _

theorem quotientValue_smul (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a)
    (c : ℂ) (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    quotientValue N L R a b ha (c • u) = c • quotientValue N L R a b ha u := by
  have hs : Function.support (c • fixedSeed L R a b u) ⊆ upperRectangle L R a b := by
    intro z hz
    apply fixedSeed_support L R a b u
    intro hzero
    exact hz (by simp only [Pi.smul_apply,hzero,smul_zero])
  calc
    _ = weakSeedL2 N (c • fixedSeed L R a b u) ((fixedSeed_memLp L R a b ha u).const_smul c)
        (upperRectangle L R a b) (upperRectangle_isCompact L R a b ha) hs :=
      weakSeedL2_congr_ae N _ _ _ _ _ _ _ _ (fixedSeed_smul_ae L R a b c u)
    _ = _ := weakSeedL2_smul N c _ _ _ _ _ hs

def fixedSeedTransferSq (N : ℕ) (L R a b : ℝ) : ℝ :=
  (compactOverlapBound N (upperRectangle L R a b) : ℝ) * (a⁻¹)^2

theorem fixedSeedTransferSq_nonneg (N : ℕ) (L R a b : ℝ) : 0 ≤ fixedSeedTransferSq N L R a b := by
  unfold fixedSeedTransferSq
  positivity

theorem quotientValue_norm_sq_le (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    ‖quotientValue N L R a b ha u‖^2 ≤ fixedSeedTransferSq N L R a b * ‖u‖^2 := by
  exact (weakSeedL2_norm_sq_le N _ _ _ _ _).trans (by
    simpa only [fixedSeedTransferSq,mul_assoc] using
      mul_le_mul_of_nonneg_left (fixedSeed_norm_sq_le L R a b ha u)
        (Nat.cast_nonneg (compactOverlapBound N (upperRectangle L R a b))))

theorem quotientValue_norm_le (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    ‖quotientValue N L R a b ha u‖ ≤ (fixedSeedTransferSq N L R a b+1)*‖u‖ := by
  let B := fixedSeedTransferSq N L R a b
  have hB : 0 ≤ B := fixedSeedTransferSq_nonneg _ _ _ _ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  calc
    _ ≤ B*‖u‖^2 := quotientValue_norm_sq_le N L R a b ha u
    _ ≤ (B+1)^2*‖u‖^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg B]) (sq_nonneg _)
    _ = _ := by ring

def fixedSeedLinear (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a) :
    ProductKernelL2TranslationAverage20261026a.PlaneL2 →ₗ[ℂ] QuotientL2 N where
  toFun := quotientValue N L R a b ha
  map_add' := by
    intro u v
    have h := quotientValue_sub N L R a b ha (u+v) v
    rw [add_sub_cancel_right] at h
    exact (eq_sub_iff_add_eq.mp h).symm
  map_smul' := quotientValue_smul N L R a b ha

/-- H1-independent bounded actual weak-seed periodization on a fixed
positive source rectangle. -/
def fixedSeedPeriodization (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a) :
    ProductKernelL2TranslationAverage20261026a.PlaneL2 →L[ℂ] QuotientL2 N :=
  (fixedSeedLinear N L R a b ha).mkContinuous (fixedSeedTransferSq N L R a b+1)
    (quotientValue_norm_le N L R a b ha)

theorem fixedSeedPeriodization_physical_ae (N : ℕ) [NeZero N] (L R a b : ℝ) (ha : 0 < a)
    (u : ProductKernelL2TranslationAverage20261026a.PlaneL2) :
    (fixedSeedPeriodization N L R a b ha u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (fixedSeed L R a b u) := weakSeedL2_ae N _ _ _ _ _

end
end ImbalancedChen.Part3.FixedRectangleWeakSeedL2Map20261026b
