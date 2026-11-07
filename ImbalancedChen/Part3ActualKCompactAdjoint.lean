import ImbalancedChen.Part3ActualKCompactL2Operator
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The Hilbert adjoint of the actual compact K/q integral operator has the
conjugate physical kernel on continuous height inputs.  Compactness,
joint kernel continuity and the two genuine restricted Lebesgue measures
justify Fubini.  The composite A†A is the positive compact-height
quadratic-form operator, without a Plancherel or automorphic assertion.
-/

namespace ImbalancedChen.Part3.ActualKCompactAdjointSourceOnly

noncomputable section

open Set MeasureTheory
open scoped InnerProduct ComplexConjugate
open P3ActualLiteralPacketIntegralSourceOnly
open ImbalancedChen.Part3.ImaginaryOrderKExplicitMajorantSourceOnly
  (restrictedKKernel)
open ImbalancedChen.Part3.ActualKRestrictedKernelContinuity20261024z
  (restrictedKKernel_joint_continuous)
open ImbalancedChen.Part3.ActualKRegionOperatorSourceOnly
  (regionVolume regionVolume_univ)
open ImbalancedChen.Part3.ActualKCompactHeightOperatorSourceOnly
  (kCompactHeightOperator)
open ImbalancedChen.Part3.ActualKCompactL2OperatorSourceOnly
  (heightVolume heightVolume_univ regionToL2 heightToL2
   regionToL2_denseRange kCompactL2Operator
   kCompactL2Operator_regionToL2)

variable {ι : Type*}

private instance regionVolume_finiteAdjoint (P : PacketData ι) :
    IsFiniteMeasure (regionVolume P) :=
  ⟨by rw [regionVolume_univ]; exact isCompact_Icc.measure_lt_top⟩

private instance heightVolume_finiteAdjoint (T : ℝ) :
    IsFiniteMeasure (heightVolume T) :=
  ⟨by rw [heightVolume_univ]; exact isCompact_Icc.measure_lt_top⟩

/-- Joint continuity of the actual physical kernel after reversing the
order of the compact q and t coordinates. -/
private theorem restrictedKKernel_flip_continuous
    (P : PacketData ι) (T : ℝ) :
    Continuous (fun p : P.region × Icc (-T) T =>
      restrictedKKernel P (p.2 : ℝ) p.1) := by
  have ht : Continuous (fun p : P.region × Icc (-T) T => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hq : Continuous (fun p : P.region × Icc (-T) T => p.1) :=
    continuous_fst
  exact (restrictedKKernel_joint_continuous P).comp (ht.prodMk hq)

/-- The actual conjugate-kernel integral is a continuous function of the
physical q variable for each continuous compact-height input. -/
def adjointHeightKernel (P : PacketData ι) (T : ℝ)
    (F : C(Icc (-T) T, ℂ)) : C(P.region, ℂ) := by
  have hjoint : Continuous (fun p : P.region × Icc (-T) T =>
      star (restrictedKKernel P (p.2 : ℝ) p.1) * F p.2) :=
    (restrictedKKernel_flip_continuous P T).star.mul
      (F.continuous.comp continuous_snd)
  have hparam : Continuous (fun q : P.region =>
      ∫ s in (Set.univ : Set (Icc (-T) T)),
        star (restrictedKKernel P (s : ℝ) q) * F s ∂heightVolume T) :=
    continuous_parametric_integral_of_continuous
      (f := fun q (s : Icc (-T) T) =>
        star (restrictedKKernel P (s : ℝ) q) * F s)
      hjoint isCompact_univ
  refine ⟨fun q => ∫ s : Icc (-T) T,
      star (restrictedKKernel P (s : ℝ) q) * F s ∂heightVolume T, ?_⟩
  simpa only [setIntegral_univ] using hparam

@[simp]
theorem adjointHeightKernel_apply (P : PacketData ι) (T : ℝ)
    (F : C(Icc (-T) T, ℂ)) (q : P.region) :
    adjointHeightKernel P T F q =
      ∫ s : Icc (-T) T,
        star (restrictedKKernel P (s : ℝ) q) * F s ∂heightVolume T := by
  rfl

/-- Conjugating the q-side integral gives the exact orientation needed
for the L2 inner-product calculation. -/
private theorem conj_adjointHeightKernel_apply
    (P : PacketData ι) (T : ℝ) (F : C(Icc (-T) T, ℂ))
    (q : P.region) :
    conj (adjointHeightKernel P T F q) =
      ∫ s : Icc (-T) T,
        restrictedKKernel P (s : ℝ) q * conj (F s) ∂heightVolume T := by
  rw [adjointHeightKernel_apply]
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    simp [Complex.star_def])

/-- Continuity on the compact product makes the literal physical
q-height triple product integrable. -/
private theorem jointKernelProduct_integrable (P : PacketData ι)
    (T : ℝ) (f : C(P.region, ℂ)) (F : C(Icc (-T) T, ℂ)) :
    Integrable (fun p : P.region × Icc (-T) T =>
      f p.1 * restrictedKKernel P (p.2 : ℝ) p.1 * star (F p.2))
      ((regionVolume P).prod (heightVolume T)) := by
  have hjoint : Continuous (fun p : P.region × Icc (-T) T =>
      f p.1 * restrictedKKernel P (p.2 : ℝ) p.1 * star (F p.2)) :=
    ((f.continuous.comp continuous_fst).mul
      (restrictedKKernel_flip_continuous P T)).mul
        ((F.continuous.comp continuous_snd).star)
  exact hjoint.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Fubini for the actual kernel and the two transported Lebesgue
measures, retaining every q and t normalization. -/
private theorem adjointHeightKernel_fubini (P : PacketData ι)
    (T : ℝ) (f : C(P.region, ℂ)) (F : C(Icc (-T) T, ℂ)) :
    (∫ q : P.region, f q * conj (adjointHeightKernel P T F q)
        ∂regionVolume P) =
      ∫ s : Icc (-T) T,
        (kCompactHeightOperator P T f) s * conj (F s)
          ∂heightVolume T := by
  have hleft (q : P.region) :
      f q * (∫ s : Icc (-T) T,
          restrictedKKernel P (s : ℝ) q * conj (F s) ∂heightVolume T) =
        ∫ s : Icc (-T) T,
          f q * restrictedKKernel P (s : ℝ) q * conj (F s)
            ∂heightVolume T := by
    calc
      _ = ∫ s : Icc (-T) T,
          f q * (restrictedKKernel P (s : ℝ) q * conj (F s))
            ∂heightVolume T :=
        (integral_const_mul (f q) _).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by ring)
  have hright (s : Icc (-T) T) :
      (∫ q : P.region,
          f q * restrictedKKernel P (s : ℝ) q ∂regionVolume P) *
          star (F s) =
        ∫ q : P.region,
          f q * restrictedKKernel P (s : ℝ) q * star (F s)
            ∂regionVolume P := by
    exact (integral_mul_const (star (F s))
      (fun q : P.region => f q * restrictedKKernel P (s : ℝ) q)).symm
  calc
    (∫ q : P.region, f q * conj (adjointHeightKernel P T F q)
        ∂regionVolume P) =
      ∫ q : P.region,
        f q * (∫ s : Icc (-T) T,
          restrictedKKernel P (s : ℝ) q * conj (F s)
            ∂heightVolume T) ∂regionVolume P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun q => by
          rw [conj_adjointHeightKernel_apply])
    _ = ∫ q : P.region, ∫ s : Icc (-T) T,
          f q * restrictedKKernel P (s : ℝ) q * star (F s)
            ∂heightVolume T ∂regionVolume P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun q => by
          simpa only [Complex.star_def] using hleft q)
    _ = ∫ s : Icc (-T) T, ∫ q : P.region,
          f q * restrictedKKernel P (s : ℝ) q * star (F s)
            ∂regionVolume P ∂heightVolume T :=
      integral_integral_swap (jointKernelProduct_integrable P T f F)
    _ = ∫ s : Icc (-T) T,
          (∫ q : P.region,
            f q * restrictedKKernel P (s : ℝ) q ∂regionVolume P) *
            star (F s) ∂heightVolume T := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => (hright s).symm)
    _ = ∫ s : Icc (-T) T,
          (kCompactHeightOperator P T f) s * conj (F s)
            ∂heightVolume T := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by
          change (∫ q : P.region,
            f q * restrictedKKernel P (s : ℝ) q ∂regionVolume P) *
              star (F s) =
            (∫ q : P.region,
              f q * restrictedKKernel P (s : ℝ) q ∂regionVolume P) *
                conj (F s)
          simp only [Complex.star_def])

/-- The compact-height adjoint is exactly the conjugate-kernel integral
on every continuous height input, represented in physical L2(q). -/
theorem kCompactL2Operator_adjoint_heightToL2
    (P : PacketData ι) (T : ℝ) (F : C(Icc (-T) T, ℂ)) :
    (kCompactL2Operator P T)† (heightToL2 T F) =
      regionToL2 P (adjointHeightKernel P T F) := by
  apply ext_inner_right ℂ
  intro x
  have hleft : Continuous (fun y : Lp ℂ 2 (regionVolume P) =>
      inner ℂ ((kCompactL2Operator P T)† (heightToL2 T F)) y) :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun y : Lp ℂ 2 (regionVolume P) =>
      inner ℂ (regionToL2 P (adjointHeightKernel P T F)) y) :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)
  refine (regionToL2_denseRange P).induction_on x
    (isClosed_eq hleft hright) ?_
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [kCompactL2Operator_regionToL2]
  change inner ℂ (heightToL2 T F)
      (heightToL2 T (kCompactHeightOperator P T f)) =
    inner ℂ (regionToL2 P (adjointHeightKernel P T F))
      (regionToL2 P f)
  unfold regionToL2 heightToL2
  rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
  exact (adjointHeightKernel_fubini P T f F).symm

/-- The adjoint costs no more operator norm than the already established
physical K/q L2 bound. -/
theorem kCompactL2Operator_adjoint_norm_le (P : PacketData ι) (T : ℝ) :
    ‖(kCompactL2Operator P T)†‖ ≤
      ((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
          Real.sqrt ((volume : Measure ℝ).real (Icc (-T) T)) := by
  have hnorm : ‖(kCompactL2Operator P T)†‖ =
      ‖kCompactL2Operator P T‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _
  rw [hnorm]
  exact ImbalancedChen.Part3.ActualKCompactL2OperatorSourceOnly.kCompactL2Operator_norm_le P T

/-- The actual compact-height K quadratic-form operator on physical L2(q). -/
def kCompactQuadraticOperator (P : PacketData ι) (T : ℝ) :
    Lp ℂ 2 (regionVolume P) →L[ℂ] Lp ℂ 2 (regionVolume P) :=
  (kCompactL2Operator P T)† ∘L kCompactL2Operator P T

/-- On continuous q inputs the positive composite is the literal
conjugate-height-kernel integral of the original K integral. -/
theorem kCompactQuadraticOperator_regionToL2 (P : PacketData ι)
    (T : ℝ) (f : C(P.region, ℂ)) :
    kCompactQuadraticOperator P T (regionToL2 P f) =
      regionToL2 P
        (adjointHeightKernel P T (kCompactHeightOperator P T f)) := by
  change (kCompactL2Operator P T)†
    (kCompactL2Operator P T (regionToL2 P f)) = _
  rw [kCompactL2Operator_regionToL2]
  exact kCompactL2Operator_adjoint_heightToL2 P T
    (kCompactHeightOperator P T f)

theorem kCompactQuadraticOperator_isPositive (P : PacketData ι) (T : ℝ) :
    (kCompactQuadraticOperator P T).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (kCompactL2Operator P T)

theorem kCompactQuadraticOperator_isSelfAdjoint (P : PacketData ι) (T : ℝ) :
    (kCompactQuadraticOperator P T).IsSelfAdjoint :=
  (kCompactQuadraticOperator_isPositive P T).isSelfAdjoint

/-- Its quadratic form is literally the L2 norm square of the physical
compact-height K transform. -/
theorem kCompactQuadraticOperator_inner (P : PacketData ι) (T : ℝ)
    (f : Lp ℂ 2 (regionVolume P)) :
    inner ℂ f (kCompactQuadraticOperator P T f) =
      (‖kCompactL2Operator P T f‖ : ℂ) ^ 2 := by
  change inner ℂ f
    ((kCompactL2Operator P T)† (kCompactL2Operator P T f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

/-- The quadratic form's value on a continuous q input is the true
compact-height K integral's L2 norm square. -/
theorem kCompactQuadraticOperator_continuous_inner
    (P : PacketData ι) (T : ℝ) (f : C(P.region, ℂ)) :
    inner ℂ (regionToL2 P f)
      (kCompactQuadraticOperator P T (regionToL2 P f)) =
        (‖heightToL2 T (kCompactHeightOperator P T f)‖ : ℂ) ^ 2 := by
  rw [kCompactQuadraticOperator_inner, kCompactL2Operator_regionToL2]

theorem kCompactQuadraticOperator_re_inner_nonneg
    (P : PacketData ι) (T : ℝ) (f : Lp ℂ 2 (regionVolume P)) :
    0 ≤ (inner ℂ f (kCompactQuadraticOperator P T f)).re := by
  exact (kCompactQuadraticOperator_isPositive P T).re_inner_nonneg_right f

end
end ImbalancedChen.Part3.ActualKCompactAdjointSourceOnly
