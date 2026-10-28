import ImbalancedChen.P1OriginalFifthActualCrossingSections
import ImbalancedChen.P1OriginalFifthLiteralKernelModulus
import Mathlib

/-!
B13 for the actual selected/firstStop old-fifth owner union.
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT. The actual section/volume estimate
and the concrete variable-MI kernel modulus are consumed, rather than
assuming a desired integral comparison or an unrelated upper hypothesis.
-/
namespace ImbalancedChen.P1OriginalFifthActualB13IntegralError
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalCoarseFifthContinuation
open P1FifthUnitBoxGainDecomposition P1FifthUnitBoxLiteralGainLower
open P1LiteralVariableFifthCompactSupplier
open P1OriginalFifthMovingMeshFubiniBridge
open P1OriginalFifthLiteralKernelModulus
open P1OriginalFifthActualCrossingSections

abbrev Point := Fin 5 → ℝ

def positiveKernel (raw : FifthWireRow) (e : ℝ) (t : Point) : ℝ :=
  max 0 (literalRawKernel e raw t)

theorem positiveKernel_integrableOn_of_subset (raw : FifthWireRow) (e : ℝ)
    (S : Set Point) (hS : S ⊆ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ)) :
    IntegrableOn (positiveKernel raw e) S := by
  have hc : ContinuousOn (positiveKernel raw e)
      (positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ)) :=
    continuousOn_const.sup (continuousOn_literalRawKernel e (1 / 400) (19 / 96)
      (by norm_num) raw)
  exact (hc.integrableOn_compact
    (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc))).mono_set hS

theorem actual_ownerUnion_subset_positiveCube (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J : Finset (Label5 m)) :
    ownerUnion raw e chi m omega J ⊆ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ) := by
  intro t ht
  obtain ⟨j, _hj, htj⟩ := mem_iUnion₂.mp ht
  exact rawOwnerDomain_subset_positiveCube raw hgrid hpositive e chi m omega j htj

theorem rawBox_volume (raw : FifthWireRow) (hgrid : raw.grid = 400) :
    volume raw.originalBox = ENNReal.ofReal (1 / (400 : ℝ)^5) := by
  have heq : raw.originalBox = univ.pi
      (fun i : Fin 5 => Ico (raw.lower i : ℝ) (raw.upper i : ℝ)) := by
    ext t
    simp [FifthWireRow.originalBox]
  have hw (i : Fin 5) : (raw.upper i : ℝ) - (raw.lower i : ℝ) = 1 / 400 := by
    simp only [FifthWireRow.upper, FifthWireRow.lower, hgrid]
    push_cast
    ring
  rw [heq, volume_pi_pi]
  simp_rw [Real.volume_Ico, hw]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 400)]
  congr 1
  ring

/-- Nonnegative bounded kernels pay one symmetric-difference volume.
The two directed lost pieces are each nonnegative, so no unnecessary
factor two is introduced by bounding their signed difference. -/
private theorem nonnegative_setIntegral_domain_difference
    (S T : Set Point) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (f : Point → ℝ) (hfS : IntegrableOn f S) (hfT : IntegrableOn f T)
    (M : ℝ) (hM : 0 ≤ M)
    (hpos : ∀ t ∈ S ∪ T, 0 ≤ f t) (hbound : ∀ t ∈ S ∪ T, f t ≤ M)
    (hfinite : volume ((S \ T) ∪ (T \ S)) < ∞) :
    |(∫ t in S, f t) - ∫ t in T, f t| ≤
      M * (volume ((S \ T) ∪ (T \ S))).toReal := by
  let A := S \ T
  let B := T \ S
  let C := S ∩ T
  let U := (S \ T) ∪ (T \ S)
  have hA : MeasurableSet A := hS.diff hT
  have hB : MeasurableSet B := hT.diff hS
  have hC : MeasurableSet C := hS.inter hT
  have hAraw : A ⊆ S ∪ T := fun _ h => Or.inl h.1
  have hBraw : B ⊆ S ∪ T := fun _ h => Or.inr h.1
  have hAU : A ⊆ U := subset_union_left
  have hBU : B ⊆ U := subset_union_right
  have hAf : volume A < ∞ := (measure_mono hAU).trans_lt hfinite
  have hBf : volume B < ∞ := (measure_mono hBU).trans_lt hfinite
  have hAr : (volume A).toReal ≤ (volume U).toReal :=
    ENNReal.toReal_mono hfinite.ne (measure_mono hAU)
  have hBr : (volume B).toReal ≤ (volume U).toReal :=
    ENNReal.toReal_mono hfinite.ne (measure_mono hBU)
  have hAi : 0 ≤ ∫ t in A, f t := setIntegral_nonneg hA (fun t ht => hpos t (hAraw ht))
  have hBi : 0 ≤ ∫ t in B, f t := setIntegral_nonneg hB (fun t ht => hpos t (hBraw ht))
  have hAn := norm_setIntegral_le_of_norm_le_const hAf (fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos t (hAraw ht))]
    exact hbound t (hAraw ht))
  have hBn := norm_setIntegral_le_of_norm_le_const hBf (fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos t (hBraw ht))]
    exact hbound t (hBraw ht))
  rw [Real.norm_eq_abs, abs_of_nonneg hAi] at hAn
  rw [Real.norm_eq_abs, abs_of_nonneg hBi] at hBn
  have hAupper : (∫ t in A, f t) ≤ M * (volume U).toReal :=
    hAn.trans (mul_le_mul_of_nonneg_left hAr hM)
  have hBupper : (∫ t in B, f t) ≤ M * (volume U).toReal :=
    hBn.trans (mul_le_mul_of_nonneg_left hBr hM)
  have hSA : S \ C = A := by
    ext t
    simp only [A, C, mem_diff, mem_inter_iff]
    tauto
  have hTB : T \ C = B := by
    ext t
    simp only [B, C, mem_diff, mem_inter_iff]
    tauto
  have hSI := setIntegral_sdiff hC hfS (show C ⊆ S from inter_subset_left)
  have hTI := setIntegral_sdiff hC hfT (show C ⊆ T from inter_subset_right)
  rw [hSA] at hSI
  rw [hTB] at hTI
  apply abs_le.mpr
  constructor <;> linarith

/-- Concrete kernel motion on any actual subset of the positive cube.
Both integrability and the modulus bound are proved, not hypotheses. -/
theorem positiveKernel_integral_motion_le (raw : FifthWireRow) (e : ℝ)
    (S : Set Point) (hS : S ⊆ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ))
    (hfinite : volume S < ∞) :
    |(∫ t in S, positiveKernel raw e t) - ∫ t in S, positiveKernel raw 0 t| ≤
      rowModulus raw e * (volume S).toReal := by
  have hi := positiveKernel_integrableOn_of_subset raw e S hS
  have hi0 := positiveKernel_integrableOn_of_subset raw 0 S hS
  rw [← integral_sub hi hi0]
  have hn := norm_setIntegral_le_of_norm_le_const hfinite (fun t ht => by
    rw [Real.norm_eq_abs]
    exact positive_kernel_difference_le_rowModulus raw e t (hS ht))
  simpa only [Real.norm_eq_abs] using hn

/-- Actual B13 with the literal variable-MI kernel and the original
selected/firstStop carrier. The right side uses the second batch's
concrete modulus and mass bound, and the geometric section theorem above.
There is no per-child cardinality multiplier and no assumed row error. -/
theorem actual_selected_owner_B13 (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400)
    (hpositive : ∀ i, 1 ≤ raw.lo i) (hkey : raw.lo 0 ≤ 77)
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200) (chi0 chi omega0 omega : ℝ)
    (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (J : Finset (Label5 (refinedMesh q)))
    (hselected0 : ∀ j ∈ J, j ∈ selectedFifthCells 0 chi0 (refinedMesh q) omega0 J)
    (hselected : ∀ j ∈ J, j ∈ selectedFifthCells e chi (refinedMesh q) omega J)
    (hstop0 : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true)
    (hstop : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) (refinedMesh q) j = true) :
    |(∫ t in ownerUnion raw e chi (refinedMesh q) omega J, positiveKernel raw e t) -
        ∫ t in ownerUnion raw 0 chi0 (refinedMesh q) omega0 J, positiveKernel raw 0 t| ≤
      rowModulus raw e / (400 : ℝ)^5 +
        rowMassBound raw * (428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4 := by
  let S := ownerUnion raw e chi (refinedMesh q) omega J
  let T := ownerUnion raw 0 chi0 (refinedMesh q) omega0 J
  let U := (S \ T) ∪ (T \ S)
  have hS : MeasurableSet S := ownerUnion_measurable raw e chi _ omega J
  have hT : MeasurableSet T := ownerUnion_measurable raw 0 chi0 _ omega0 J
  have hSK := actual_ownerUnion_subset_positiveCube raw hgrid hpositive e chi _ omega J
  have hTK := actual_ownerUnion_subset_positiveCube raw hgrid hpositive 0 chi0 _ omega0 J
  have hSraw : S ⊆ raw.originalBox := ownerUnion_subset_raw raw e chi _ omega J
  have hSvol : volume S ≤ ENNReal.ofReal (1 / (400 : ℝ)^5) :=
    (measure_mono hSraw).trans_eq (rawBox_volume raw hgrid)
  have hSfinite : volume S < ∞ := hSvol.trans_lt ENNReal.ofReal_lt_top
  have hSreal : (volume S).toReal ≤ 1 / (400 : ℝ)^5 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSvol
    simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (400 : ℝ)^5)] using hh
  have hUeq : U = ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J := by
    dsimp only [U, S, T, ownerSymmDiff]
    exact union_comm _ _
  have hUvol : volume U ≤ ENNReal.ofReal ((428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4) := by
    rw [hUeq]
    exact actual_ownerSymmDiff_volume_le raw q hq hgrid hkey e he hemax
      chi0 chi omega0 omega hchi hstep J hselected0 hselected hstop0 hstop
  have hUfinite : volume U < ∞ := hUvol.trans_lt ENNReal.ofReal_lt_top
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hUreal : (volume U).toReal ≤ (428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUvol
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ (428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4)] using hh
  have hM : 0 ≤ rowMassBound raw := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_rowMassBound raw)
  have hmod := rowModulus_nonneg raw (e : ℝ)
  have hmotion := positiveKernel_integral_motion_le raw (e : ℝ) S hSK hSfinite
  have hdomain : |(∫ t in S, positiveKernel raw 0 t) - ∫ t in T, positiveKernel raw 0 t| ≤
      rowMassBound raw * (volume U).toReal :=
    nonnegative_setIntegral_domain_difference S T hS hT (positiveKernel raw 0)
      (positiveKernel_integrableOn_of_subset raw 0 S hSK)
      (positiveKernel_integrableOn_of_subset raw 0 T hTK) (rowMassBound raw) hM
      (fun _ _ => le_max_left _ _) (by
        intro t ht
        have htK : t ∈ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ) := ht.elim hSK hTK
        exact positive_kernel_le_rowMassBound raw 0 (by norm_num) t htK) hUfinite
  calc
    |(∫ t in S, positiveKernel raw e t) - ∫ t in T, positiveKernel raw 0 t| ≤
        |(∫ t in S, positiveKernel raw e t) - ∫ t in S, positiveKernel raw 0 t| +
          |(∫ t in S, positiveKernel raw 0 t) - ∫ t in T, positiveKernel raw 0 t| :=
      abs_sub_le _ _ _
    _ ≤ rowModulus raw e * (volume S).toReal + rowMassBound raw * (volume U).toReal :=
      add_le_add hmotion hdomain
    _ ≤ rowModulus raw e * (1 / (400 : ℝ)^5) +
        rowMassBound raw * ((428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4) :=
      add_le_add (mul_le_mul_of_nonneg_left hSreal hmod)
        (mul_le_mul_of_nonneg_left hUreal hM)
    _ = rowModulus raw e / (400 : ℝ)^5 +
        rowMassBound raw * (428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4 := by ring

end
end ImbalancedChen.P1OriginalFifthActualB13IntegralError
