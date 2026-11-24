import ImbalancedChen.P1FifthUnitBoxLiteralGainLower
import Mathlib

/-!
Concrete compact-kernel inputs for the moving grid400 mesh schedule.
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.

The kernel is exactly max(0,literalRawKernel(e,raw,t)): the saved mask keeps
its variable M_I(t), and the old profile is the variable rawFourth(t)-2e.
Neither old profile nor mask is replaced by a constant. This is the literal
conservative raw-row kernel, not an identity with an arbitrary actual old4.
-/
namespace ImbalancedChen.P1OriginalFifthLiteralKernelModulus

noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower
open P1LiteralVariableFifthCompactSupplier

abbrev Point := Fin 5 → ℝ

/-- The SAME positive compact cube containing every positive-key grid400
raw-owner domain. Both the five reciprocal weights and the residual
last-coordinate denominator stay away from zero here. -/
abbrev CompactPoint := positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ)

instance compactSpaceCompactPoint : CompactSpace CompactPoint :=
  isCompact_iff_compactSpace.mp
    (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc))

abbrev BufferPoint := Icc (0 : ℝ) (3 / 51200 : ℝ)

instance compactSpaceBufferPoint : CompactSpace BufferPoint :=
  isCompact_iff_compactSpace.mp isCompact_Icc

theorem compactPoint_coordinate_pos (t : CompactPoint) (i : Fin 5) :
    0 < (t : Point) i :=
  (by norm_num : (0 : ℝ) < 1 / 400).trans_le (t.property i (mem_univ _)).1

private theorem coordinate_continuous (i : Fin 5) :
    Continuous (fun p : ℝ × CompactPoint => (p.2 : Point) i) :=
  (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)

private theorem tuple_continuous :
    Continuous (fun p : ℝ × CompactPoint => (p.2 : Point)) :=
  continuous_subtype_val.comp continuous_snd

private theorem sum_continuous :
    Continuous (fun p : ℝ × CompactPoint => ∑ i, (p.2 : Point) i) :=
  continuous_finsetSum _ (fun i _ => coordinate_continuous i)

/-- Joint continuity includes the moving strict own-cube boundary. The
canonical zero-extended lower factor agrees with that gated profile at
ALL positive tuples, including the equality face. -/
theorem moving_profile_joint_continuous
    (level : ℝ × CompactPoint → ℝ) (hlevel : Continuous level) :
    Continuous (fun p : ℝ × CompactPoint =>
      primeOwnCubeGatedProfile (level p) (p.2 : Point)) := by
  have hlast := coordinate_continuous (Fin.last 4)
  have hnonzero : ∀ p : ℝ × CompactPoint, (p.2 : Point) (Fin.last 4) ≠ 0 :=
    fun p => (compactPoint_coordinate_pos p.2 (Fin.last 4)).ne'
  have harg : Continuous (fun p : ℝ × CompactPoint =>
      (level p - ∑ i, (p.2 : Point) i) / (p.2 : Point) (Fin.last 4)) :=
    (hlevel.sub sum_continuous).div hlast hnonzero
  have hc : Continuous (fun p : ℝ × CompactPoint =>
      4 * actualExtendedThirdLowerFactor
        ((level p - ∑ i, (p.2 : Point) i) / (p.2 : Point) (Fin.last 4)) /
          (p.2 : Point) (Fin.last 4)) :=
    (continuous_const.mul (continuous_actualExtendedThirdLowerFactor.comp harg)).div
      hlast hnonzero
  have heq : (fun p : ℝ × CompactPoint =>
        primeOwnCubeGatedProfile (level p) (p.2 : Point)) =
      (fun p : ℝ × CompactPoint =>
        4 * actualExtendedThirdLowerFactor
          ((level p - ∑ i, (p.2 : Point) i) / (p.2 : Point) (Fin.last 4)) /
            (p.2 : Point) (Fin.last 4)) := by
    funext p
    rw [p1PrimeOwnCubeGatedProfile_eq_profile _ _
      (compactPoint_coordinate_pos p.2 (Fin.last 4)),
      p1PrimeTupleMinusProfile_eq_lowerFactor _ _
        (compactPoint_coordinate_pos p.2 (Fin.last 4))]
  rw [heq]
  exact hc

/-- The raw variable-MI candidate varies jointly with e and all five
physical coordinates. In particular the saved raw mask is unchanged. -/
theorem rawCandidate_joint_continuous (raw : FifthWireRow) :
    Continuous (fun p : ℝ × CompactPoint => rawCandidate p.1 raw (p.2 : Point)) := by
  have hsum : Continuous (fun p : ℝ × CompactPoint =>
      ∑ i ∈ maskSlots 5 raw.mask.toNat, (p.2 : Point) i) :=
    continuous_finsetSum _ (fun i _ => coordinate_continuous i)
  change Continuous (fun p : ℝ × CompactPoint =>
    VariableEnvelope.v (∑ i ∈ maskSlots 5 raw.mask.toNat, (p.2 : Point) i) - 2 * p.1)
  exact (VariableEnvelope.continuous_v.comp hsum).sub
    (continuous_const.mul continuous_fst)

/-- The old raw-fourth fifteen-tent plus W envelope remains a function
of the same physical tuple; only its common buffer shifts with e. -/
theorem old5_joint_continuous :
    Continuous (fun p : ℝ × CompactPoint => old5 p.1 (p.2 : Point)) := by
  change Continuous (fun p : ℝ × CompactPoint => rawFourth (p.2 : Point) - 2 * p.1)
  exact (continuous_rawFourth.comp tuple_continuous).sub
    (continuous_const.mul continuous_fst)

/-- Actual joint continuity of the literal signed raw-row kernel. This
is stronger than separate continuity with a fixed e and is what permits
the compact-open/sup-norm argument below. -/
theorem literalRawKernel_joint_continuous (raw : FifthWireRow) :
    Continuous (fun p : ℝ × CompactPoint => literalRawKernel p.1 raw (p.2 : Point)) := by
  have hnew := moving_profile_joint_continuous _ (rawCandidate_joint_continuous raw)
  have hold := moving_profile_joint_continuous _ old5_joint_continuous
  have hprod : Continuous (fun p : ℝ × CompactPoint => ∏ i, 1 / (p.2 : Point) i) :=
    continuous_finsetProd _ (fun i _ =>
      continuous_const.div (coordinate_continuous i)
        (fun p => (compactPoint_coordinate_pos p.2 i).ne'))
  exact (hnew.sub hold).mul hprod

/-- The exact nonnegative kernel used in the predecessor's B13 estimate. -/
def positiveRowMap (raw : FifthWireRow) (e : ℝ) : C(CompactPoint, ℝ) :=
  ⟨fun t => max 0 (literalRawKernel e raw (t : Point)),
    continuous_const.sup ((literalRawKernel_joint_continuous raw).comp
      (continuous_const.prodMk continuous_id))⟩

theorem positiveRowMap_apply (raw : FifthWireRow) (e : ℝ) (t : CompactPoint) :
    positiveRowMap raw e t = max 0 (literalRawKernel e raw (t : Point)) := rfl

/-- Continuity in the genuine uniform norm on the positive compact cube,
not merely pointwise continuity at a chosen tuple. -/
theorem positiveRowMap_continuous (raw : FifthWireRow) :
    Continuous (positiveRowMap raw : ℝ → C(CompactPoint, ℝ)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × CompactPoint =>
    max 0 (literalRawKernel p.1 raw (p.2 : Point)))
  exact continuous_const.sup (literalRawKernel_joint_continuous raw)

/-- A concrete finite continuous modulus. Unlike a desired integral
bound, this is defined directly from the actual continuous kernel. -/
def rowModulus (raw : FifthWireRow) (e : ℝ) : ℝ :=
  ‖positiveRowMap raw e - positiveRowMap raw 0‖

theorem rowModulus_continuous (raw : FifthWireRow) : Continuous (rowModulus raw) :=
  ((positiveRowMap_continuous raw).sub continuous_const).norm

theorem rowModulus_zero (raw : FifthWireRow) : rowModulus raw 0 = 0 := by
  simp only [rowModulus, sub_self, norm_zero]

theorem rowModulus_nonneg (raw : FifthWireRow) (e : ℝ) : 0 ≤ rowModulus raw e :=
  norm_nonneg _

/-- Pointwise domination on the precise compact range used by B13. -/
theorem positive_kernel_difference_le_rowModulus (raw : FifthWireRow) (e : ℝ)
    (t : Point) (ht : t ∈ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ)) :
    |max 0 (literalRawKernel e raw t) - max 0 (literalRawKernel 0 raw t)| ≤
      rowModulus raw e := by
  have h := (positiveRowMap raw e - positiveRowMap raw 0).norm_coe_le_norm
    (⟨t, ht⟩ : CompactPoint)
  simpa only [ContinuousMap.sub_apply, positiveRowMap_apply, Real.norm_eq_abs,
    rowModulus] using h

/-- The physical buffer interval is itself compact, so the moving
continuous functions form one bounded family in the actual sup norm. -/
def bufferFamily (raw : FifthWireRow) : C(BufferPoint, C(CompactPoint, ℝ)) :=
  ⟨fun e => positiveRowMap raw (e : ℝ),
    (positiveRowMap_continuous raw).comp continuous_subtype_val⟩

def rowMassBound (raw : FifthWireRow) : ℝ := max 1 ‖bufferFamily raw‖

theorem one_le_rowMassBound (raw : FifthWireRow) : 1 ≤ rowMassBound raw := le_max_left _ _

theorem positive_kernel_le_rowMassBound (raw : FifthWireRow) (e : ℝ)
    (he : e ∈ Icc (0 : ℝ) (3 / 51200 : ℝ)) (t : Point)
    (ht : t ∈ positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ)) :
    max 0 (literalRawKernel e raw t) ≤ rowMassBound raw := by
  have hpoint := (positiveRowMap raw e).norm_coe_le_norm (⟨t, ht⟩ : CompactPoint)
  have hpoint' : |max 0 (literalRawKernel e raw t)| ≤ ‖positiveRowMap raw e‖ := by
    simpa only [positiveRowMap_apply, Real.norm_eq_abs] using hpoint
  rw [abs_of_nonneg (le_max_left 0 _)] at hpoint'
  have hfamily := (bufferFamily raw).norm_coe_le_norm (⟨e, he⟩ : BufferPoint)
  have hfamily' : ‖positiveRowMap raw e‖ ≤ ‖bufferFamily raw‖ := hfamily
  exact hpoint'.trans (hfamily'.trans (le_max_right _ _))

/-- The domain/range binding is proved from the actual raw-owner subset,
not supplied as a hypothetical compactness of the integral domain. -/
theorem actual_rawOwner_kernel_controls (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (he : (e : ℝ) ∈ Icc (0 : ℝ) (3 / 51200 : ℝ))
    (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Fin 5 → Fin (m + 1))
    (t : Point) (ht : t ∈ rawOwnerDomain raw e chi m omega j) :
    |max 0 (literalRawKernel (e : ℝ) raw t) - max 0 (literalRawKernel 0 raw t)| ≤
        rowModulus raw e ∧
      max 0 (literalRawKernel (e : ℝ) raw t) ≤ rowMassBound raw := by
  have htCompact := rawOwnerDomain_subset_positiveCube raw hgrid hpositive e chi m omega j ht
  exact ⟨positive_kernel_difference_le_rowModulus raw e t htCompact,
    positive_kernel_le_rowMassBound raw e he t htCompact⟩

/-- These are precisely hmodulus/hzero (plus actual positive mass bounds)
for the previous joint-buffer/mesh theorem, now supplied for every finite
raw bank without any kernel-regularity hypothesis. -/
theorem finite_bank_modulus_inputs (records : Finset FifthWireRow) :
    (∀ raw ∈ records, ContinuousAt (rowModulus raw) 0) ∧
      (∀ raw ∈ records, rowModulus raw 0 = 0) ∧
      (∀ raw ∈ records, 1 ≤ rowMassBound raw) :=
  ⟨fun raw _ => (rowModulus_continuous raw).continuousAt,
    fun raw _ => rowModulus_zero raw, fun raw _ => one_le_rowMassBound raw⟩

end
end ImbalancedChen.P1OriginalFifthLiteralKernelModulus
