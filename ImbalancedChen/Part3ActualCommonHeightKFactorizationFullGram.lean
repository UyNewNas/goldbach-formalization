import ImbalancedChen.Part3ActualKPacketAdapter
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Star.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit. 2026-10-24.
No Lean, lake, compiler, helper, numerical calculation or Git command was run.
ROOT owns the compilation queue. This file changes no actual source.

This supplies one concrete prerequisite for the common-height K branch:
the integral of the ACTUAL finite packet factors into the ACTUAL test's
K_{2it}(q)dq/q transform and its frozen completed/coefficient sum.
The transform has no coefficient or phase depending on spectral height.

The second form of the same finite-to-integral prerequisite is a compact
raw-height Gram identity for the actual K-mode row at any positive physical
q. Every original (j,m,n) label and every off-diagonal pair is retained.
Integrability is derived from the already proved joint continuity of the
specific K integral. Positivity is the integral of its actual norm square.

The height integration below is explicitly unweighted Lebesgue dt on
[-T,T]. It is NOT identified with the continuous Kuznetsov measure and is
NOT called Plancherel. No cusp Fourier coefficient, Kuznetsov identity,
regular/exceptional large sieve, 7/32 estimate or desired return is assumed.
Those analytic suppliers remain open. See the companion CP for exact pins.
-/

namespace ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly

variable {ι : Type*}

/-- ONE common spectral height; it is not selected separately by row. -/
def commonHeight (t : ℝ) : ι → ℕ → ℕ → ℝ := fun _ _ _ => t

/-- The literal frozen m interval/phase and coprime signed coefficient. -/
def completedPacketSum (P : PacketData ι) (k : D4 → ℤ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    (P.completed k).weight m *
      signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n

/-- The actual integral realization, retaining dq/q and the physical scale Y0. -/
def kTestTransform (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℂ :=
  ∫ q : ℝ, spectralTest k P.Y0 q *
    ((imaginaryOrderK t q : ℂ)/(q : ℂ))

theorem kTestTransform_integrable (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    Integrable (fun q : ℝ => spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ)/(q : ℂ))) := by
  exact integrable_spectralTest_mul_K P k t

/-- Exact pointwise factorization. No absolute values or masks are altered. -/
theorem common_height_mode_factorization (P : PacketData ι)
    (k : D4 → ℤ) (t q : ℝ) :
    kModeFunction P (commonHeight t) k q =
      (spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ))) *
        completedPacketSum P k := by
  unfold kModeFunction commonHeight completedPacketSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Main finite-to-integral lemma: the actual coefficient sum is independent
of both q and t, so the genuine K transform can be taken outside it. -/
theorem actual_common_height_modeIntegral (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight t) k q) =
      kTestTransform P k t * completedPacketSum P k := by
  calc
    (∫ q : ℝ, kModeFunction P (commonHeight t) k q) =
        ∫ q : ℝ, (spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ)/(q : ℂ))) * completedPacketSum P k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun q => common_height_mode_factorization P k t q)
    _ = kTestTransform P k t * completedPacketSum P k := by
      exact integral_mul_const (completedPacketSum P k) _

/-- Exact energy factorization; it does not bound either analytic factor. -/
theorem actual_common_height_modeIntegral_norm_sq (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2 =
      ‖kTestTransform P k t‖^2 * ‖completedPacketSum P k‖^2 := by
  rw [actual_common_height_modeIntegral, norm_mul, mul_pow]

/-- The one completed interval and phase can also be factored across levels.
In particular no independently chosen level interval has been introduced. -/
theorem completedPacketSum_common_interval (P : PacketData ι) (k : D4 → ℤ) :
    completedPacketSum P k =
      (∑ m ∈ P.mCarrier, (P.completed k).weight m) *
        (∑ j ∈ P.rows, ∑ n ∈ P.nCarrier j,
          signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n) := by
  unfold completedPacketSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (Finset.sum_mul_sum P.mCarrier (P.nCarrier j)
    (fun m => (P.completed k).weight m)
    (fun n => signedCoefficient P.negativeCusp
      (modePacket (P.packet j) k P.U P.Z) n)).symm

/-- Labelled flattening preserves all original finite copies. -/
abbrev RowLabel (ι : Type*) := (_j : ι) × (ℕ × ℕ)

def labelCarrier (P : PacketData ι) : Finset (RowLabel ι) :=
  P.rows.sigma (fun j => P.mCarrier ×ˢ P.nCarrier j)

def modeAtom (P : PacketData ι) (k : D4 → ℤ) (q : ℝ)
    (l : RowLabel ι) (t : ℝ) : ℂ :=
  spectralTest k P.Y0 q *
    ((P.completed k).weight l.2.1 *
      signedCoefficient P.negativeCusp
        (modePacket (P.packet l.1) k P.U P.Z) l.2.2) *
    ((imaginaryOrderK t q : ℂ)/(q : ℂ))

def modeRow (P : PacketData ι) (k : D4 → ℤ) (q t : ℝ) : ℂ :=
  ∑ l ∈ labelCarrier P, modeAtom P k q l t

theorem modeRow_eq_actual (P : PacketData ι) (k : D4 → ℤ) (q t : ℝ) :
    modeRow P k q t = kModeFunction P (commonHeight t) k q := by
  unfold modeRow labelCarrier
  rw [Finset.sum_sigma]
  simp only [Finset.sum_product, modeAtom, kModeFunction, commonHeight,
    Finset.mul_sum, mul_assoc]

/-- Actual K continuity, not an assumed spectral family continuity premise. -/
theorem modeAtom_continuous (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (l : RowLabel ι) :
    Continuous (modeAtom P k q l) := by
  have hp : Continuous (fun t : ℝ => (t, (⟨q, by change q ≤ q; rfl⟩ : Ici q))) := by
    fun_prop
  have hK : Continuous (fun t : ℝ => (imaginaryOrderK t q : ℂ)) :=
    Complex.continuous_ofReal.comp ((imaginaryOrderK_joint_continuous q hq).comp hp)
  exact continuous_const.mul (hK.div_const (q : ℂ))

theorem modeRow_continuous (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) : Continuous (modeRow P k q) := by
  unfold modeRow
  exact continuous_finsetSum _ (fun l _hl => modeAtom_continuous P k hq l)

/-- This is a genuine raw-height integral, not an unspecified quadratic form. -/
def compactHeightEnergy (P : PacketData ι) (k : D4 → ℤ) (q T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, ‖modeRow P k q t‖^2

theorem compactHeightEnergy_integrable (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (T : ℝ) :
    IntegrableOn (fun t => ‖modeRow P k q t‖^2) (Icc (-T) T) := by
  exact ((modeRow_continuous P k hq).norm.pow 2).continuousOn.integrableOn_compact
    isCompact_Icc

theorem compactHeightEnergy_nonneg (P : PacketData ι) (k : D4 → ℤ)
    (q T : ℝ) : 0 ≤ compactHeightEnergy P k q T := by
  exact integral_nonneg (fun t => sq_nonneg _)

lemma complex_square (z : ℂ) : (‖z‖^2 : ℂ) = z * star z := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj z).symm

/-- Complete Gram expansion. No diagonal or signed off-diagonal is removed. -/
theorem modeRow_full_gram (P : PacketData ι) (k : D4 → ℤ) (q t : ℝ) :
    (‖modeRow P k q t‖^2 : ℂ) =
      ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        modeAtom P k q a t * star (modeAtom P k q b t) := by
  rw [complex_square]
  unfold modeRow
  rw [star_sum, Finset.sum_mul_sum]

theorem gramAtom_integrable (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (T : ℝ) (a b : RowLabel ι) :
    IntegrableOn (fun t => modeAtom P k q a t * star (modeAtom P k q b t))
      (Icc (-T) T) := by
  exact ((modeAtom_continuous P k hq a).mul
    (modeAtom_continuous P k hq b).star).continuousOn.integrableOn_compact isCompact_Icc

/-- Finite-to-integral full Gram identity with all original copies retained.
The explicit q>0 proof prevents positivity of an undefined integral from
being used as evidence of a well-defined spectral quadratic form. -/
theorem actual_compact_height_full_gram (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (T : ℝ) :
    (compactHeightEnergy P k q T : ℂ) =
      ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        ∫ t in Icc (-T) T,
          modeAtom P k q a t * star (modeAtom P k q b t) := by
  have hinner (a : RowLabel ι) :
      IntegrableOn (fun t => ∑ b ∈ labelCarrier P,
        modeAtom P k q a t * star (modeAtom P k q b t)) (Icc (-T) T) :=
    integrable_finsetSum (labelCarrier P)
      (fun b _hb => gramAtom_integrable P k hq T a b)
  calc
    (compactHeightEnergy P k q T : ℂ) =
        ∫ t in Icc (-T) T, (‖modeRow P k q t‖^2 : ℂ) := by
      refine (integral_complex_ofReal (f := fun t : ℝ => ‖modeRow P k q t‖^2)
        (μ := volume.restrict (Icc (-T) T))).symm.trans ?_
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => Complex.ofReal_pow _ _)
    _ = ∫ t in Icc (-T) T,
        ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
          modeAtom P k q a t * star (modeAtom P k q b t) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => modeRow_full_gram P k q t)
    _ = ∑ a ∈ labelCarrier P, ∫ t in Icc (-T) T,
        ∑ b ∈ labelCarrier P,
          modeAtom P k q a t * star (modeAtom P k q b t) :=
      integral_finsetSum (labelCarrier P) (fun a _ha => hinner a)
    _ = ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        ∫ t in Icc (-T) T,
          modeAtom P k q a t * star (modeAtom P k q b t) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact integral_finsetSum (labelCarrier P)
        (fun b _hb => gramAtom_integrable P k hq T a b)

/-- The physical support supplies positivity; callers supply no extra
positive-axis licence or analytic/integrability hypothesis. -/
theorem actual_region_compact_height_full_gram (P : PacketData ι)
    (k : D4 → ℤ) (q T : ℝ) (hq : q ∈ P.region) :
    IntegrableOn (fun t => ‖modeRow P k q t‖^2) (Icc (-T) T) ∧
      0 ≤ compactHeightEnergy P k q T ∧
      (compactHeightEnergy P k q T : ℂ) =
        ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
          ∫ t in Icc (-T) T,
            modeAtom P k q a t * star (modeAtom P k q b t) := by
  have hlow : P.Y0/16 ≤ q := hq.1
  have hqpos : 0 < q := by linarith [P.Y0_pos]
  exact ⟨compactHeightEnergy_integrable P k hqpos T,
    compactHeightEnergy_nonneg P k q T,
    actual_compact_height_full_gram P k hqpos T⟩

end
end ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly

/-!
EXACT OPEN BOUNDARY:
* No theorem here identifies kTestTransform with the normalization, signs,
  cusp scaling matrices, or kernel of the required level-z Kuznetsov formula.
* The compact raw-height Gram identity is not the continuous automorphic
  Plancherel identity. Cusp/Eisenstein coefficients and its positive measure
  have not been supplied or silently replaced by a freely assumed family.
* The regular and exceptional shell estimates, Kim--Sarnak 7/32, coprime ABL
  packet extraction, same-mask enhanced mean and full return (24)/(25) remain.
* PacketData.rows/nCarrier still need the actual original chart/source
  matching. No new dictionary theorem is asserted for original P3 labels.
* This candidate has complete by bodies and zero sorry/admit/axiom commands;
  only ROOT's subsequent strict compilation can establish acceptance.
-/
