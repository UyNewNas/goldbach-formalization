import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Algebra.Star.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED. CODE_ONLY, 2026-10-24.
The actual false cusp has e(-n/z); the actual true cusp has e(+n/z).
Conjugating beta and flipping the Bool therefore conjugates the actual signed
coefficient. All four mode frequencies are reflected. No beta reality,
normalizedF conjugation, rho/sigma symmetry, or Fourier-coefficient symmetry
is assumed. The unchanged arbitrary PacketData.kernel is not claimed real;
the final assertions use the actual real imaginaryOrderK kernel instead.
This module imports actual repository modules only and is independent of the
previous uninstalled symmetry candidate. Private phase lemmas are included.
-/

namespace ImbalancedChen.Part3.ActualConjugatedPacketP3SourceOnly
noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e chi spectralMode spectralTest)
open P3ActualLiteralPacketIntegralSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ImaginaryOrderKBesselSourceOnly

variable {ι : Type*}

private theorem actual_e_neg (s : ℝ) : e (-s) = star (e s) := by
  unfold e
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

private theorem actual_spectralTest_neg_frequency (k : D4 → ℤ) (Y0 q : ℝ) :
    spectralTest (-k) Y0 q = star (spectralTest k Y0 q) := by
  have hphase : ((-k) 0 : ℝ) / 64 * (q / Y0) =
      -((k 0 : ℝ) / 64 * (q / Y0)) := by
    change ((-(k 0) : ℤ) : ℝ) / 64 * (q / Y0) =
      -((k 0 : ℝ) / 64 * (q / Y0))
    rw [Int.cast_neg]
    ring
  change (chi (q / Y0) : ℂ) * e (((-k) 0 : ℝ) / 64 * (q / Y0)) =
    star ((chi (q / Y0) : ℂ) * e ((k 0 : ℝ) / 64 * (q / Y0)))
  rw [hphase, actual_e_neg, star_mul']
  simp only [Complex.star_def, Complex.conj_ofReal]

/-- Only beta is conjugated; the residue, multiplier, level and proofs survive. -/
def conjugatedCoprimePacket (d : CoprimePacket) : CoprimePacket :=
  { d with beta := fun y z => star (d.beta y z) }

theorem conjugatedCoprimePacket_frozen (d : CoprimePacket) :
    (conjugatedCoprimePacket d).residue = d.residue ∧
      (conjugatedCoprimePacket d).multiplier = d.multiplier ∧
      (conjugatedCoprimePacket d).level = d.level := by
  exact ⟨rfl, rfl, rfl⟩

theorem conjugatedCoprimePacket_beta (d : CoprimePacket) (y z : ℕ) :
    (conjugatedCoprimePacket d).beta y z = star (d.beta y z) := by
  rfl

theorem conjugatedCoprimePacket_involutive (d : CoprimePacket) :
    conjugatedCoprimePacket (conjugatedCoprimePacket d) = d := by
  cases d
  simp only [conjugatedCoprimePacket, star_star]

/-- Both signed cusp phases are checked by the actual Bool convention. -/
theorem cuspPhase_not (negative : Bool) (z n : ℕ) :
    cuspPhase (!negative) z n = star (cuspPhase negative z n) := by
  have hphase : (if !negative then (1 : ℝ) else -1) * (n : ℝ) / (z : ℝ) =
      -((if negative then (1 : ℝ) else -1) * (n : ℝ) / (z : ℝ)) := by
    cases negative <;> simp <;> ring
  unfold cuspPhase
  rw [hphase]
  exact actual_e_neg _

/-- Exact signed coefficient conjugation, including the unchanged coprime mask. -/
theorem signedCoefficient_conjugated (negative : Bool) (d : CoprimePacket)
    (n : ℕ) :
    signedCoefficient (!negative) (conjugatedCoprimePacket d) n =
      star (signedCoefficient negative d n) := by
  by_cases hc : Nat.Coprime n d.residue
  · simp only [signedCoefficient, conjugatedCoprimePacket, if_pos hc,
      cuspPhase_not, star_mul']
  · simp only [signedCoefficient, conjugatedCoprimePacket, if_neg hc, star_zero]

theorem signedCoefficient_true_conjugated (d : CoprimePacket) (n : ℕ) :
    signedCoefficient true (conjugatedCoprimePacket d) n =
      star (signedCoefficient false d n) := by
  exact signedCoefficient_conjugated false d n

theorem signedCoefficient_false_conjugated (d : CoprimePacket) (n : ℕ) :
    signedCoefficient false (conjugatedCoprimePacket d) n =
      star (signedCoefficient true d n) := by
  exact signedCoefficient_conjugated true d n

/-- Conjugation reflects exactly the k2/k3 packet modulation phases. -/
theorem modePacket_conjugated (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) :
    modePacket (conjugatedCoprimePacket d) (-k) U Z =
      conjugatedCoprimePacket (modePacket d k U Z) := by
  have h2 : ((-k) 2 : ℝ) = -(k 2 : ℝ) := by
    change ((-(k 2) : ℤ) : ℝ) = -(k 2 : ℝ)
    exact Int.cast_neg _
  have h3 : ((-k) 3 : ℝ) = -(k 3 : ℝ) := by
    change ((-(k 3) : ℤ) : ℝ) = -(k 3 : ℝ)
    exact Int.cast_neg _
  have hphase (y z : ℕ) :
      ((-k) 2 : ℝ) / 64 * ((y : ℝ) / U) +
        ((-k) 3 : ℝ) / 64 * ((z : ℝ) / Z) =
      -((k 2 : ℝ) / 64 * ((y : ℝ) / U) +
        (k 3 : ℝ) / 64 * ((z : ℝ) / Z)) := by
    rw [h2, h3]
    ring
  have hbeta :
      (fun y z : ℕ => star (d.beta y z) *
        e (((-k) 2 : ℝ) / 64 * ((y : ℝ) / U) +
          ((-k) 3 : ℝ) / 64 * ((z : ℝ) / Z))) =
      (fun y z : ℕ => star (d.beta y z *
        e ((k 2 : ℝ) / 64 * ((y : ℝ) / U) +
          (k 3 : ℝ) / 64 * ((z : ℝ) / Z)))) := by
    funext y z
    rw [hphase, actual_e_neg, star_mul']
  exact congrArg (fun b : ℕ → ℕ → ℂ => ({ d with beta := b } : CoprimePacket)) hbeta

theorem signedCoefficient_modePacket_conjugated (negative : Bool)
    (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    signedCoefficient (!negative)
        (modePacket (conjugatedCoprimePacket d) (-k) U Z) n =
      star (signedCoefficient negative (modePacket d k U Z) n) := by
  rw [modePacket_conjugated, signedCoefficient_conjugated]

/-- The one completed interval is unchanged, and its k1 phase is conjugated. -/
theorem completed_weight_neg_frequency (P : PacketData ι) (k : D4 → ℤ)
    (m : ℕ) :
    (P.completed (-k)).weight m = star ((P.completed k).weight m) := by
  by_cases hm : m ∈ P.mCarrier
  · rw [P.completed_weight_mem (-k) m hm, P.completed_weight_mem k m hm]
    have hphase : ((-k) 1 : ℝ) / 64 * ((m : ℝ) / P.V) =
        -((k 1 : ℝ) / 64 * ((m : ℝ) / P.V)) := by
      change ((-(k 1) : ℤ) : ℝ) / 64 * ((m : ℝ) / P.V) =
        -((k 1 : ℝ) / 64 * ((m : ℝ) / P.V))
      rw [Int.cast_neg]
      ring
    rw [hphase, actual_e_neg]
  · change m ∉ Finset.Ico P.lo P.hi at hm
    simp only [PacketData.completed, CommonCompletedVariable.weight,
      if_neg hm, star_zero]

/-- The actual data changes only the packet beta and the signed-cusp flag. -/
def conjugatedPacketData (P : PacketData ι) : PacketData ι :=
  { P with
    packet := fun j => conjugatedCoprimePacket (P.packet j)
    negativeCusp := !P.negativeCusp }

theorem conjugatedPacketData_frozen (P : PacketData ι) :
    (conjugatedPacketData P).rows = P.rows ∧
      (conjugatedPacketData P).nCarrier = P.nCarrier ∧
      (conjugatedPacketData P).mCarrier = P.mCarrier ∧
      (conjugatedPacketData P).completed = P.completed ∧
      (conjugatedPacketData P).region = P.region ∧
      (conjugatedPacketData P).Y0 = P.Y0 ∧
      (conjugatedPacketData P).V = P.V ∧
      (conjugatedPacketData P).U = P.U ∧
      (conjugatedPacketData P).Z = P.Z ∧
      (conjugatedPacketData P).rho = P.rho ∧
      (conjugatedPacketData P).sigma = P.sigma ∧
      (conjugatedPacketData P).kernel = P.kernel := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Full finite packet conjugation, with every original j/m/n copy retained. -/
theorem completedPacketSum_conjugated_neg_frequency (P : PacketData ι)
    (k : D4 → ℤ) :
    completedPacketSum (conjugatedPacketData P) (-k) =
      star (completedPacketSum P k) := by
  change
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed (-k)).weight m *
        signedCoefficient (!P.negativeCusp)
          (modePacket (conjugatedCoprimePacket (P.packet j)) (-k) P.U P.Z) n) =
    star (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp
          (modePacket (P.packet j) k P.U P.Z) n)
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  rw [completed_weight_neg_frequency, signedCoefficient_modePacket_conjugated,
    star_mul']

/-- The analytic transform sees only Y0, and not beta or the cusp sign. -/
theorem kTestTransform_conjugated (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform (conjugatedPacketData P) k t = kTestTransform P k t := by
  rfl

/-- Actual real K, real dq/q denominator and the real cutoff supply conjugation. -/
theorem kTestTransform_conjugated_neg_frequency (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform (conjugatedPacketData P) (-k) t =
      star (kTestTransform P k t) := by
  unfold kTestTransform
  change (∫ q : ℝ, spectralTest (-k) P.Y0 q *
      ((imaginaryOrderK t q : ℂ) / (q : ℂ))) =
    star (∫ q : ℝ, spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ) / (q : ℂ)))
  calc
    _ = ∫ q : ℝ, star (spectralTest k P.Y0 q *
        ((imaginaryOrderK t q : ℂ) / (q : ℂ))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        rw [actual_spectralTest_neg_frequency, star_mul']
        simp only [star_div₀, Complex.star_def, Complex.conj_ofReal])
    _ = _ := by
      simpa only [Complex.star_def] using
        (integral_conj (f := fun q : ℝ => spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ) / (q : ℂ))))

/-- Pointwise conjugation of the actual common-height K mode, including beta. -/
theorem common_height_kModeFunction_conjugated (P : PacketData ι)
    (k : D4 → ℤ) (t q : ℝ) :
    kModeFunction (conjugatedPacketData P) (commonHeight t) (-k) q =
      star (kModeFunction P (commonHeight t) k q) := by
  rw [common_height_mode_factorization, common_height_mode_factorization]
  change (spectralTest (-k) P.Y0 q *
      ((imaginaryOrderK t q : ℂ) / (q : ℂ))) *
        completedPacketSum (conjugatedPacketData P) (-k) =
    star ((spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ) / (q : ℂ))) * completedPacketSum P k)
  rw [actual_spectralTest_neg_frequency, completedPacketSum_conjugated_neg_frequency]
  simp only [star_mul', star_div₀, Complex.star_def, Complex.conj_ofReal]

/-- Actual mode-integral conjugation; no complex packet factor is discarded. -/
theorem actual_common_height_modeIntegral_conjugated (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction (conjugatedPacketData P) (commonHeight t) (-k) q) =
      star (∫ q : ℝ, kModeFunction P (commonHeight t) k q) := by
  rw [actual_common_height_modeIntegral, actual_common_height_modeIntegral,
    kTestTransform_conjugated_neg_frequency,
    completedPacketSum_conjugated_neg_frequency, star_mul']

/-- K's actual evenness also permits reflecting the one common height. -/
theorem common_height_kModeFunction_neg_height (P : PacketData ι)
    (k : D4 → ℤ) (t q : ℝ) :
    kModeFunction P (commonHeight (-t)) k q =
      kModeFunction P (commonHeight t) k q := by
  rw [common_height_mode_factorization, common_height_mode_factorization,
    imaginaryOrderK_neg]

theorem actual_common_height_modeIntegral_conjugated_reflected_height
    (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction (conjugatedPacketData P) (commonHeight (-t)) (-k) q) =
      star (∫ q : ℝ, kModeFunction P (commonHeight t) k q) := by
  calc
    _ = ∫ q : ℝ,
        kModeFunction (conjugatedPacketData P) (commonHeight t) (-k) q := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q =>
        common_height_kModeFunction_neg_height (conjugatedPacketData P) (-k) t q)
    _ = _ := actual_common_height_modeIntegral_conjugated P k t

/-- The literal record-updated modeFunction adapter uses the specific K kernel. -/
theorem withKKernel_common_height_modeIntegral_conjugated (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ,
      (withKKernel (conjugatedPacketData P) (commonHeight t)).modeFunction (-k) q) =
      star (∫ q : ℝ, (withKKernel P (commonHeight t)).modeFunction k q) := by
  rw [withKKernel_modeFunction, withKKernel_modeFunction]
  exact actual_common_height_modeIntegral_conjugated P k t

end
end ImbalancedChen.Part3.ActualConjugatedPacketP3SourceOnly

/-!
OPEN BOUNDARY: neither the actual physical normalizedF nor actualCoeff is
claimed Hermitian. Consequently there is no theorem here identifying the
conjugated physical packet with the conjugate of the original physical
packet, and no sum-over-k conjugation theorem for actual Fourier coefficients.
rho and sigma are preserved without any conjectural sign-change law.
The arbitrary original PacketData.kernel is also preserved without asserting
its reality. The final mode-integral theorems explicitly select the actual
real K kernel, whose height evenness has already been proved in the actual
import. No spectral estimate or manuscript endpoint is supplied.
All proof bodies are source only, uncompiled and unaccepted.
-/
