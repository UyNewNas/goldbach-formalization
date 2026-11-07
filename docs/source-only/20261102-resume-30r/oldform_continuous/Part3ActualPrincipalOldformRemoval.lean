import ImbalancedChen.Part3ActualFrickeNonzeroFourier
import ImbalancedChen.Part3EisensteinAmplitudeMultiplicativity
import ImbalancedChen.Part3Gamma0DegeneracyMap
import ImbalancedChen.Part3OriginalRowOldformArithmetic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, R22, 2026-11-02.

Actual principal-character completed Eisenstein oldforms, at every
positive integer dilation. The scalar below is identified with the
literal physical Fourier integral of the pre-existing continued family;
it is not an arbitrary raw-rho input. Coprime removal is proved using
the existing finite divisor multiplicativity, and the critical-line
multiplier is bounded by the exact divisor count, uniformly in t.

The actual OriginalData row supplies both coprimality conditions through
Q20. Both signed physical frequencies and t = 0 are retained. No Bessel
value, completed zeta, or Gamma value is divided out on the critical line.

This is the principal-character oldclass only. It does not identify that
oldclass with the full singular-cusp continuous spectrum, construct the
character-pair Plancherel change of basis, or supply the Maass/holomorphic
removal estimates. The amplitude is a completed K amplitude: no claim that
it is already the raw Whittaker rho or the normalized trace R is made.

Import staging: Part3ActualFrickeNonzeroFourier is exact source reuse from
the 20261026b-FrickeNonzero draft. Its formerly held dependency
Part3CompletedIntegerNonzeroFourier must use the R22 minimal repair recorded
in REGISTRY.json. The original frozen files are unchanged.
-/

namespace ImbalancedChen.Part3.ActualPrincipalOldformRemoval20261102r

noncomputable section

open Set MeasureTheory Complex
open scoped BigOperators UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open NormalizedEisensteinPrimeAmplitude20261026b
open EisensteinAmplitudeMultiplicativity20261026b
open CriticalEisensteinScattering20261025a
open CompletedIntegerNonzeroFourier20261026b
open ActualFrickeNonzeroFourier20261026b
open CompletedActualEisensteinIdentity20261025a
open CompletedKWeightedIntegral20261026b
open FiniteLevelEisensteinOldforms20261025a
open PrimitiveEisensteinFourierParameterAnalytic
open ComplexOrderKBridgeSourceOnly
open OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102
open OriginalRowOldformArithmetic20261102
open Gamma0DegeneracyMapSourceOnly
open LevelOldformFricke20261026a
open LevelOldformScattering20261026a
open FrickeNormalizer

theorem pnatDilate_eq_degeneracy (d : ℕ+) (w : ℍ) :
    pnatDilate d w = degeneracyDiagonal d d.pos • w := by
  apply UpperHalfPlane.ext
  rw [degeneracyDiagonal_smul_coe]
  simp [pnatDilate, PrimeLevelEisensteinDegeneracy20261025a.dilate]

/-- The functions whose Fourier amplitudes are used below are actual
Gamma0(N)-invariant oldforms whenever their dilation divides N. -/
theorem principal_dilation_Gamma0_invariant
    (N : ℕ) (hN : 0 < N) (d : ℕ+) (hd : (d : ℕ) ∣ N)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (w : ℍ) :
    completedActualEisenstein s (pnatDilate d (γ • w)) =
      completedActualEisenstein s (pnatDilate d w) := by
  have hNd : 0 < N / (d : ℕ) := Nat.div_pos (Nat.le_of_dvd hN hd) d.pos
  have hmul : N / (d : ℕ) * (d : ℕ) = N := Nat.div_mul_cancel hd
  have h := scaled_function_gamma0_invariant (N / (d : ℕ)) d hNd d.pos
    (completedActualEisenstein s)
    (fun g _ z => completedActualEisenstein_SL2_invariant s hs0 hs1 g z)
    γ (by simpa only [hmul] using hγ) w
  simpa only [pnatDilate_eq_degeneracy] using h

/-- The actual K amplitude of E*(k z,s), with its exact dilation gate.
It is used as a physical oldform only when k > 0. -/
def principalDilationAmplitude (k r : ℕ) (s : ℂ) : ℂ :=
  if k ∣ r then
    (Real.sqrt (k : ℝ) : ℂ) * normalizedDivisorAmplitude (r / k) s
  else 0

/-- Identification with the existing selected actual Fourier coefficient.
The K argument remains 2*pi*r*y; the divisor frequency is r/k. -/
theorem naturalDilationCoefficient_eq_principalAmplitude
    (k r : ℕ) (hk : 0 < k) (hr : 0 < r) (s : ℂ) (y : ℝ) :
    naturalDilationCoefficient k r s y =
      2 * (Real.sqrt y : ℂ) * principalDilationAmplitude k r s *
        complexOrderK (s - 1 / 2) (2 * Real.pi * r * y) := by
  have hcoef := integerDilationCoefficient_eq ⟨k, hk⟩ r hr s y
  change naturalDilationCoefficient k r s y = _ at hcoef
  rw [hcoef]
  by_cases hd : k ∣ r
  · simp only [if_pos hd, principalDilationAmplitude,
      normalizedDivisorAmplitude]
    rw [Real.sqrt_mul (Nat.cast_nonneg k), Complex.ofReal_mul]
    ring
  · simp [principalDilationAmplitude, hd]

/-- Genuine Fourier integral of the continued full-level oldform.
Both choices of the signed integer frequency are explicit. -/
theorem completed_integer_fourier_eq_principalAmplitude
    (k : ℕ+) (r : ℕ) (hr : 0 < r) (s : ℂ)
    (y : ℝ) (hy : 0 < y) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (∫ x in (0 : ℝ)..1,
      completedActualEisenstein s (pnatDilate k (horizontalPoint y hy x)) *
        integerPhase (ε * (r : ℤ)) x) =
      2 * (Real.sqrt y : ℂ) * principalDilationAmplitude k r s *
        complexOrderK (s - 1 / 2) (2 * Real.pi * r * y) := by
  rw [completed_integer_nonzero_integral k r hr s y hy ε hε]
  exact naturalDilationCoefficient_eq_principalAmplitude k r k.pos hr s y

/-- The critical-line power appearing before the actual divisor sum
has norm one. The positive integer base fixes the complex branch. -/
theorem critical_amplitude_power_norm (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (criticalParameter t - 1 / 2)‖ = 1 := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)]
  norm_num [criticalParameter]

theorem critical_divisor_power_norm (d : ℕ) (hd : 0 < d) (t : ℝ) :
    ‖(d : ℂ) ^ (1 - 2 * criticalParameter t)‖ = 1 := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hd)]
  norm_num [criticalParameter]

/-- Zero Ramanujan power for the actual untwisted multiplier, uniformly
in every real height including zero. The exact divisor loss is retained. -/
theorem normalizedAmplitude_critical_norm_le_divisors (n : ℕ) (t : ℝ) :
    ‖normalizedDivisorAmplitude n (criticalParameter t)‖ ≤
      (n.divisors.card : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, normalizedDivisorAmplitude, divisorFactor]
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [normalizedDivisorAmplitude, norm_mul,
    critical_amplitude_power_norm n hpos t, one_mul]
  unfold divisorFactor
  calc
    ‖∑ d ∈ n.divisors, (d : ℂ) ^ (1 - 2 * criticalParameter t)‖ ≤
        ∑ d ∈ n.divisors, ‖(d : ℂ) ^ (1 - 2 * criticalParameter t)‖ :=
      norm_sum_le _ _
    _ = ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact critical_divisor_power_norm d (Nat.pos_of_mem_divisors hd) t
    _ = (n.divisors.card : ℝ) := by simp

/-- Coprime index removal on EACH actual principal-character dilation.
The proof retains the zero branch when the dilation does not divide n. -/
theorem principalDilationAmplitude_mul_of_coprime
    (k a n : ℕ) (hk : 0 < k) (hak : a.Coprime k)
    (han : a.Coprime n) (s : ℂ) :
    principalDilationAmplitude k (a * n) s =
      normalizedDivisorAmplitude a s * principalDilationAmplitude k n s := by
  have hgate : k ∣ a * n ↔ k ∣ n := hak.symm.dvd_mul_left
  by_cases hkn : k ∣ n
  · have hkan : k ∣ a * n := hgate.mpr hkn
    have hquot : a * n / k = a * (n / k) := by
      apply Nat.eq_of_mul_eq_mul_left hk
      calc
        k * (a * n / k) = a * n := Nat.mul_div_cancel' hkan
        _ = a * (k * (n / k)) := by rw [Nat.mul_div_cancel' hkn]
        _ = k * (a * (n / k)) := by ring
    have hcop : a.Coprime (n / k) := han.of_dvd_right (Nat.div_dvd_of_dvd hkn)
    simp only [principalDilationAmplitude, if_pos hkan, if_pos hkn, hquot,
      normalizedAmplitude_mul_of_coprime hcop]
    ring
  · have hkan : ¬ k ∣ a * n := fun h => hkn (hgate.mp h)
    simp [principalDilationAmplitude, hkn, hkan]

/-- Actual OriginalData supplies the arithmetic prerequisites. The
positive dilation belongs to the principal-character oldclass at z. -/
theorem original_row_principal_dilation_removal
    (D : OriginalData) (key : BlockKey) (z : Row D key)
    (d : ℕ+) (hd : (d : ℕ) ∣ z.val)
    {n : ℕ} (hn : n ∈ nCarrier D key z.val) (s : ℂ) :
    principalDilationAmplitude d ((D.block.atom.residue.natAbs * key.1) * n) s =
      normalizedDivisorAmplitude (D.block.atom.residue.natAbs * key.1) s *
        principalDilationAmplitude d n s := by
  apply principalDilationAmplitude_mul_of_coprime d _ n d.pos
  · exact (original_abl_argument_coprime_level D key z).of_dvd_right hd
  · exact (original_index_coprime_abl_argument D key z hn).symm

/-- The squared pointwise cost on the actual row is a divisor loss and
has no t power. This is not a full cusp-summed continuous quadratic form. -/
theorem original_row_principal_dilation_norm_sq
    (D : OriginalData) (key : BlockKey) (z : Row D key)
    (d : ℕ+) (hd : (d : ℕ) ∣ z.val)
    {n : ℕ} (hn : n ∈ nCarrier D key z.val) (t : ℝ) :
    ‖principalDilationAmplitude d ((D.block.atom.residue.natAbs * key.1) * n)
        (criticalParameter t)‖ ^ 2 ≤
      ((D.block.atom.residue.natAbs * key.1).divisors.card : ℝ) ^ 2 *
        ‖principalDilationAmplitude d n (criticalParameter t)‖ ^ 2 := by
  rw [original_row_principal_dilation_removal D key z d hd hn,
    norm_mul, mul_pow]
  have h := normalizedAmplitude_critical_norm_le_divisors
    (D.block.atom.residue.natAbs * key.1) t
  have hsq : ‖normalizedDivisorAmplitude (D.block.atom.residue.natAbs * key.1)
      (criticalParameter t)‖ ^ 2 ≤
      ((D.block.atom.residue.natAbs * key.1).divisors.card : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- The same removal is bound to the literal physical Fourier integral,
with the original multiplied frequency and its K argument both retained.
The nonzero original residue is necessary only for this nonzero mode. -/
theorem original_row_principal_dilation_fourier_critical
    (D : OriginalData) (key : BlockKey) (z : Row D key)
    (ha : D.block.atom.residue ≠ 0)
    (d : ℕ+) (hd : (d : ℕ) ∣ z.val)
    {n : ℕ} (hn : n ∈ nCarrier D key z.val)
    (t y : ℝ) (hy : 0 < y) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (∫ x in (0 : ℝ)..1,
      completedActualEisenstein (criticalParameter t)
        (pnatDilate d (horizontalPoint y hy x)) *
          integerPhase (ε * (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℤ)) x) =
      2 * (Real.sqrt y : ℂ) *
        (normalizedDivisorAmplitude (D.block.atom.residue.natAbs * key.1)
          (criticalParameter t) * principalDilationAmplitude d n (criticalParameter t)) *
        complexOrderK (criticalParameter t - 1 / 2)
          (2 * Real.pi * (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℝ) * y) := by
  have hsource := nCarrier_positive_coprime D key z.val hn
  have hA : 0 < D.block.atom.residue.natAbs * key.1 :=
    Nat.mul_pos (Int.natAbs_pos.mpr ha) hsource.1
  rw [completed_integer_fourier_eq_principalAmplitude d _
      (Nat.mul_pos hA hsource.2.1) (criticalParameter t) y hy ε hε,
    original_row_principal_dilation_removal D key z d hd hn]

/-- The K amplitude of the actual finite reflected completed level series.
The canonical oldform list, its coefficients and its normalization are
all the original constructions; no basis is chosen here. -/
def principalReflectedAmplitude (N r : ℕ) (s : ℂ) : ℂ :=
  ((oldformTerms (canonicalPrimeList N) s).map (fun v =>
    v.2 * principalDilationAmplitude (N / (v.1 : ℕ)) r s)).sum /
      oldformNormalization (canonicalPrimeList N) s

theorem reflectedNonzeroCoefficient_eq_principalAmplitude
    (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : 0 < r) (s : ℂ) (y : ℝ) :
    reflectedNonzeroCoefficient N r s y =
      2 * (Real.sqrt y : ℂ) * principalReflectedAmplitude N r s *
        complexOrderK (s - 1 / 2) (2 * Real.pi * r * y) := by
  have hmap :
      (oldformTerms (canonicalPrimeList N) s).map (fun v =>
        v.2 * naturalDilationCoefficient (N / (v.1 : ℕ)) r s y) =
      (oldformTerms (canonicalPrimeList N) s).map (fun v =>
        (2 * (Real.sqrt y : ℂ)) *
          (v.2 * principalDilationAmplitude (N / (v.1 : ℕ)) r s) *
            complexOrderK (s - 1 / 2) (2 * Real.pi * r * y)) := by
    apply List.map_congr_left
    intro v hv
    have hvN := canonical_oldform_index_dvd N hN s v hv
    have hcomp : 0 < N / (v.1 : ℕ) :=
      Nat.div_pos (Nat.le_of_dvd hN hvN) v.1.pos
    rw [naturalDilationCoefficient_eq_principalAmplitude _ r hcomp hr s y]
    ring
  unfold reflectedNonzeroCoefficient principalReflectedAmplitude
  rw [hmap, List.sum_map_mul_right, List.sum_map_mul_left]
  ring

/-- Removal for the whole original finite principal-character expression,
including its genuine Euler normalization and every complementary dilation. -/
theorem principalReflectedAmplitude_mul_of_coprime
    (N : ℕ) (hN : 0 < N) (a n : ℕ)
    (haN : a.Coprime N) (han : a.Coprime n) (s : ℂ) :
    principalReflectedAmplitude N (a * n) s =
      normalizedDivisorAmplitude a s * principalReflectedAmplitude N n s := by
  have hmap :
      (oldformTerms (canonicalPrimeList N) s).map (fun v =>
        v.2 * principalDilationAmplitude (N / (v.1 : ℕ)) (a * n) s) =
      (oldformTerms (canonicalPrimeList N) s).map (fun v =>
        normalizedDivisorAmplitude a s *
          (v.2 * principalDilationAmplitude (N / (v.1 : ℕ)) n s)) := by
    apply List.map_congr_left
    intro v hv
    have hvN := canonical_oldform_index_dvd N hN s v hv
    have hcomp : 0 < N / (v.1 : ℕ) :=
      Nat.div_pos (Nat.le_of_dvd hN hvN) v.1.pos
    have hacomp : a.Coprime (N / (v.1 : ℕ)) :=
      haN.of_dvd_right (Nat.div_dvd_of_dvd hvN)
    rw [principalDilationAmplitude_mul_of_coprime _ a n hcomp hacomp han s]
    ring
  unfold principalReflectedAmplitude
  rw [hmap, List.sum_map_mul_left]
  ring

/-- Original actual row, literal Fricke Fourier integral, all real t,
both signed frequencies. This still concerns one completed incoming
Eisenstein family; it is not the full continuous Plancherel identity. -/
theorem original_row_completed_fricke_removal_critical
    (D : OriginalData) (key : BlockKey) (z : Row D key)
    (ha : D.block.atom.residue ≠ 0)
    {n : ℕ} (hn : n ∈ nCarrier D key z.val)
    (t y : ℝ) (hy : 0 < y) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (∫ x in (0 : ℝ)..1,
      completedLevelOldform z.val (criticalParameter t)
        (frickeSL z.val (levelCarrier_licensed D key z.property).1 •
          horizontalPoint y hy x) *
        integerPhase (ε * (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℤ)) x) =
      2 * (Real.sqrt y : ℂ) *
        (normalizedDivisorAmplitude (D.block.atom.residue.natAbs * key.1)
          (criticalParameter t) * principalReflectedAmplitude z.val n (criticalParameter t)) *
        complexOrderK (criticalParameter t - 1 / 2)
          (2 * Real.pi * (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℝ) * y) := by
  have hz : 0 < z.val := (levelCarrier_licensed D key z.property).1
  have hsource := nCarrier_positive_coprime D key z.val hn
  have hA : 0 < D.block.atom.residue.natAbs * key.1 :=
    Nat.mul_pos (Int.natAbs_pos.mpr ha) hsource.1
  have hr := Nat.mul_pos hA hsource.2.1
  rw [completed_fricke_nonzero_integral_critical z.val hz t _ hr y hy ε hε,
    reflectedNonzeroCoefficient_eq_principalAmplitude z.val hz _ hr (criticalParameter t) y,
    principalReflectedAmplitude_mul_of_coprime z.val hz _ n
      (original_abl_argument_coprime_level D key z)
      (original_index_coprime_abl_argument D key z hn).symm]

end

end ImbalancedChen.Part3.ActualPrincipalOldformRemoval20261102r
