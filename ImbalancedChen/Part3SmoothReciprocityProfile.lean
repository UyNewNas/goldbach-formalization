import ImbalancedChen.Part3SharedFirstFactorSmallCoreSmoothFrequency

/-!
# Uniform derivatives of the actual smooth reciprocity profile

The positive circle character here is the slow factor of the existing
three-phase reciprocity identity. Its parameter is a signed real number.
Every derivative of the fixed low pass contributes an inverse scale, and
every derivative of the character contributes its actual modulation
parameter. The fixed Fourier transform pays the entire polynomial weight.

Only ordinary derivatives in the real frequency variable are estimated.
Joint physical-parameter derivatives, Mellin separation and its L1 cost,
periodic root operators and the complementary 7/32 estimate remain separate
proof obligations. In particular, a future total V derivative of the full
physical expression includes the V/L prefactor and the varying Z=X^eta;
its operator is 1+Eu-Erho+eta*EZ, not merely Eu-Erho.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform ContDiff

def CommonSmoothCutoff.smoothReciprocityProfile (Z rho u : ℝ) : ℂ :=
  (CommonSmoothCutoff.poissonSmoothLowPass (u / Z) : ℂ) *
    (𝓕 CommonSmoothCutoff.dyadicCutoffSchwartz) u *
      fourier (1 : ℤ) ((rho * u : ℝ) : UnitAddCircle)

namespace SmoothReciprocityProfileProof

open CommonSmoothCutoff

private def cutoffPart (Z u : ℝ) : ℂ :=
  (poissonSmoothLowPass (u / Z) : ℂ)

private def phasePart (rho u : ℝ) : ℂ :=
  fourier (1 : ℤ) ((rho * u : ℝ) : UnitAddCircle)

private def fixedSpectrum : 𝓢(ℝ, ℂ) := 𝓕 dyadicCutoffSchwartz

private def amplitudePart (Z u : ℝ) : ℂ := cutoffPart Z u * fixedSpectrum u

private def cutoffBound (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 n dyadicCutoffSchwartz

private def spectrumBound (r n : ℕ) : ℝ :=
  2 ^ r * (Finset.Iic (r, n)).sup
    (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) fixedSpectrum

private def amplitudeBound (r n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * cutoffBound i * spectrumBound r (n - i)

private def modulationBound (r J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    (J.choose i : ℝ) * amplitudeBound r i * (2 * Real.pi) ^ (J - i)

private theorem cutoffBound_nonneg (n : ℕ) : 0 ≤ cutoffBound n := by
  unfold cutoffBound
  positivity

private theorem spectrumBound_nonneg (r n : ℕ) : 0 ≤ spectrumBound r n := by
  unfold spectrumBound
  positivity

private theorem amplitudeBound_nonneg (r n : ℕ) : 0 ≤ amplitudeBound r n := by
  unfold amplitudeBound
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (cutoffBound_nonneg i))
    (spectrumBound_nonneg r (n - i))

private theorem modulationBound_nonneg (r J : ℕ) : 0 ≤ modulationBound r J := by
  unfold modulationBound
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (amplitudeBound_nonneg r i))
    (pow_nonneg (by positivity) _)

private theorem cutoffPart_eq_shift (Z : ℝ) :
    cutoffPart Z = fun u : ℝ ↦
      dyadicCutoffSchwartz (3 / 2 + (2 * Z)⁻¹ * u) := by
  funext u
  have harg : (u / Z) / 2 = (2 * Z)⁻¹ * u := by
    calc
      (u / Z) / 2 = u / (Z * 2) := div_div u Z 2
      _ = u / (2 * Z) := by rw [mul_comm Z (2 : ℝ)]
      _ = (2 * Z)⁻¹ * u := by rw [div_eq_mul_inv, mul_comm]
  simp only [cutoffPart, poissonSmoothLowPass,
    dyadicCutoffSchwartz_apply, dyadicCutoff]
  rw [harg]

private theorem cutoffPart_contDiff (Z : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (cutoffPart Z) := by
  rw [cutoffPart_eq_shift]
  exact (dyadicCutoffSchwartz.smooth n).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id))

private theorem cutoffPart_iteratedDeriv (Z : ℝ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (cutoffPart Z) u =
      ((2 * Z)⁻¹) ^ n •
        iteratedDeriv n (dyadicCutoffSchwartz : ℝ → ℂ)
          (3 / 2 + (2 * Z)⁻¹ * u) := by
  rw [cutoffPart_eq_shift]
  have hs : ContDiff ℝ n
      (fun x : ℝ ↦ dyadicCutoffSchwartz (3 / 2 + x)) :=
    (dyadicCutoffSchwartz.smooth n).comp (contDiff_const.add contDiff_id)
  have hscale := congrFun
    (iteratedDeriv_comp_const_smul hs ((2 * Z)⁻¹)) u
  simpa only [iteratedDeriv_comp_const_add] using hscale

/-- The precise inverse-scale factor is kept before using Z >= 1. -/
private theorem cutoffPart_deriv_scaled_bound (Z : ℝ) (hZ : 1 ≤ Z)
    (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (cutoffPart Z) u‖ ≤
      ((2 * Z)⁻¹) ^ n * cutoffBound n := by
  have hlambda : 0 ≤ (2 * Z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hpsi := SchwartzMap.le_seminorm' (𝕜 := ℝ) 0 n dyadicCutoffSchwartz
    (3 / 2 + (2 * Z)⁻¹ * u)
  simp only [pow_zero, one_mul] at hpsi
  rw [cutoffPart_iteratedDeriv, norm_smul, Real.norm_eq_abs,
    abs_pow, abs_of_nonneg hlambda]
  exact mul_le_mul_of_nonneg_left hpsi (pow_nonneg hlambda _)

private theorem cutoffPart_deriv_bound (Z : ℝ) (hZ : 1 ≤ Z)
    (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (cutoffPart Z) u‖ ≤ cutoffBound n := by
  have hlambda : 0 ≤ (2 * Z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hlambda_one : (2 * Z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  calc
    ‖iteratedDeriv n (cutoffPart Z) u‖ ≤
        ((2 * Z)⁻¹) ^ n * cutoffBound n :=
      cutoffPart_deriv_scaled_bound Z hZ n u
    _ ≤ 1 * cutoffBound n :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hlambda hlambda_one)
        (cutoffBound_nonneg n)
    _ = cutoffBound n := one_mul _

private theorem fixedSpectrum_deriv_weighted (r n : ℕ) (u : ℝ) :
    (1 + |u|) ^ r *
        ‖iteratedDeriv n (fixedSpectrum : ℝ → ℂ) u‖ ≤ spectrumBound r n := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (r, n)) le_rfl le_rfl fixedSpectrum u
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    spectrumBound] using h

private theorem phasePart_contDiff (rho : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (phasePart rho) := by
  have hlinear : ContDiff ℝ n
      (fun u : ℝ ↦ (2 * Real.pi * Complex.I * (rho : ℂ)) * (u : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  change ContDiff ℝ n
    (fun u : ℝ ↦ fourier (1 : ℤ) ((rho * u : ℝ) : UnitAddCircle))
  have hphase :
      (fun u : ℝ ↦ fourier (1 : ℤ) ((rho * u : ℝ) : UnitAddCircle)) =
        (fun u : ℝ ↦ Complex.exp
          ((2 * Real.pi * Complex.I * (rho : ℂ)) * (u : ℂ))) := by
    funext u
    rw [fourier_coe_apply]
    congr 1
    simp only [Int.cast_one, mul_one, Complex.ofReal_one, div_one, Complex.ofReal_mul]
    ring
  rw [hphase]
  exact Complex.contDiff_exp.comp hlinear

private theorem phasePart_hasDerivAt (rho u : ℝ) :
    HasDerivAt (phasePart rho)
      ((2 * Real.pi * Complex.I * (rho : ℂ)) * phasePart rho u) u := by
  have h := (hasDerivAt_fourier (1 : ℝ) (1 : ℤ) (rho * u)).scomp u
    ((hasDerivAt_id u).const_mul rho)
  change HasDerivAt
    (fun v : ℝ ↦ fourier (1 : ℤ) ((rho * v : ℝ) : UnitAddCircle))
    ((2 * Real.pi * Complex.I * (rho : ℂ)) *
      fourier (1 : ℤ) ((rho * u : ℝ) : UnitAddCircle)) u
  simpa [Function.comp_def, Complex.real_smul,
    mul_assoc, mul_left_comm, mul_comm] using h

private theorem phasePart_deriv (rho : ℝ) :
    deriv (phasePart rho) = fun u : ℝ ↦
      (2 * Real.pi * Complex.I * (rho : ℂ)) * phasePart rho u := by
  funext u
  exact (phasePart_hasDerivAt rho u).deriv

private theorem phasePart_iteratedDeriv (rho : ℝ) (n : ℕ) :
    iteratedDeriv n (phasePart rho) = fun u : ℝ ↦
      (2 * Real.pi * Complex.I * (rho : ℂ)) ^ n * phasePart rho u := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext u
      rw [deriv_const_mul_field, phasePart_deriv, pow_succ]
      exact (mul_assoc _ _ _).symm

private theorem phasePart_norm (rho u : ℝ) : ‖phasePart rho u‖ = 1 := by
  simp only [phasePart, fourier_apply, Circle.norm_coe]

private theorem phasePart_iteratedDeriv_norm (rho : ℝ) (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (phasePart rho) u‖ =
      (2 * Real.pi) ^ n * |rho| ^ n := by
  rw [phasePart_iteratedDeriv, norm_mul, phasePart_norm, mul_one, norm_pow]
  have hk : ‖(2 * Real.pi * Complex.I * (rho : ℂ))‖ =
      2 * Real.pi * |rho| := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hk, mul_pow]

private theorem phasePart_deriv_bound (rho : ℝ) (n J : ℕ)
    (hn : n ≤ J) (u : ℝ) :
    ‖iteratedDeriv n (phasePart rho) u‖ ≤
      (2 * Real.pi) ^ n * (1 + |rho|) ^ J := by
  rw [phasePart_iteratedDeriv_norm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |rho| ^ n ≤ (1 + |rho|) ^ n :=
      pow_le_pow_left₀ (abs_nonneg rho) (by linarith) n
    _ ≤ (1 + |rho|) ^ J :=
      pow_le_pow_right₀ (by linarith [abs_nonneg rho]) hn

private theorem amplitudePart_contDiff (Z : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (amplitudePart Z) :=
  (cutoffPart_contDiff Z n).mul (fixedSpectrum.smooth n)

private theorem amplitudePart_deriv_weighted (r n : ℕ) (Z : ℝ)
    (hZ : 1 ≤ Z) (u : ℝ) :
    (1 + |u|) ^ r * ‖iteratedDeriv n (amplitudePart Z) u‖ ≤
      amplitudeBound r n := by
  have hw : 0 ≤ (1 + |u|) ^ r := by positivity
  have hprod : iteratedDeriv n (amplitudePart Z) u =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i (cutoffPart Z) u *
          iteratedDeriv (n - i) (fixedSpectrum : ℝ → ℂ) u :=
    iteratedDeriv_mul (n := n) (x := u)
      (cutoffPart_contDiff Z n).contDiffAt (fixedSpectrum.smooth n).contDiffAt
  rw [hprod]
  calc
    (1 + |u|) ^ r * ‖∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i (cutoffPart Z) u *
          iteratedDeriv (n - i) (fixedSpectrum : ℝ → ℂ) u‖ ≤
        (1 + |u|) ^ r * ∑ i ∈ Finset.range (n + 1),
          ‖(n.choose i : ℂ) * iteratedDeriv i (cutoffPart Z) u *
            iteratedDeriv (n - i) (fixedSpectrum : ℝ → ℂ) u‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ i ∈ Finset.range (n + 1), (1 + |u|) ^ r *
          ‖(n.choose i : ℂ) * iteratedDeriv i (cutoffPart Z) u *
            iteratedDeriv (n - i) (fixedSpectrum : ℝ → ℂ) u‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * cutoffBound i * spectrumBound r (n - i) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (1 + |u|) ^ r * ((n.choose i : ℝ) *
            ‖iteratedDeriv i (cutoffPart Z) u‖ *
              ‖iteratedDeriv (n - i) (fixedSpectrum : ℝ → ℂ) u‖) =
            (n.choose i : ℝ) * (‖iteratedDeriv i (cutoffPart Z) u‖ *
              ((1 + |u|) ^ r *
                ‖iteratedDeriv (n - i) (fixedSpectrum : ℝ → ℂ) u‖)) := by ring
        _ ≤ (n.choose i : ℝ) * (cutoffBound i * spectrumBound r (n - i)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul (cutoffPart_deriv_bound Z hZ i u)
            (fixedSpectrum_deriv_weighted r (n - i) u)
            (mul_nonneg hw (norm_nonneg _)) (cutoffBound_nonneg i)
        _ = (n.choose i : ℝ) * cutoffBound i * spectrumBound r (n - i) := by ring
    _ = amplitudeBound r n := rfl

private theorem profile_deriv_weighted (r J : ℕ) (Z rho : ℝ)
    (hZ : 1 ≤ Z) (u : ℝ) :
    (1 + |u|) ^ r *
        ‖iteratedDeriv J (smoothReciprocityProfile Z rho) u‖ ≤
      modulationBound r J * (1 + |rho|) ^ J := by
  have hw : 0 ≤ (1 + |u|) ^ r := by positivity
  have hprod : iteratedDeriv J (smoothReciprocityProfile Z rho) u =
      ∑ i ∈ Finset.range (J + 1), (J.choose i : ℂ) *
        iteratedDeriv i (amplitudePart Z) u *
          iteratedDeriv (J - i) (phasePart rho) u :=
    iteratedDeriv_mul (n := J) (x := u)
      (amplitudePart_contDiff Z J).contDiffAt (phasePart_contDiff rho J).contDiffAt
  rw [hprod]
  calc
    (1 + |u|) ^ r * ‖∑ i ∈ Finset.range (J + 1), (J.choose i : ℂ) *
        iteratedDeriv i (amplitudePart Z) u *
          iteratedDeriv (J - i) (phasePart rho) u‖ ≤
        (1 + |u|) ^ r * ∑ i ∈ Finset.range (J + 1),
          ‖(J.choose i : ℂ) * iteratedDeriv i (amplitudePart Z) u *
            iteratedDeriv (J - i) (phasePart rho) u‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ i ∈ Finset.range (J + 1), (1 + |u|) ^ r *
          ‖(J.choose i : ℂ) * iteratedDeriv i (amplitudePart Z) u *
            iteratedDeriv (J - i) (phasePart rho) u‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (J + 1),
          ((J.choose i : ℝ) * amplitudeBound r i * (2 * Real.pi) ^ (J - i)) *
            (1 + |rho|) ^ J := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (1 + |u|) ^ r * ((J.choose i : ℝ) *
            ‖iteratedDeriv i (amplitudePart Z) u‖ *
              ‖iteratedDeriv (J - i) (phasePart rho) u‖) =
            ((J.choose i : ℝ) * ((1 + |u|) ^ r *
              ‖iteratedDeriv i (amplitudePart Z) u‖)) *
                ‖iteratedDeriv (J - i) (phasePart rho) u‖ := by ring
        _ ≤ ((J.choose i : ℝ) * amplitudeBound r i) *
              ((2 * Real.pi) ^ (J - i) * (1 + |rho|) ^ J) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left
              (amplitudePart_deriv_weighted r i Z hZ u) (Nat.cast_nonneg _))
            (phasePart_deriv_bound rho (J - i) J (Nat.sub_le J i) u)
            (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (amplitudeBound_nonneg r i))
        _ = ((J.choose i : ℝ) * amplitudeBound r i * (2 * Real.pi) ^ (J - i)) *
              (1 + |rho|) ^ J := by ring
    _ = modulationBound r J * (1 + |rho|) ^ J := by
      rw [modulationBound, Finset.sum_mul]

end SmoothReciprocityProfileProof

theorem CommonSmoothCutoff.smoothReciprocityProfile_iteratedDeriv_uniform
    (r J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z rho : ℝ, 1 ≤ Z →
        ∀ u : ℝ,
          (1 + |u|) ^ r *
              ‖iteratedDeriv J
                (CommonSmoothCutoff.smoothReciprocityProfile Z rho) u‖ ≤
            C * (1 + |rho|) ^ J
:= by
  refine ⟨1 + SmoothReciprocityProfileProof.modulationBound r J, ?_, ?_⟩
  · have h := SmoothReciprocityProfileProof.modulationBound_nonneg r J
    linarith
  · intro Z rho hZ u
    calc
      (1 + |u|) ^ r *
          ‖iteratedDeriv J
            (CommonSmoothCutoff.smoothReciprocityProfile Z rho) u‖ ≤
          SmoothReciprocityProfileProof.modulationBound r J * (1 + |rho|) ^ J :=
        SmoothReciprocityProfileProof.profile_deriv_weighted r J Z rho hZ u
      _ ≤ (1 + SmoothReciprocityProfileProof.modulationBound r J) *
            (1 + |rho|) ^ J :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end

end ImbalancedChen.Part3
