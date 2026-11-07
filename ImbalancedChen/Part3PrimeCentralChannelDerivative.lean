import ImbalancedChen.Part3PrimeCompletedChannelReflection
import ImbalancedChen.Part3CentralHeightLogEuler

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The evenness of the actual full-level completed Fourier family forces its
genuine parameter derivative to vanish at 1/2. Differentiating the actual
prime oldform expression therefore gives a signed cross-channel identity
for the completed derivative. This is a pointwise identity of physical
functions, not a constraint imposed on prescribed scattering entries.
The ordinary central derivative is then retained through its proved
factor 2, with both independent cusp channels and their exact signs.
-/

noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.PrimeCompletedChannelReflection20261026b
open ImbalancedChen.Part3.CentralHeightLogEuler20261026b
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b

/-- Evenness is used on a genuine open neighborhood, rather than at just
the fixed point of the reflection. -/
theorem completedActual_hasDerivAt_center_zero (z : UpperHalfPlane) :
    HasDerivAt (fun s : ℂ => completedActualEisenstein s z) 0 (1 / 2 : ℂ) := by
  let d : ℂ := deriv (fun s : ℂ => completedActualEisenstein s z) (1 / 2)
  have hF : HasDerivAt (fun s : ℂ => completedActualEisenstein s z) d (1 / 2 : ℂ) :=
    (completedActualEisenstein_analyticOnNhd z (1 / 2) (by norm_num)).differentiableAt.hasDerivAt
  have hR : HasDerivAt (fun s : ℂ => completedActualEisenstein (1 - s) z)
      (-d) (1 / 2 : ℂ) := by
    convert hF.comp (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1) using 1 <;> norm_num
  have he : (fun s : ℂ => completedActualEisenstein (1 - s) z) =ᶠ[𝓝 (1 / 2 : ℂ)]
      (fun s : ℂ => completedActualEisenstein s z) := by
    have hstrip : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ 𝓝 (1 / 2 : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
    filter_upwards [hstrip] with s hs
    have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs.1
    have hs1 : s ≠ 1 := by intro h; subst s; simpa using hs.2
    exact completedActual_reflection s hs0 hs1 z
  have hd : -d = d := (hR.congr_of_eventuallyEq he.symm).unique hF
  have hd0 : d = 0 := by linear_combination -(1 / 2 : ℂ) * hd
  simpa only [hd0] using hF

theorem primeRatio_hasDerivAt {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (primeRatio p)
      (-(Real.log (p : ℝ) : ℂ) * primeRatio p s) s := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := ((hasDerivAt_id s).neg).const_cpow (c := (p : ℂ)) (Or.inl hp0)
  convert h using 1 <;>
    simp [primeRatio, ← Complex.ofReal_log (Nat.cast_nonneg p), mul_comm, mul_left_comm, mul_assoc]

/-- Signed genuine central cross-channel derivative of the actual completed
prime Eisenstein family. Both completed central cusp functions are retained. -/
theorem completed_prime_hasDerivAt_center_cross {p : ℕ} (hp : p.Prime) (z : UpperHalfPlane) :
    HasDerivAt (fun s : ℂ => completedLevelOldform p s z)
      (-(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
          completedLevelOldform p (1 / 2) z +
        ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) /
          (1 - primeRatio p (1 / 2) ^ 2)) *
            completedLevelOldform p (1 / 2) (frickeSL p hp.pos • z)) (1 / 2 : ℂ) := by
  let c : ℂ := 1 / 2
  let q : ℂ := primeRatio p c
  let L : ℂ := (Real.log (p : ℝ) : ℂ)
  let X : ℂ := completedActualEisenstein c z
  let Y : ℂ := completedActualEisenstein c (pnatDilate ⟨p, hp.pos⟩ z)
  have hq : HasDerivAt (primeRatio p) (-L * q) c := primeRatio_hasDerivAt hp c
  have hX := completedActual_hasDerivAt_center_zero z
  have hY := completedActual_hasDerivAt_center_zero (pnatDilate ⟨p, hp.pos⟩ z)
  have hd : 1 - q ^ 2 ≠ 0 := prime_local_denominator_ne_zero hp (by norm_num : 0 < c.re)
  have hNum := hq.mul (hY.sub (hq.mul hX))
  have hDen := (hq.pow 2).const_sub 1
  have hRaw := hNum.div hDen hd
  have hSimplified : HasDerivAt (fun s : ℂ => primeRatio p s *
      (completedActualEisenstein s (pnatDilate ⟨p, hp.pos⟩ z) -
        primeRatio p s * completedActualEisenstein s z) / (1 - primeRatio p s ^ 2))
      (L * q * (2 * q * X - (1 + q ^ 2) * Y) / (1 - q ^ 2) ^ 2) c := by
    convert hRaw using 1 <;> dsimp only [X, Y, q, L, c] <;> ring
  have hNative : HasDerivAt (fun s : ℂ => completedLevelOldform p s z)
      (L * q * (2 * q * X - (1 + q ^ 2) * Y) / (1 - q ^ 2) ^ 2) c := by
    apply hSimplified.congr_of_eventuallyEq
    have hpos : {s : ℂ | 0 < s.re} ∈ 𝓝 c :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [c])
    filter_upwards [hpos] with s hs
    exact completed_prime_q_explicit hp s hs z
  convert hNative using 1
  rw [completed_prime_q_explicit hp c (by norm_num [c]),
    completed_prime_fricke_q_explicit hp c (by norm_num [c]) (by norm_num [c])]
  change -L / (1 - q ^ 2) * (q * (Y - q * X) / (1 - q ^ 2)) +
    (L * q / (1 - q ^ 2)) * (q * (X - q * Y) / (1 - q ^ 2)) = _
  field_simp [hd]
  <;> ring

theorem completed_prime_deriv_center_cross {p : ℕ} (hp : p.Prime) (z : UpperHalfPlane) :
    deriv (fun s : ℂ => completedLevelOldform p s z) (1 / 2) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
          completedLevelOldform p (1 / 2) z +
        ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) /
          (1 - primeRatio p (1 / 2) ^ 2)) *
            completedLevelOldform p (1 / 2) (frickeSL p hp.pos • z) :=
  (completed_prime_hasDerivAt_center_cross hp z).deriv

/-- The second row follows at the actual Fricke point, using the proved
geometric involution; the two physical channel functions stay distinct. -/
theorem completed_prime_fricke_deriv_center_cross {p : ℕ} (hp : p.Prime)
    (z : UpperHalfPlane) :
    deriv (fun s : ℂ => completedLevelOldform p s (frickeSL p hp.pos • z)) (1 / 2) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
          completedLevelOldform p (1 / 2) (frickeSL p hp.pos • z) +
        ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) /
          (1 - primeRatio p (1 / 2) ^ 2)) * completedLevelOldform p (1 / 2) z := by
  simpa only [frickeSL_action_involutive p hp.pos z] using
    completed_prime_deriv_center_cross hp (frickeSL p hp.pos • z)

/-- The same physical cross-channel identity expressed in genuine ordinary
central derivatives. The common factor two cancels, with no pole division. -/
theorem completed_prime_deriv_center_in_ordinary_channels {p : ℕ} (hp : p.Prime)
    (z : UpperHalfPlane) :
    2 * deriv (fun s : ℂ => completedLevelOldform p s z) (1 / 2) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        deriv (fun s : ℂ => centralOrdinaryLevel p s z) (1 / 2) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) /
        (1 - primeRatio p (1 / 2) ^ 2)) *
          deriv (fun s : ℂ => centralOrdinaryLevel p s (frickeSL p hp.pos • z)) (1 / 2) := by
  rw [completed_prime_deriv_center_cross hp z]
  simp_rw [centralOrdinaryLevel_deriv_center]
  ring

end ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b
