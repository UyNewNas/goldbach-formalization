import ImbalancedChen.Part3DistributionTargets
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators

/-!
# Finite complex dispersion for the actual medium atom

The physical modulus remains q1*q2*q3. The three factor labels and the
beta label are kept separately, including different factorizations of the
same modulus and every inactive gamma. Both complex coefficients and the
literal primitive-coprime centre stay in the exact finite identities.

Cauchy is applied only after the entire signed modulus row is formed.
Its proof uses Mathlib's finite squared Cauchy inequality for the norms
of alpha and that complete complex row. No absolute values are inserted
inside the modulus or beta sums and no source coefficient is replaced.

The double-star identity provides the exact pair of labelled rows needed
by a later completion argument. This module does not construct the common
Poisson interval or identify that completed pair with an IV.3 reciprocal
AP. It proves no auxiliary SW, gcd average or RestrictedMediumObligation.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

/-- The original complete physical modulus, with its three labels. -/
def complexFactorModulus (r : ℕ × ℕ × ℕ) : ℕ := r.1 * r.2.1 * r.2.2

/-- The original complex factor coefficient, with no absolute value or
normalization by a number of factorizations. -/
def MediumAtom.complexFactorGamma (d : MediumAtom) (r : ℕ × ℕ × ℕ) : ℂ :=
  d.gamma1 r.1 * d.gamma2 r.2.1 * d.gamma3 r.2.2

def MediumAtom.complexFactorLabels (d : MediumAtom) : Finset (ℕ × ℕ × ℕ) :=
  factorCarrier d.Q1 ×ˢ (factorCarrier d.Q2 ×ˢ factorCarrier d.Q3)

/-- A complete factor label together with the original beta integer. -/
def MediumAtom.complexRowLabels (d : MediumAtom) : Finset ((ℕ × ℕ × ℕ) × ℕ) :=
  d.complexFactorLabels ×ˢ d.betaCarrier

/-- The literal arithmetic kernel of `MediumAtom.discrepancy`.
Finite identities also permit modulus zero under total division; actual
admissible carrier applications already have positive physical moduli. -/
def complexPrimitiveKernel (a : ℤ) (q n m : ℕ) : ℂ :=
  (if (((n * m : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ)) then 1 else 0) -
    (if (n * m).Coprime q then 1 else 0) / (Nat.totient q : ℂ)

def MediumAtom.complexRowContribution (d : MediumAtom) (n : ℕ)
    (l : (ℕ × ℕ × ℕ) × ℕ) : ℂ :=
  d.complexFactorGamma l.1 * d.beta l.2 *
    complexPrimitiveKernel d.residue (complexFactorModulus l.1) n l.2

/-- The full progression row before its primitive centre is subtracted. -/
def MediumAtom.complexProgressionRow (d : MediumAtom) (n : ℕ) : ℂ :=
  ∑ l ∈ d.complexRowLabels, d.complexFactorGamma l.1 * d.beta l.2 *
    (if (((n * l.2 : ℕ) : ℤ) % (complexFactorModulus l.1 : ℤ) =
      d.residue % (complexFactorModulus l.1 : ℤ)) then 1 else 0)

/-- The full primitive-coprime centre on the same labels and modulus. -/
def MediumAtom.complexPrincipalRow (d : MediumAtom) (n : ℕ) : ℂ :=
  ∑ l ∈ d.complexRowLabels,
    d.complexFactorGamma l.1 * d.beta l.2 *
      (if (n * l.2).Coprime (complexFactorModulus l.1) then 1 else 0) /
        (Nat.totient (complexFactorModulus l.1) : ℂ)

def MediumAtom.complexCenteredRow (d : MediumAtom) (n : ℕ) : ℂ :=
  d.complexProgressionRow n - d.complexPrincipalRow n

/-- The actual row is the sum of its labelled centered contributions. -/
theorem MediumAtom.complexCenteredRow_eq_sum (d : MediumAtom) (n : ℕ) :
    d.complexCenteredRow n =
      ∑ l ∈ d.complexRowLabels, d.complexRowContribution n l := by
  unfold MediumAtom.complexCenteredRow MediumAtom.complexProgressionRow
    MediumAtom.complexPrincipalRow
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold MediumAtom.complexRowContribution complexPrimitiveKernel
  ring

/-- Inactive gamma labels contribute zero without changing either carrier. -/
theorem MediumAtom.complexRowContribution_eq_zero_of_inactive
    (d : MediumAtom) (n : ℕ) (l : (ℕ × ℕ × ℕ) × ℕ)
    (h : d.gamma1 l.1.1 = 0 ∨ d.gamma2 l.1.2.1 = 0 ∨ d.gamma3 l.1.2.2 = 0) :
    d.complexRowContribution n l = 0 := by
  rcases h with h | h | h <;>
    simp only [MediumAtom.complexRowContribution, MediumAtom.complexFactorGamma,
      h, zero_mul, mul_zero]

/-- Exact finite Fubini: the actual signedError is a linear combination
of the complete complex rows, before any norm or Cauchy inequality. -/
theorem MediumAtom.signedError_eq_complexCenteredRows (d : MediumAtom) :
    d.signedError =
      ∑ n ∈ d.alphaCarrier, d.alpha n * d.complexCenteredRow n := by
  have hsource : d.signedError =
      ∑ l ∈ d.complexRowLabels, ∑ n ∈ d.alphaCarrier,
        d.alpha n * d.complexRowContribution n l := by
    unfold MediumAtom.signedError MediumAtom.discrepancy
      MediumAtom.complexRowLabels MediumAtom.complexFactorLabels
      MediumAtom.complexRowContribution MediumAtom.complexFactorGamma
      complexPrimitiveKernel complexFactorModulus
    simp only [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q1 _
    apply Finset.sum_congr rfl
    intro q2 _
    apply Finset.sum_congr rfl
    intro q3 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsource, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [MediumAtom.complexCenteredRow_eq_sum, Finset.mul_sum]

/-- Squared Cauchy for literal complex finite sums. The complex weights
in the source remain unchanged; norms enter only this final inequality. -/
theorem complex_finset_cauchy_norm_sq {iota : Type*} (S : Finset iota)
    (f g : iota → ℂ) :
    ‖∑ i ∈ S, f i * g i‖ ^ 2 ≤
      (∑ i ∈ S, ‖f i‖ ^ 2) * ∑ i ∈ S, ‖g i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ S, f i * g i‖ ≤ ∑ i ∈ S, ‖f i‖ * ‖g i‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun i => f i * g i)
  have hsum : 0 ≤ ∑ i ∈ S, ‖f i‖ * ‖g i‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ (∑ i ∈ S, ‖f i‖ * ‖g i‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hsum).2 hnorm
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖f i‖) (fun i => ‖g i‖)

/-- Actual complex Cauchy with all modulus signs still inside the row. -/
theorem MediumAtom.signedError_norm_sq_le_complexRows (d : MediumAtom) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) *
        ∑ n ∈ d.alphaCarrier, ‖d.complexCenteredRow n‖ ^ 2 := by
  rw [MediumAtom.signedError_eq_complexCenteredRows]
  exact complex_finset_cauchy_norm_sq d.alphaCarrier d.alpha d.complexCenteredRow

/-- The one-bounded alpha gate gives its actual finite L2 budget. -/
theorem mediumAdmissible_alpha_norm_sq_sum_le_card
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) ≤ (d.alphaCarrier.card : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, halpha, _⟩ := hd
  calc
    _ ≤ ∑ _n ∈ d.alphaCarrier, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := halpha n hn
      simpa only [one_pow] using
        (sq_le_sq₀ (norm_nonneg (d.alpha n)) (by norm_num : (0 : ℝ) ≤ 1)).2 hn1
    _ = _ := by simp

theorem MediumAtom.signedError_norm_sq_le_card_mul_complexRows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤ (d.alphaCarrier.card : ℝ) *
      ∑ n ∈ d.alphaCarrier, ‖d.complexCenteredRow n‖ ^ 2 :=
  d.signedError_norm_sq_le_complexRows.trans
    (mul_le_mul_of_nonneg_right (mediumAdmissible_alpha_norm_sq_sum_le_card hd)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

def MediumAtom.complexDispersionW (d : MediumAtom) (S : Finset ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, w n * ‖d.complexProgressionRow n‖ ^ 2

def MediumAtom.complexDispersionV (d : MediumAtom) (S : Finset ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, w n *
    (d.complexProgressionRow n * star (d.complexPrincipalRow n)).re

def MediumAtom.complexDispersionU (d : MediumAtom) (S : Finset ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, w n * ‖d.complexPrincipalRow n‖ ^ 2

/-- The complex cross term uses its real part, with the primitive centre
retained. It is not the product of two real surrogate rows. -/
theorem MediumAtom.complex_dispersion_identity (d : MediumAtom)
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S, w n * ‖d.complexCenteredRow n‖ ^ 2) =
      d.complexDispersionW S w - 2 * d.complexDispersionV S w +
        d.complexDispersionU S w := by
  unfold MediumAtom.complexCenteredRow MediumAtom.complexDispersionW
    MediumAtom.complexDispersionV MediumAtom.complexDispersionU
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, starRingEnd_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem MediumAtom.complex_dispersion_nonneg (d : MediumAtom)
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) :
    0 ≤ d.complexDispersionW S w - 2 * d.complexDispersionV S w +
      d.complexDispersionU S w := by
  rw [← MediumAtom.complex_dispersion_identity]
  exact Finset.sum_nonneg (fun n hn => mul_nonneg (hw n hn) (sq_nonneg _))

/-- The exact complex counterpart of the pinned real dispersion bound. -/
theorem MediumAtom.signedError_norm_sq_le_complexDispersion (d : MediumAtom) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) *
        (d.complexDispersionW d.alphaCarrier (fun _ => 1) -
          2 * d.complexDispersionV d.alphaCarrier (fun _ => 1) +
            d.complexDispersionU d.alphaCarrier (fun _ => 1)) := by
  rw [← MediumAtom.complex_dispersion_identity]
  simpa only [one_mul] using d.signedError_norm_sq_le_complexRows

/-- A nonnegative common smoothing weight enlarges the n carrier only
after Cauchy; the modulus and beta carriers are unchanged. -/
theorem MediumAtom.signedError_norm_sq_le_smoothedComplexDispersion
    (d : MediumAtom) (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : d.alphaCarrier ⊆ S) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hmajor : ∀ n ∈ d.alphaCarrier, 1 ≤ w n) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) *
        (d.complexDispersionW S w - 2 * d.complexDispersionV S w +
          d.complexDispersionU S w) := by
  apply d.signedError_norm_sq_le_complexRows.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [← MediumAtom.complex_dispersion_identity]
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, w n * ‖d.complexCenteredRow n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hmajor n hn) (sq_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun n hn _ => mul_nonneg (hw n hn) (sq_nonneg _))

/-- Squaring a genuine complex finite sum produces two full labels and
complex conjugation, with no absolute value on an individual summand. -/
theorem complex_norm_sq_sum_eq_double_star {iota : Type*} (S : Finset iota)
    (f : iota → ℂ) :
    ((‖∑ i ∈ S, f i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, f i * star (f j) := by
  calc
    _ = (∑ i ∈ S, f i) * star (∑ i ∈ S, f i) := by
      rw [Complex.ofReal_pow]
      exact (Complex.mul_conj' _).symm
    _ = _ := by
      rw [star_sum]
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- This is the exact labelled pair that a future Poisson/CRT argument
must transform. Different complete moduli and beta integers are retained. -/
theorem MediumAtom.complexRow_norm_sq_eq_double_star (d : MediumAtom) (n : ℕ) :
    ((‖d.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
        d.complexRowContribution n l * star (d.complexRowContribution n l') := by
  rw [MediumAtom.complexCenteredRow_eq_sum]
  exact complex_norm_sq_sum_eq_double_star d.complexRowLabels (d.complexRowContribution n)

/-- The common smoothing sum is now inside two complete factor/beta
labels. This is an exact identity, so a future completion must use this
one S and w rather than choosing a new interval for each modulus pair. -/
theorem MediumAtom.smoothedComplexRows_eq_double_star (d : MediumAtom)
    (S : Finset ℕ) (w : ℕ → ℝ) :
    ((∑ n ∈ S, w n * ‖d.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels, ∑ n ∈ S,
        (w n : ℂ) * d.complexRowContribution n l *
          star (d.complexRowContribution n l') := by
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, MediumAtom.complexRow_norm_sq_eq_double_star,
    Finset.mul_sum, ← mul_assoc]
  calc
    _ = ∑ l ∈ d.complexRowLabels, ∑ n ∈ S, ∑ l' ∈ d.complexRowLabels,
        (w n : ℂ) * d.complexRowContribution n l *
          star (d.complexRowContribution n l') := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm

end

end ImbalancedChen.Part3
