import ImbalancedChen.Part3OriginalRegularThreeMeasures
import ImbalancedChen.Part3RegularCumulativeShellPayment
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! The holomorphic summand of the printed regular norm, on the
orthonormal Petersson bases and the two slash-action frames used by the
native cumulative estimate. -/

noncomputable section
namespace ImbalancedChen.Part3.PrintedHolomorphicRegularNorm20261123

open Finset
open scoped BigOperators MatrixGroups UpperHalfPlane InnerProductSpace
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicPeterssonSpace20261112 (Forms BasisIndex)
open OriginalHolomorphicCuspFrames20261110 (sieveCoeff sieveCoeff_eq_scaled_R)
open ActualContinuousPoincarePairing20261110 (originalFrame)
open OriginalRegularPacketTest20261113 (Dyadic energy)
open OriginalRegularHolomorphicWeight20261113 (order)
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis functional shell weights mem_weights)
open OriginalRegularThreeMeasures20261113 (manuscript_regular_three)
open RegularCumulativeShellPayment20261102 (heightCut)

/-- For weight k = 2j+2, sieveCoeff is n^(-(k-1)/2) times the actual
q-expansion coefficient of the form slashed by the observing matrix. -/
def printedCoeff (q j : ℕ) [NeZero q] (one : Bool) (f : Forms q (j+1)) (n : ℕ) : ℂ :=
  (Real.sqrt (((2*j+1).factorial : ℝ)/(4*Real.pi)^(2*j+1)) : ℂ) *
    sieveCoeff q (NeZero.pos q) (j+1) f (originalFrame one) n

private def scale (j : ℕ) : ℝ :=
  Real.sqrt (((2*j+1).factorial : ℝ)/(4*Real.pi)^(2*j+1)) * (4*Real.pi)^(j+1)

private theorem scale_sq (j : ℕ) :
    (scale j)^2 = (4*Real.pi)*Real.Gamma (2*(j : ℝ)+2) := by
  let u : ℝ := 4*Real.pi
  have hu : 0 < u := mul_pos (by norm_num) Real.pi_pos
  have hden : 0 < u^(2*j+1) := pow_pos hu _
  have hfac : 0 ≤ (((2*j+1).factorial : ℝ)/u^(2*j+1)) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hg : Real.Gamma (2*(j : ℝ)+2) = ((2*j+1).factorial : ℝ) := by
    rw [show 2*(j : ℝ)+2 = ((2*j+1 : ℕ) : ℝ)+1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial (2*j+1)
  have hpow : (u^(j+1))^2 = u^(2*j+1)*u := by
    calc
      (u^(j+1))^2 = u^((j+1)*2) := (pow_mul u _ _).symm
      _ = u^((2*j+1)+1) := congrArg (fun n : ℕ => u^n) (by omega)
      _ = u^(2*j+1)*u := pow_succ u _
  change (Real.sqrt _ * u^(j+1))^2 = u*_
  rw [mul_pow, Real.sq_sqrt hfac, hpow, hg]
  field_simp [hden.ne'] <;> ring

private theorem finite_row (q j : ℕ) [NeZero q] (one : Bool)
    (S : Finset ℕ) (a : ℕ → ℂ) (hpos : ∀ n ∈ S, 0 < n) (f : Forms q (j+1)) :
    (∑ n ∈ S, a n * printedCoeff q j one f n) =
      (scale j : ℂ) * functional q j one S a f := by
  rw [functional, mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [printedCoeff, sieveCoeff_eq_scaled_R q (NeZero.pos q) (j+1) f (originalFrame one) (hpos n hn)]
  simp only [scale, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- With the manuscript measure 1/(2π) the printed weight-k quadratic
form is exactly twice the native Γ(k)-weighted form. -/
theorem printed_shell_eq (q j : ℕ) [NeZero q] (one : Bool) (S : Finset ℕ)
    (a : ℕ → ℂ) (hpos : ∀ n ∈ S, 0 < n) (basis : WeightBasis q j) :
    (1/(2*Real.pi)) *
        (∑ i, ‖∑ n ∈ S, a n * printedCoeff q j one (basis i) n‖^2) =
      2 * shell q j one S a basis := by
  calc
    _ = (1/(2*Real.pi)) *
        ((scale j)^2 * ∑ i, ‖functional q j one S a (basis i)‖^2) := by
      apply congrArg (fun x : ℝ => (1/(2*Real.pi))*x)
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [finite_row q j one S a hpos, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = _ := by
      rw [scale_sq, shell]
      field_simp [Real.pi_ne_zero] <;> ring

/-- The full positive block includes every ONB vector at every even
weight satisfying k-1 ≤ T. -/
theorem printed_cumulative_eq (q : ℕ) [NeZero q] (one : Bool) (T : ℝ)
    (S : Finset ℕ) (a : ℕ → ℂ) (hpos : ∀ n ∈ S, 0 < n)
    (bases : ∀ j, WeightBasis q j) :
    (1/(2*Real.pi)) * (∑ j ∈ weights T,
      ∑ i, ‖∑ n ∈ S, a n * printedCoeff q j one (bases j i) n‖^2) =
    2 * ∑ j ∈ weights T, shell q j one S a (bases j) := by
  calc
    _ = ∑ j ∈ weights T, (1/(2*Real.pi)) *
        (∑ i, ‖∑ n ∈ S, a n * printedCoeff q j one (bases j i) n‖^2) := by rw [mul_sum]
    _ = ∑ j ∈ weights T, 2 * shell q j one S a (bases j) :=
      sum_congr rfl (fun j _ => printed_shell_eq q j one S a hpos (bases j))
    _ = _ := by symm; rw [mul_sum]

abbrev Atom (q : ℕ) [NeZero q] := Σ j : ℕ, BasisIndex q (j+1)

def atomHeight (q : ℕ) [NeZero q] (p : Atom q) : ℝ := order p.1

/-- Each of the two linear functionals carries the square root of the
same positive spectral weight. -/
def measuredRow (q : ℕ) [NeZero q] (one : Bool) (S : Finset ℕ) (a : ℕ → ℂ)
    (bases : ∀ j, WeightBasis q j) (p : Atom q) : ℂ :=
  (Real.sqrt (1/(2*Real.pi)) : ℂ) *
    ∑ n ∈ S, a n * printedCoeff q p.1 one (bases p.1 p.2) n

private theorem measured_sq (q : ℕ) [NeZero q] (one : Bool) (S : Finset ℕ) (a : ℕ → ℂ)
    (bases : ∀ j, WeightBasis q j) (p : Atom q) :
    ‖measuredRow q one S a bases p‖^2 =
      (1/(2*Real.pi)) * ‖∑ n ∈ S, a n * printedCoeff q p.1 one (bases p.1 p.2) n‖^2 := by
  have hμ : 0 ≤ 1/(2*Real.pi) := by positivity
  rw [measuredRow, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hμ]

/-- A constant fixed before the level, cusp, Fourier row, ONBs and
spectral truncation supplies the cumulative premise of the shell consumer. -/
theorem finite_cumulative (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (one : Bool) {T L : ℝ},
    1 ≤ T → 1/2 ≤ L → ∀ (S : Finset ℕ) (a : ℕ → ℂ), Dyadic L S →
    ∀ (bases : ∀ j, WeightBasis q j) (F : Finset (Atom q)),
      (∑ p ∈ heightCut F (atomHeight q) T, ‖measuredRow q one S a bases p‖^2) ≤
        (T^2+L^(1+ε)/(q : ℝ)) * (C * energy S a) := by
  obtain ⟨D, hD, sieve⟩ := manuscript_regular_three ε hε
  refine ⟨2*D, mul_pos (by norm_num) hD, ?_⟩
  intro q inst one T L hT hL S a hband bases F
  classical
  have hpos (n : ℕ) (hn : n ∈ S) : 0 < n := by
    have hnR : (0 : ℝ) < n := lt_trans (by linarith only [hL]) (hband n hn).1
    exact_mod_cast hnR
  let full := (weights T).sigma (fun j => (univ : Finset (BasisIndex q (j+1))))
  have hsub : heightCut F (atomHeight q) T ⊆ full := by
    intro p hp
    have hb : |atomHeight q p| ≤ T := (mem_filter.mp hp).2
    exact mem_sigma.mpr ⟨mem_weights.mpr ((le_abs_self (atomHeight q p)).trans hb), mem_univ _⟩
  have hbudget := (sieve q one false hT hL S a hband).2.2.2.2 bases
  calc
    _ ≤ ∑ p ∈ full, ‖measuredRow q one S a bases p‖^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = (1/(2*Real.pi)) * (∑ j ∈ weights T,
          ∑ i, ‖∑ n ∈ S, a n * printedCoeff q j one (bases j i) n‖^2) := by
      rw [show full = (weights T).sigma (fun j => (univ : Finset (BasisIndex q (j+1)))) from rfl,
        sum_sigma]
      simp only [measured_sq, mul_sum]
    _ = 2 * ∑ j ∈ weights T, shell q j one S a (bases j) :=
      printed_cumulative_eq q one T S a hpos bases
    _ ≤ 2 * (D * (T^2+L^(1+ε)/(q : ℝ)) * energy S a) :=
      mul_le_mul_of_nonneg_left hbudget (by norm_num)
    _ = _ := by ring

end ImbalancedChen.Part3.PrintedHolomorphicRegularNorm20261123
end
