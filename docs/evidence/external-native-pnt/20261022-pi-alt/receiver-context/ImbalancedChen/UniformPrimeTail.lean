import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform prime-counting tails conditional on the upstream real PNT

This mathlib-only module proves elementary transfers from the exact real-endpoint
PNT statement exported by the external upstream theorem
`primeCounting_asymptotic_real`. That theorem is not imported or proved here.
Its existential error-function statement is an explicit premise of every
prime-counting estimate below. No estimate for half-product mass is assumed.

The first transfer chooses one threshold for every real `x >= sqrt N`
simultaneously, including `x >= 2` and positivity of its logarithm. In particular,
this is stronger than a statement about a single chosen sequence of arguments.
The second transfer gives the literal fixed-power prime-prefix bound needed for
the small rectangle and order-error terms in the half-product mass calculation.
The exponent is fixed before the eventual threshold is chosen.

All endpoint floors are natural floors, and `Nat.primeCounting` includes its
integer endpoint. There are no exceptional parity restrictions on `N`.
-/

namespace ImbalancedChen

open Filter Asymptotics

section RealPNTTransfer

/- The exact upstream real PNT contract remains an explicit input. This
section proves its uniform consequences, not the prime number theorem. -/
variable (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
  ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
    (1 + c x) * x / Real.log x)

include hPNT

/-- One real threshold works for the entire tail, with positive logarithms.
The threshold depends only on the supplied PNT witness and `epsilon`. -/
theorem exists_primeCounting_real_relative_error_threshold_of_real_pnt
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      0 < Real.log x ∧
      |(Nat.primeCounting (Nat.floor x) : ℝ) - x / Real.log x| ≤
        epsilon * (x / Real.log x) := by
  obtain ⟨c, hc, hcount⟩ := hPNT
  have hsmall : ∀ᶠ x : ℝ in atTop, |c x| ≤ epsilon := by
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using hc.bound hepsilon
  obtain ⟨X, hX⟩ := eventually_atTop.mp hsmall
  refine ⟨max X 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (le_max_right X 2).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hmain : 0 ≤ x / Real.log x := div_nonneg hx0 hlog.le
  refine ⟨hlog, ?_⟩
  calc
    |(Nat.primeCounting (Nat.floor x) : ℝ) - x / Real.log x| =
        |c x| * (x / Real.log x) := by
      rw [hcount x]
      have heq : (1 + c x) * x / Real.log x - x / Real.log x =
          c x * (x / Real.log x) := by ring
      rw [heq, abs_mul, abs_of_nonneg hmain]
    _ ≤ epsilon * (x / Real.log x) :=
      mul_le_mul_of_nonneg_right (hX x ((le_max_left X 2).trans hx)) hmain

/-- Uniformity over all real endpoints above the square-root cutoff, using
one eventual condition on the natural center. Positivity is included in the
same eventual statement as the error estimate. -/
theorem eventually_primeCounting_uniform_sqrt_tail_of_real_pnt
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, Real.sqrt (N : ℝ) ≤ x →
      2 ≤ x ∧ 0 < Real.log x ∧
      |(Nat.primeCounting (Nat.floor x) : ℝ) - x / Real.log x| ≤
        epsilon * (x / Real.log x) := by
  obtain ⟨X, hX2, hX⟩ :=
    exists_primeCounting_real_relative_error_threshold_of_real_pnt
      hPNT epsilon hepsilon
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually (eventually_ge_atTop X)] with N hN
  intro x hx
  have hXx : X ≤ x := hN.trans hx
  exact ⟨hX2.trans hXx, hX x hXx⟩

/-- Explicit common-threshold version: `N0` is chosen before both `N` and
`x`, so no summand-dependent threshold is hidden in the uniform estimate. -/
theorem exists_primeCounting_uniform_sqrt_tail_threshold_of_real_pnt
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ x : ℝ, Real.sqrt (N : ℝ) ≤ x →
        2 ≤ x ∧ 0 < Real.log x ∧
        |(Nat.primeCounting (Nat.floor x) : ℝ) - x / Real.log x| ≤
          epsilon * (x / Real.log x) := by
  exact eventually_atTop.mp
    (eventually_primeCounting_uniform_sqrt_tail_of_real_pnt hPNT epsilon hepsilon)

/-- The literal relative-error adapter without the auxiliary sign facts. -/
theorem eventually_primeCounting_real_relative_error_of_real_pnt
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, Real.sqrt (N : ℝ) ≤ x →
      |(Nat.primeCounting (Nat.floor x) : ℝ) - x / Real.log x| ≤
        epsilon * (x / Real.log x) := by
  filter_upwards
    [eventually_primeCounting_uniform_sqrt_tail_of_real_pnt hPNT epsilon hepsilon]
    with N hN
  intro x hx
  exact (hN x hx).2.2

/-- For each fixed positive real exponent, the actual prime prefix at
`floor (N^gamma)` is eventually at most `(2/gamma) * N^gamma/log N`.
The exponent need not be at least one half. -/
theorem eventually_primeCounting_rpow_le_of_real_pnt
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ gamma)) : ℝ) ≤
        (2 / gamma) * (N : ℝ) ^ gamma / Real.log (N : ℝ) := by
  obtain ⟨X, _hX2, hX⟩ :=
    exists_primeCounting_real_relative_error_threshold_of_real_pnt
      hPNT 1 zero_lt_one
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ gamma) atTop atTop :=
    (tendsto_rpow_atTop hgamma).comp tendsto_natCast_atTop_atTop
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually (eventually_ge_atTop X),
    hnat.eventually (eventually_gt_atTop (1 : ℝ))] with N hNX hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN
  have herror := (hX ((N : ℝ) ^ gamma) hNX).2
  have hupper :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ gamma)) : ℝ) ≤
        2 * ((N : ℝ) ^ gamma / Real.log ((N : ℝ) ^ gamma)) := by
    have hle := (le_abs_self
      ((Nat.primeCounting (Nat.floor ((N : ℝ) ^ gamma)) : ℝ) -
        (N : ℝ) ^ gamma / Real.log ((N : ℝ) ^ gamma))).trans herror
    linarith
  calc
    (Nat.primeCounting (Nat.floor ((N : ℝ) ^ gamma)) : ℝ) ≤
        2 * ((N : ℝ) ^ gamma / Real.log ((N : ℝ) ^ gamma)) := hupper
    _ = (2 / gamma) * (N : ℝ) ^ gamma / Real.log (N : ℝ) := by
      rw [Real.log_rpow hNpos]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end RealPNTTransfer

end ImbalancedChen
