import ImbalancedChen.P4BLabelledOuterPPUpperAssembly
import ImbalancedChen.CompactLocalThreshold

/-!
# Compact extraction of the A = 3 constant and threshold

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The local hypothesis is a genuine neighborhood-uniform signed rank-two
prime-product estimate: one C and one threshold control every nearby family
member. Compactness extracts a finite subcover, sums its positive constants,
and maximizes its thresholds. Pointwise eventual estimates alone do not meet
this hypothesis, and continuity alone is not substituted for local uniformity.

The actual local estimates and their P3 licensing remain OPEN inputs. This
module proves no such estimate, no spectral theorem, and no upper-count bound.
At each parameter all occurrences of Q, rho, and the labelled weight use that
same parameter. The moving-parameter corollary changes all three together and
requires eventual membership in the one compact set.
-/

namespace ImbalancedChen.P4BCompactPrimeProductA3

noncomputable section
open Filter Topology Set
open scoped BigOperators
open Part3

/-- Local common constants and thresholds yield a common positive constant
and threshold over the compact set, even when the signed coefficient family
varies with the parameter. The labelled-prime cap remains exactly N. -/
theorem exists_uniform_A3_on_compact_of_local
    {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    (Q : X → ℕ → Finset ℕ) (rho : X → ℕ → ℕ → ℝ)
    (V : X → (N : ℕ) → (Fin 2 → Fin (N + 1)) → ℝ)
    (hlocal : ∀ x ∈ S, ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ,
      ∀ᶠ y in 𝓝[S] x, ∀ N : ℕ, n ≤ N → Even N →
        |primeProductSignedError 2 N N (Q y N) (rho y N) (V y N)| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ x ∈ S,
        |primeProductSignedError 2 N N (Q x N) (rho x N) (V x N)| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ) := by
  classical
  choose C hC n hn using fun x : S => hlocal x.val x.property
  let U := fun x : S => {y : X | ∀ N : ℕ, n x ≤ N → Even N →
    |primeProductSignedError 2 N N (Q y N) (rho y N) (V y N)| ≤
      C x * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ)}
  obtain ⟨t, ht⟩ := hS.elim_nhdsWithin_subcover'
    (fun x hx => U ⟨x, hx⟩) (fun x hx => hn ⟨x, hx⟩)
  have hsum : 0 ≤ ∑ x ∈ t, C x :=
    Finset.sum_nonneg (fun x _hx => (hC x).le)
  refine ⟨1 + ∑ x ∈ t, C x, by linarith only [hsum],
    max 2 (t.sup n), le_max_left _ _, ?_⟩
  intro N hN hEven x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hnN : n y ≤ N :=
    (Finset.le_sup (f := n) hy).trans ((le_max_right _ _).trans hN)
  have hCy : C y ≤ 1 + ∑ z ∈ t, C z := by
    have hle : C y ≤ ∑ z ∈ t, C z :=
      Finset.single_le_sum (fun z _hz => (hC z).le) hy
    linarith only [hle]
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := (Real.log_pos hNreal).le
  exact (hxy N hnN hEven).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCy (Nat.cast_nonneg N)) (pow_nonneg hlog 3))

/-- A parameter may depend arbitrarily on N once it eventually lies in the
compact family. Both the coefficient and source use that same parameter.
The positive tolerance is chosen after the common A = 3 constant exists. -/
theorem eventually_moving_signed_error_le_of_local_A3
    {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    (Q : X → ℕ → Finset ℕ) (rho : X → ℕ → ℕ → ℝ)
    (V : X → (N : ℕ) → (Fin 2 → Fin (N + 1)) → ℝ)
    (hlocal : ∀ x ∈ S, ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ,
      ∀ᶠ y in 𝓝[S] x, ∀ N : ℕ, n ≤ N → Even N →
        |primeProductSignedError 2 N N (Q y N) (rho y N) (V y N)| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ))
    (parameter : ℕ → X) (hparameter : ∀ᶠ N : ℕ in atTop, parameter N ∈ S)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |primeProductSignedError 2 N N (Q (parameter N) N)
        (rho (parameter N) N) (V (parameter N) N)| ≤
          tolerance * singularNormalization N := by
  obtain ⟨C, hC, N0, _hN0, hbound⟩ :=
    exists_uniform_A3_on_compact_of_local S hS Q rho V hlocal
  filter_upwards [hparameter, eventually_ge_atTop N0,
    eventually_logSaving_le_singularNormalization C hC.le 3 (by norm_num)
      tolerance htolerance] with N hmem hN hbudget
  intro hEven
  exact (hbound N hN hEven (parameter N) hmem).trans hbudget.2

end
end ImbalancedChen.P4BCompactPrimeProductA3
