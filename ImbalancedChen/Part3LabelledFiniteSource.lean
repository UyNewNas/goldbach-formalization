import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-! Uncompiled exact finite labelled-source extraction candidate. -/
namespace ImbalancedChen.Part3
noncomputable section
open scoped BigOperators
open Classical

/-- Labelled prime tuples, retaining repeated primes and their slot order. -/
def labelledPrimeTuples (k P : ℕ) : Finset (Fin k → Fin (P + 1)) :=
  Finset.univ.filter (fun t => ∀ i : Fin k, Nat.Prime (t i).val)

def labelledProduct {k P : ℕ} (t : Fin k → Fin (P + 1)) : ℕ :=
  ∏ i : Fin k, (t i).val

/-- The exact `eq:current-PP` error for a finite labelled source.  Geometric
licensing is not asserted for arbitrary `W`.  There is no additive-prime
filter hidden in its source; that filter is recovered by the physical sieve. -/
def primeProductSignedError (k P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    (∑ t ∈ labelledPrimeTuples k P, W t *
      ((if Nat.ModEq q (labelledProduct t) N then (1 : ℝ) else 0) -
        (if Nat.Coprime (labelledProduct t) q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ)))

end
end ImbalancedChen.Part3
