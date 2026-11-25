import ImbalancedChen.P2OriginalEulerWordConjugacyCore
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The exact original Family declaration, moved without changing its fully
qualified name, fields or declaration bytes. The accepted original Euler
operators are imported from their existing owner. No alternate Family,
licence or target assumption is defined.

The old full owner must use the import/removal postimage archived in
20261125-p2-9-geometric-family when loaded with this core. Its heavy
consumer theorems are not imported or granted acceptance here. All
constructor, projection and other generated owned declarations still
require ordinary compilation, independent replay and the owned audit.
-/
namespace ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily

noncomputable section
open Classical
open scoped BigOperators ContDiff

-- The rank index is Fin (kStar+1), so one family contains all k <= kStar.
-- A single C_m and B_m work for EVERY rank and target at derivative order m.
-- Real support makes the integer extension an actual smooth geometric
-- function; it supplies no congruence, primality or modulus-dependent filter.
structure Family (kStar : ℕ) where
  aStar : ℝ
  aStar_pos : 0 < aStar
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  upper_pos : 0 < upper
  ambient : (T : ℕ) → (k : Fin (kStar+1)) →
    (Fin k.val → ℝ) → ℝ
  smooth : ∀ T k, ContDiff ℝ ∞ (ambient T k)
  support : ∀ T k v, ambient T k v ≠ 0 →
    (∀ i, lower * (T : ℝ)^aStar ≤ v i) ∧
      (∏ i, v i) ≤ upper * (T : ℝ)
  finitePrimeSupport : ∀ T k,
    Set.Finite {u : Fin k.val → ℕ |
      (∀ i, (u i).Prime) ∧ ambient T k (fun i => (u i : ℝ)) ≠ 0}
  mixedEuler : ∀ m : ℕ, ∃ C B : ℕ,
    0 < C ∧ ∀ (T : ℕ) (k : Fin (kStar+1))
      (w : List (Fin k.val)) (v : Fin k.val → ℝ),
      w.length ≤ m →
      |eulerWord w (ambient T k) v| ≤
        (C : ℝ) * (Real.log ((T : ℝ)+2))^B


end
end ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
