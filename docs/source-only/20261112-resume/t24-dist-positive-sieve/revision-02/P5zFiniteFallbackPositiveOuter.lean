import ImbalancedChen.P5zLabelledIntegerShiftPositiveSieve
import ImbalancedChen.P4AOriginalFiniteFallbackCount

/-!
SOURCE ONLY / YELLOW / UNCOMPILED.
The original finite fallback policy and its original beta attachment are
used verbatim. Tuple cap P is independent of additive-prime target N.
There is no product <= N restriction and no PP estimate is asserted.
-/
namespace ImbalancedChen.P5zFiniteFallbackPositiveOuter

noncomputable section
open scoped BigOperators
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)

/-- The original all-natural upper majorant enters at the same target N,
with precisely the original B,r,n,e,q,a,omega,tau,L and modulus carrier. -/
theorem primeMass_le {α : Type*}
    (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hz : cutoff N ≤ (N : ℝ))
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (hW : ∀ t ∈ S, 0 ≤ W t) :
    let Q := moduli N ((N : ℝ) ^ omega)
    let R := rho B r n e q a omega N tau L
    p5z_labelledPrimeMass S f W N ≤
      p5z_labelledMass S W * physicalDensitySum Q R +
        p5z_labelledCoprimeCorrection S f W Q R +
        p5z_labelledDistributionError S f W N Q R +
        p5z_labelledSmallPrimeMass S f W N (Nat.ceil (cutoff N)) := by
  exact P5zLabelledIntegerShiftPositiveSieve.primeMass_le_main_add_errors
    S f W N (Nat.ceil (cutoff N)) (moduli N ((N : ℝ) ^ omega))
    (rho B r n e q a omega N tau L) hW
    (P4AOriginalFiniteFallbackCount.upper_majorant B r n e q a omega N tau L
      hL hwL hwz hz)

/-- Full actual tuple carrier, including every outer point above N.
In particular P=2*N is permitted with the additive target still N.
The old exact Part3 PP equality is reused with both parameters visible. -/
theorem fullPrimeTupleMass_le
    (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hz : cutoff N ≤ (N : ℝ))
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ)
    (hW : ∀ t ∈ Part3.labelledPrimeTuples k P, 0 ≤ W t) :
    let S := Part3.labelledPrimeTuples k P
    let Q := moduli N ((N : ℝ) ^ omega)
    let R := rho B r n e q a omega N tau L
    p5z_labelledPrimeMass S Part3.labelledProduct W N ≤
      p5z_labelledMass S W * physicalDensitySum Q R +
        p5z_labelledCoprimeCorrection S Part3.labelledProduct W Q R +
        Part3.primeProductSignedError k P N Q R W +
        p5z_labelledSmallPrimeMass S Part3.labelledProduct W N (Nat.ceil (cutoff N)) := by
  have h := primeMass_le B r n e q a omega N tau L hL hwL hwz hz
    (Part3.labelledPrimeTuples k P) Part3.labelledProduct W hW
  dsimp only at h ⊢
  rw [p5z_labelledDistributionError_eq_primeProductSignedError] at h
  exact h

end
end ImbalancedChen.P5zFiniteFallbackPositiveOuter
