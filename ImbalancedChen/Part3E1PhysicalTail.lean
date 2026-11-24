import ImbalancedChen.Part3E1SameCutoffProgression
import ImbalancedChen.Part3E1WholeTail

/-!
# Physical S2 and its common Fourier truncation

The finite physical source and its exact zero mode use the original two
primitive gates and the right totient on every tagged fibre.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset Filter GevreyCutoff
open scoped BigOperators FourierTransform SchwartzMap

/-- The physical single-congruence S2 sum at a fixed common divisor. -/
def physicalSameCutoffS2FixedD (Q R N : Finset ℕ) (d : ℕ) (a : ℤ) (V : ℝ)
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ primitive a Q, ∑ n ∈ N, ∑ s ∈ R, ∑ n' ∈ N, ∑ r ∈ R,
    physicalSameCutoffS2Fibre V a q d r s n n'
      ((qWeight q : ℂ) * lambdaTrim r * star (lambdaTrim s) * alpha n * star (alpha n'))

/-- The exact zero Fourier term at the same physical moduli. -/
def physicalSameCutoffS2ZeroFixedD (Q R N : Finset ℕ) (d : ℕ) (a : ℤ) (V : ℝ)
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ primitive a Q, ∑ n ∈ N, ∑ s ∈ R, ∑ n' ∈ N, ∑ r ∈ R,
    if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
      ((qWeight q : ℂ) * lambdaTrim r * star (lambdaTrim s) * alpha n * star (alpha n')) *
        sameCutoffS2ZeroMode V (q * d * r) / ((q * d * s).totient : ℂ)
    else 0

/-- Subtracting the physical zero term gives the complete nonzero series
summed over exactly the same finite carriers. -/
theorem physicalSameCutoffS2FixedD_sub_zero (Q R N : Finset ℕ) {d : ℕ} (a : ℤ) {V : ℝ}
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ)
    (hV : 0 < V) (hd : 0 < d) (hQ : ∀ q ∈ Q, 0 < q) (hR : ∀ r ∈ R, 0 < r) :
    physicalSameCutoffS2FixedD Q R N d a V qWeight lambdaTrim alpha -
        physicalSameCutoffS2ZeroFixedD Q R N d a V qWeight lambdaTrim alpha =
      sameCutoffFullS2FixedD Q R N d a V qWeight lambdaTrim alpha := by
  unfold physicalSameCutoffS2FixedD physicalSameCutoffS2ZeroFixedD sameCutoffFullS2FixedD
  simp only [← sum_sub_distrib]
  refine sum_congr rfl fun q hq => sum_congr rfl fun n _ =>
    sum_congr rfl fun s _ => sum_congr rfl fun n' _ => sum_congr rfl fun r hr => ?_
  have hm := Nat.mul_pos (Nat.mul_pos (hQ q (mem_filter.mp hq).1) hd) (hR r hr)
  rw [physicalSameCutoffS2Fibre_eq_zero_add_nonzero hV a q d r s n n' _ hm, add_sub_cancel_left]
  rfl

/-- The error in using the finite signed Fourier window for physical S2,
after subtracting the exact zero mode. -/
theorem physicalSameCutoffS2Block_sub_retained_le (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (Q N D : Finset ℕ) (R : ℕ → Finset ℕ) (H : ℕ → ℝ)
      (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℕ → ℂ)
      (alpha : ℕ → ℂ) (B : ℝ),
      0 < V → 0 ≤ B → (∀ q ∈ Q, 0 < q) →
      (∀ d ∈ D, 0 < d ∧ 0 ≤ H d ∧ ∀ r ∈ R d, 0 < r) →
      (∀ d ∈ D, ∀ q ∈ Q, ∀ r ∈ R d, Real.log X^5 ≤
        V / ((q * d * r : ℕ) : ℝ) * H d) →
      (∀ q ∈ Q, qWeight q ∈ Set.Icc 0 1) →
      (∀ d ∈ D, ∀ r ∈ R d, ‖lambdaTrim d r‖ ≤ B) → (∀ n ∈ N, ‖alpha n‖ ≤ 1) →
      ‖((∑ d ∈ D, physicalSameCutoffS2FixedD Q (R d) N d a V qWeight (lambdaTrim d) alpha) -
        ∑ d ∈ D, physicalSameCutoffS2ZeroFixedD Q (R d) N d a V qWeight (lambdaTrim d) alpha) -
        ∑ d ∈ D, retainedS2FixedD Q (R d) N ⌊H d⌋₊ d a V
          (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) qWeight (lambdaTrim d) alpha‖ ≤
        (B^2 * (8 * X ^ (-(K : ℝ))) * (Q.card : ℝ) * (N.card : ℝ)^2) *
          ∑ d ∈ D, ((R d).card : ℝ)^2 := by
  filter_upwards [sameCutoffFullS2Block_sub_retained_le K]
    with X hTail Q N D R H a V qWeight lambdaTrim alpha B hV hB hQ hD hmesh hW hLambda hAlpha
  have hphysical :
      (∑ d ∈ D, physicalSameCutoffS2FixedD Q (R d) N d a V qWeight (lambdaTrim d) alpha) -
        (∑ d ∈ D, physicalSameCutoffS2ZeroFixedD Q (R d) N d a V qWeight (lambdaTrim d) alpha) =
      ∑ d ∈ D, sameCutoffFullS2FixedD Q (R d) N d a V qWeight (lambdaTrim d) alpha := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun d hd => physicalSameCutoffS2FixedD_sub_zero Q (R d) N a
      qWeight (lambdaTrim d) alpha hV (hD d hd).1 hQ (hD d hd).2.2
  rw [hphysical]
  exact hTail Q N D R H a V qWeight lambdaTrim alpha B hV hB hQ hD hmesh hW hLambda hAlpha

end

end ImbalancedChen.Part3.E1Finite
