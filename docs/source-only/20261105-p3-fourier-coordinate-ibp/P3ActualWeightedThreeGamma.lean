import ImbalancedChen.P3ActualWeightedFineSameRho
import ImbalancedChen.P3ActualSortedFineSourceGamma

/-!
P3.6 / exact weighted sorted source -> actual frozen three-gamma tensor.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The original geometric W is a function of the labelled prime tuple, not
just of its full integer product. Its EXACT sorted product fibre is therefore
inserted as an arithmetic function after the sorted source has been formed.
Only then may the existing original fine-label scalar identity and literal
three frozen gamma sums be used. This is an exact finite transport, retaining
the same physical q and rho(q) in both the congruence and coprime-mean terms.

IMPORTANT: the fibre function is NOT a Fourier-separated slot multiplier
and is NOT one-bounded merely because the original gamma_i are one-bounded.
This result does not give an admissible medium source or a modulus bound.
-/ 

namespace ImbalancedChen.P3ActualWeightedThreeGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualSortedFineSourceGamma
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- One literal physical modulus, with the original exact coprime mean:
transport the true tuple-dependent weight via the sorted product fibre,
then apply the real weak-word run-length and frozen three-gamma identity.
No invariance under equal-label slot permutations is postulated. -/
theorem weighted_sorted_three_gamma_one_modulus
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (q T r : ℕ) (c : ℝ) (W : List ℕ → ℝ) :
    let input := p 0 :: p 1 :: p 2 :: tail
    let blocks := actualPrimeFineLabelBlocksOfWord input
    let B := actualPrimeFineLabelFinset N τ
    let size := actualFrozenSplitSize D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    (∑ n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod,
        (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
          weightedFineFibre N τ blocks W n) * fineKernel T q n) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
      (actualPrimeFineWordMultiplicity input : ℝ))) *
    (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
      ∑ d ∈ T₂.image List.prod,
        gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
        ((ArithmeticFunction.moebius (r * (a * b * d)) : ℝ) *
          (weightedFineFibre N τ blocks W (a * b * d) *
            fineKernel T q (a * b * d)))) := by
  let input : List ℕ := p 0 :: p 1 :: p 2 :: tail
  let blocks : List (ℕ × ℕ) := actualPrimeFineLabelBlocksOfWord input
  let H : ℕ → ℝ := fun n =>
    weightedFineFibre N τ blocks W n * fineKernel T q n
  have hsource := actual_sorted_fine_source_gamma N hN τ hτ
    D A yz upper p tail horder r c H
  have hleft :
      (∑ n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod,
          (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
            weightedFineFibre N τ blocks W n) * fineKernel T q n) =
        c * (∑ n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod,
          (ArithmeticFunction.moebius (r * n) : ℝ) * H n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [H]
    ring
  calc
    _ = c * (∑ n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod,
          (ArithmeticFunction.moebius (r * n) : ℝ) * H n) := hleft
    _ = _ := by
      simpa only [H, input, blocks, actualPrimeFineLabelSortedTuples] using hsource

/-- The literal SAME integer rho on the complete physical modulus family
is carried through the true arbitrary-labelled-W fibre and the original
three-gamma scalar normalization. Both sides use fineKernel(T,q,n), hence
the identical congruence-minus-exact-coprime-mean kernel, and no
independent mean coefficient is introduced. -/
theorem weighted_sorted_three_gamma_same_rho
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (T r : ℕ) (c : ℝ) (W : List ℕ → ℝ) :
    let input := p 0 :: p 1 :: p 2 :: tail
    let blocks := actualPrimeFineLabelBlocksOfWord input
    let B := actualPrimeFineLabelFinset N τ
    let size := actualFrozenSplitSize D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    weightedSortedPP N τ blocks Q rho T r c W =
      ∑ q ∈ Q, rho q *
        ((c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
          (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
          (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
          (actualPrimeFineWordMultiplicity input : ℝ))) *
        (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
          ∑ d ∈ T₂.image List.prod,
            gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
            ((ArithmeticFunction.moebius (r * (a * b * d)) : ℝ) *
              (weightedFineFibre N τ blocks W (a * b * d) *
                fineKernel T q (a * b * d))))) := by
  let input : List ℕ := p 0 :: p 1 :: p 2 :: tail
  let blocks : List (ℕ × ℕ) := actualPrimeFineLabelBlocksOfWord input
  calc
    weightedSortedPP N τ blocks Q rho T r c W =
        ∑ q ∈ Q, rho q *
          ∑ n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod,
            (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
              weightedFineFibre N τ blocks W n) * fineKernel T q n :=
      weightedSortedPP_fibre N τ blocks Q rho T r c W
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrArg (fun z : ℝ => rho q * z)
        (weighted_sorted_three_gamma_one_modulus N hN τ hτ
          D A yz upper p tail horder q T r c W)

end
end ImbalancedChen.P3ActualWeightedThreeGamma
