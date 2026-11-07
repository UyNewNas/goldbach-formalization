import ImbalancedChen.P5OriginalPresievedTargetTransport
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

True marked-quotient target binding for the entire actual presieved
coefficient. The original selected compiler supplies Z<=the smallest
marked prime. This DERIVES full-prefix coprimality with every actual prime
below Z, and therefore the full target transport. Physical D, Z, small
cutoff and beta level are held fixed; they are never recomputed at B*N.

This matches genuine presieved coefficients only, not old native sigma.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedMarkedBinding

noncomputable section
open P5U1011JointOverlap
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenJointNearCapCompiler
open OriginalPresievedTargetTransport

/-- Actual marked prime provenance plus its genuine prime ceiling derives
coprimality with the complete allowed prime product below z. Strictness is
in the carrier p<z; equality of z with a marked prime is allowed. -/
theorem actual_prefix_coprime_full_carrier {N enumeration : ℕ}
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E) {z : ℝ}
    (hz : z ≤ (slots t 3 : ℝ)) (hcap : z ≤ (enumeration : ℝ)) :
    (fullPrefix t).Coprime (actualSmallPrimeProduct N enumeration z) := by
  rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N enumeration z hcap]
  exact fullPrefix_coprime_lowered_sieve ht hz

/-- The actual all-sixteen near-cap compiler supplies the required prime
ceiling; no final coprimality or coefficient-equality premise occurs. -/
theorem compiled_prefix_coprime_full_carrier {n N enumeration : ℕ}
    (hN : 1 < N) {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta)
    {t : Four} (ht : t ∈ ordinaryTuples n N E)
    (hcap : Z n N eta t ≤ (enumeration : ℝ)) :
    (fullPrefix t).Coprime (actualSmallPrimeProduct N enumeration (Z n N eta t)) := by
  have hleg := compiled_legality hN heta ht
  have hz : Z n N eta t ≤ (slots t 3 : ℝ) := by
    simpa only [slots, Matrix.cons_val_three] using hleg.2.2.1
  exact actual_prefix_coprime_full_carrier (Finset.mem_filter.mp ht).1 hz hcap

/-- The same decreasing ordered rough alphabet is used by physical and
marked-quotient rows, with arbitrary covering enumerations. -/
theorem compiled_rough_alphabet_on_mark {n N commonCap rowCap : ℕ}
    (hN : 1 < N) {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta)
    {t : Four} (ht : t ∈ ordinaryTuples n N E) (w : ℝ)
    (hcommon : Z n N eta t ≤ (commonCap : ℝ))
    (hrow : Z n N eta t ≤ (rowCap : ℝ)) :
    roughPrimeUniverse (fullPrefix t * N) rowCap w (Z n N eta t) =
      roughPrimeUniverse N commonCap w (Z n N eta t) :=
  rough_universe_target_mul_cover
    (compiled_prefix_coprime_full_carrier hN heta ht hcommon) hcommon hrow

/-- Entire TRUE presieved row target match, preserving the policy built
at the original physical residual D(n,N,eta,t). The policy factory is
arbitrary; its argument D is identical on both sides. Beta level L and
small cutoff w are also identical, even though the deletion target changes. -/
theorem compiled_presieved_physical_levels_on_mark
    (retainAtPhysicalLevel : ℝ → List ℕ → Bool)
    {n N commonCap rowCap : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta)
    {t : Four} (ht : t ∈ ordinaryTuples n N E) (w L : ℝ)
    (hw : w ≤ Z n N eta t)
    (hcommon : Z n N eta t ≤ (commonCap : ℝ))
    (hrow : Z n N eta t ≤ (rowCap : ℝ)) :
    let z := Z n N eta t
    let physicalD := D n N eta t
    actualSmallRoughModuli (retainAtPhysicalLevel physicalD)
        (fullPrefix t * N) rowCap w z =
      actualSmallRoughModuli (retainAtPhysicalLevel physicalD) N commonCap w z ∧
    actualSmallRoughRho (retainAtPhysicalLevel physicalD)
        (fullPrefix t * N) rowCap w z L =
      actualSmallRoughRho (retainAtPhysicalLevel physicalD) N commonCap w z L := by
  dsimp only
  exact presieved_target_mul_cover (retainAtPhysicalLevel (D n N eta t)) L hw
    (compiled_prefix_coprime_full_carrier hN heta ht hcommon) hcommon hrow

/-- Original common beta cutoff and level, with the same physical
residual policy. This is an exact quotient-row engineering match and
asserts no equality with a preexisting native or physical sigma. -/
theorem original_common_presieved_levels_on_mark
    (retainAtPhysicalLevel : ℝ → List ℕ → Bool)
    {n N commonCap rowCap : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta)
    {t : Four} (ht : t ∈ ordinaryTuples n N E) (nu0 betaEta : ℝ)
    (hw : (N : ℝ) ^ (nu0 * betaEta ^ 2) ≤ Z n N eta t)
    (hcommon : Z n N eta t ≤ (commonCap : ℝ))
    (hrow : Z n N eta t ≤ (rowCap : ℝ)) :
    let w := (N : ℝ) ^ (nu0 * betaEta ^ 2)
    let L := (N : ℝ) ^ (nu0 * betaEta)
    let z := Z n N eta t
    let physicalD := D n N eta t
    actualSmallRoughModuli (retainAtPhysicalLevel physicalD)
        (fullPrefix t * N) rowCap w z =
      actualSmallRoughModuli (retainAtPhysicalLevel physicalD) N commonCap w z ∧
    actualSmallRoughRho (retainAtPhysicalLevel physicalD)
        (fullPrefix t * N) rowCap w z L =
      actualSmallRoughRho (retainAtPhysicalLevel physicalD) N commonCap w z L :=
  compiled_presieved_physical_levels_on_mark retainAtPhysicalLevel hN heta ht
    ((N : ℝ) ^ (nu0 * betaEta ^ 2)) ((N : ℝ) ^ (nu0 * betaEta)) hw hcommon hrow

end
end ImbalancedChen.P5Z.OriginalPresievedMarkedBinding
