import ImbalancedChen.P3ActualU8CompiledDelta
import ImbalancedChen.ActualSmallRosser
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A quantitative physical-coefficient perturbation bound for the original U8
rank-three prime-product source. Unlike the preceding common-carrier L1 bound,
the right side is a ROUGH INTEGER-coefficient difference and the literal
small-Rosser weighted norm. This pays no causal compilation bound and does
not infer a small discrepancy from a small harmonic wall.

The sign switch at c=0 is charged explicitly: c*betaPlus for c>=0 and
c*betaMinus for c<0. The finite physical product is reindexed by the
already-proved UNIQUE small/rough decomposition, with exact source labels,
full physical moduli and primitive means unchanged.
-/

namespace ImbalancedChen.P3ActualU8RoughDeltaNorm

noncomputable section
open scoped BigOperators
open Classical

private theorem abs_mul_le_abs_mul
    (x beta k : ℝ) (hbeta : |beta| ≤ k) :
    |x * beta| ≤ |x| * k := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hbeta (abs_nonneg x)

/-- The SIGN-SENSITIVE attachment is Lipschitz in its rough coefficient.
This remains true when the two coefficients have opposite signs, precisely
because the two slopes both have absolute value at most k. -/
theorem signAttachedCoefficient_lipschitz
    (x y betaMinus betaPlus : ℝ) :
    |signAttachedCoefficient x betaMinus betaPlus -
       signAttachedCoefficient y betaMinus betaPlus| ≤
      max |betaMinus| |betaPlus| * |x - y| := by
  let k : ℝ := max |betaMinus| |betaPlus|
  have hm : |betaMinus| ≤ k := le_max_left _ _
  have hp : |betaPlus| ≤ k := le_max_right _ _
  unfold signAttachedCoefficient
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · simp only [if_pos hx, if_pos hy]
      rw [← sub_mul, abs_mul]
      calc
        |x - y| * |betaPlus| ≤ |x - y| * k :=
          mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = k * |x - y| := mul_comm _ _
    · have hyneg : y < 0 := lt_of_not_ge hy
      have hxy : y ≤ x := (le_of_lt hyneg).trans hx
      have hgap : |x| + |y| = |x - y| := by
        rw [abs_of_nonneg hx, abs_of_neg hyneg,
          abs_of_nonneg (sub_nonneg.mpr hxy)]
        ring
      simp only [if_pos hx, if_neg hy]
      calc
        |x * betaPlus - y * betaMinus| ≤
            |x * betaPlus| + |y * betaMinus| := abs_sub _ _
        _ ≤ |x| * k + |y| * k :=
            add_le_add (abs_mul_le_abs_mul x betaPlus k hp)
              (abs_mul_le_abs_mul y betaMinus k hm)
        _ = k * |x - y| := by rw [← hgap]; ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hxy : x < y := hxneg.trans_le hy
      have hgap : |x| + |y| = |x - y| := by
        rw [abs_of_neg hxneg, abs_of_nonneg hy,
          abs_of_neg (sub_neg.mpr hxy)]
        ring
      simp only [if_neg hx, if_pos hy]
      calc
        |x * betaMinus - y * betaPlus| ≤
            |x * betaMinus| + |y * betaPlus| := abs_sub _ _
        _ ≤ |x| * k + |y| * k :=
            add_le_add (abs_mul_le_abs_mul x betaMinus k hm)
              (abs_mul_le_abs_mul y betaPlus k hp)
        _ = k * |x - y| := by rw [← hgap]; ring
    · simp only [if_neg hx, if_neg hy]
      rw [← sub_mul, abs_mul]
      calc
        |x - y| * |betaMinus| ≤ |x - y| * k :=
          mul_le_mul_of_nonneg_left hm (abs_nonneg _)
        _ = k * |x - y| := mul_comm _ _

/-- The physical L1 coefficient difference is controlled by the actual
small/rough PAIR, without multiplying by the number of physical moduli.
The small factor uses the literal max of the two signed beta coefficients;
inactive small Rosser slots therefore contribute zero. -/
theorem physical_delta_l1_le_rough_delta
    (w : ℝ) (small rough : Finset ℕ)
    (hsmall : ∀ a ∈ small, SmallPrimeSupportedAt w a)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (c1 c0 betaMinus betaPlus : ℕ → ℝ) :
    (∑ q ∈ smallRoughModuli small rough,
      |smallRoughRho small rough c1 betaMinus betaPlus q -
        smallRoughRho small rough c0 betaMinus betaPlus q|) ≤
    (∑ a ∈ small, max |betaMinus a| |betaPlus a|) *
      (∑ b ∈ rough, |c1 b - c0 b|) := by
  classical
  calc
    _ = ∑ x ∈ smallRoughPairs small rough,
        |signAttachedCoefficient (c1 x.2) (betaMinus x.1) (betaPlus x.1) -
          signAttachedCoefficient (c0 x.2) (betaMinus x.1) (betaPlus x.1)| := by
      rw [sum_smallRoughModuli hsmall hrough]
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
      rw [smallRoughRho_mul hsmall hrough c1 betaMinus betaPlus ha hb,
        smallRoughRho_mul hsmall hrough c0 betaMinus betaPlus ha hb]
      rfl
    _ ≤ ∑ x ∈ smallRoughPairs small rough,
        max |betaMinus x.1| |betaPlus x.1| * |c1 x.2 - c0 x.2| := by
      apply Finset.sum_le_sum
      intro x hx
      exact signAttachedCoefficient_lipschitz
        (c1 x.2) (c0 x.2) (betaMinus x.1) (betaPlus x.1)
    _ = (∑ a ∈ small, max |betaMinus a| |betaPlus a|) *
          (∑ b ∈ rough, |c1 b - c0 b|) := by
      simp only [smallRoughPairs, Finset.sum_product]
      calc
        _ = ∑ a ∈ small,
              max |betaMinus a| |betaPlus a| *
                (∑ b ∈ rough, |c1 b - c0 b|) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_mul]

/-- Literal physical coefficient bound: the small factor comes from
actual Li-Liu Rosser upper/lower coefficients, not an invented beta.
No bound on the causal rough-coefficient difference is asserted. -/
theorem actual_small_rosser_physical_delta_l1
    (retainOdd : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (rough : Finset ℕ)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (compiled : ℕ → ℤ) :
    (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w) rough,
      |smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fun b => (compiled b : ℝ))
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L) q -
       smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L) q|) ≤
      (∑ a ∈ actualSmallRosserSupport N cap w,
        max |actualSmallRosserMinus N cap w L a|
          |actualSmallRosserPlus N cap w L a|) *
        (∑ b ∈ rough,
          |(compiled b : ℝ) - fixedRoughCoefficient retainOdd N cap w z b|) := by
  exact physical_delta_l1_le_rough_delta w
    (actualSmallRosserSupport N cap w) rough
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    hrough
    (fun b => (compiled b : ℝ))
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)

/-- Original U8 sharp-K labels, including p2=q, with exact coprime mean.
The compiled-minus-raw discrepancy is reduced to the ROUGH coefficient
difference and actual beta norm. It is not yet an arbitrary-log saving,
nor an identification of the final frozen causal physical rho_T. -/
theorem actual_u8_compiled_PP_delta_le_rough_delta
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (compiled : ℕ → ℤ) :
    let small := actualSmallRosserSupport N cap w
    let Q := smallRoughModuli small rough
    let rhoComp := smallRoughRho small rough
      (fun b => (compiled b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let rhoRaw := smallRoughRho small rough
      (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    |Part3.primeProductSignedError 3 N N Q rhoComp
        (P5U8SharpKSource.physicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rhoRaw
        (P5U8SharpKSource.physicalWeight N)| ≤
    ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
      ((∑ a ∈ small, max |actualSmallRosserMinus N cap w L a|
        |actualSmallRosserPlus N cap w L a|) *
      (∑ b ∈ rough, |(compiled b : ℝ) -
        fixedRoughCoefficient retainOdd N cap w z b|)) := by
  dsimp
  let small := actualSmallRosserSupport N cap w
  let Q := smallRoughModuli small rough
  let rhoComp := smallRoughRho small rough
    (fun b => (compiled b : ℝ))
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
  let rhoRaw := smallRoughRho small rough
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
  have hpos : ∀ q ∈ Q, 0 < q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
    exact Nat.mul_pos
      (Nat.pos_of_ne_zero
        (actualSmallRosserSupport_squarefree N cap w ha).ne_zero)
      (Nat.pos_of_ne_zero (hrough x.2 hb).1)
  have hlinear := P3ActualU8CompiledDelta.actual_u8_signed_PP_difference
    N Q rhoComp rhoRaw
  have hnorm := P3ActualU8UnitPhysicalNorm.labelled_unit_signed_error_le_l1
    (P5U8SharpKSource.arithmeticTriples N)
    P5U8SharpKSource.product N Q
    (fun q => rhoComp q - rhoRaw q) hpos
  have hphysical : (∑ q ∈ Q, |rhoComp q - rhoRaw q|) ≤
      (∑ a ∈ small, max |actualSmallRosserMinus N cap w L a|
        |actualSmallRosserPlus N cap w L a|) *
      (∑ b ∈ rough,
        |(compiled b : ℝ) - fixedRoughCoefficient retainOdd N cap w z b|) :=
    actual_small_rosser_physical_delta_l1
      retainOdd N cap w z L rough hrough compiled
  calc
    _ = |p5z_labelledDistributionError
          (P5U8SharpKSource.arithmeticTriples N)
          P5U8SharpKSource.product (fun _ => (1 : ℝ)) N Q
          (fun q => rhoComp q - rhoRaw q)| := by
        rw [hlinear]
        congr 1
        ring
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
          (∑ q ∈ Q, |rhoComp q - rhoRaw q|) := hnorm
    _ ≤ _ := mul_le_mul_of_nonneg_left hphysical (by positivity)

end
end ImbalancedChen.P3ActualU8RoughDeltaNorm
