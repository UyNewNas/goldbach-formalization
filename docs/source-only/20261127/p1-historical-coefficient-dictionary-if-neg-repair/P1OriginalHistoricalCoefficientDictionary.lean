import ImbalancedChen.P1Full87TrueDUnitBound
import ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData
import Mathlib.Data.Complex.Basic

/-!
# The actual historical policy difference on its small/rough factors

SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The two policies use the same physical N, cap, w, z and L. At an occupied
small/rough product a*b, their difference is the difference of the two
retention masks times ONE attached Mobius coefficient. The small Rosser
member is selected by the sign of Mobius(b), before multiplying by the
policy-mask difference. In particular, deleting a retained rough modulus
does not exchange the small plus and minus coefficients.

The complex test identity and its remainingModuli specialization keep the
complete product a*b in the original filter. They do not replace the
original physical supports by products/free/wholeHigh, drop squarefree
collisions, supply whole-atom factorization gates, or bound a medium sum.
-/

namespace ImbalancedChen.P1OriginalHistoricalCoefficientDictionary

noncomputable section

open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- A covering rough support formed from the two original policy supports. -/
def commonRoughSupport (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  fixedRoughSupport fresh N cap w z ∪ fixedRoughSupport old N cap w z

/-- Only the retention decision changes between the two policies. -/
def roughMaskDelta (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (b : ℕ) : ℝ :=
  (if b ∈ fixedRoughSupport fresh N cap w z then 1 else 0) -
    (if b ∈ fixedRoughSupport old N cap w z then 1 else 0)

/-- The small Rosser member is selected by the original rough Mobius sign. -/
def attachedMobius (N cap : ℕ) (w L : ℝ) (a b : ℕ) : ℝ :=
  signAttachedCoefficient (ArithmeticFunction.moebius b : ℝ)
    (actualSmallRosserMinus N cap w L a) (actualSmallRosserPlus N cap w L a)

private theorem commonRoughSupport_rough
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {b : ℕ} (hb : b ∈ commonRoughSupport old fresh N cap w z) :
    RoughPrimeSupportedAt w b := by
  rcases Finset.mem_union.mp hb with hf | ho
  · exact fixedRoughSupport_roughPrimeSupportedAt fresh N cap w z hf
  · exact fixedRoughSupport_roughPrimeSupportedAt old N cap w z ho

/-- The common carrier has exactly the original union of physical supports.
It adds no physical modulus and uses the same strict small/rough cutoff. -/
theorem trueDDeltaSupport_eq_smallRoughModuli
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    trueDDeltaSupport old fresh N cap w z =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (commonRoughSupport old fresh N cap w z) := by
  simp only [trueDDeltaSupport, actualSmallRoughModuli, commonRoughSupport,
    smallRoughModuli, smallRoughPairs, Finset.product_union, Finset.image_union]

/-- The zero extensions in trueDDeltaRho are already enforced by each
actual physical coefficient. This retains the original fresh-minus-old order. -/
theorem trueDDeltaRho_eq_actual_difference
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ) :
    trueDDeltaRho old fresh N cap w z L d =
      actualSmallRoughRho fresh N cap w z L d -
        actualSmallRoughRho old N cap w z L d := by
  have hzero (retainOdd : List ℕ → Bool) :
      (if d ∈ actualSmallRoughModuli retainOdd N cap w z then
        actualSmallRoughRho retainOdd N cap w z L d else 0) =
        actualSmallRoughRho retainOdd N cap w z L d := by
    by_cases hd : d ∈ actualSmallRoughModuli retainOdd N cap w z
    · simp only [if_pos hd]
    · have hz : actualSmallRoughRho retainOdd N cap w z L d = 0 :=
        smallRoughRho_eq_zero_of_not_mem
          (actualSmallRosserSupport N cap w) (fixedRoughSupport retainOdd N cap w z)
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) hd
      simp only [if_neg hd, hz]
  simp only [trueDDeltaRho, hzero fresh, hzero old]

/-- The exact historical coefficient at its unique physical small/rough
factorization. The policy mask stays OUTSIDE the original sign attachment. -/
theorem trueDDeltaRho_mul
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {a b : ℕ} (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ commonRoughSupport old fresh N cap w z) :
    trueDDeltaRho old fresh N cap w z L (a * b) =
      roughMaskDelta old fresh N cap w z b * attachedMobius N cap w L a b := by
  have hs : ∀ a ∈ actualSmallRosserSupport N cap w, SmallPrimeSupportedAt w a :=
    fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hr : ∀ b ∈ commonRoughSupport old fresh N cap w z, RoughPrimeSupportedAt w b :=
    fun b hb => commonRoughSupport_rough old fresh N cap w z hb
  have hf : fixedRoughSupport fresh N cap w z ⊆
      commonRoughSupport old fresh N cap w z :=
    fun b hb => Finset.mem_union.mpr (Or.inl hb)
  have ho : fixedRoughSupport old N cap w z ⊆
      commonRoughSupport old fresh N cap w z :=
    fun b hb => Finset.mem_union.mpr (Or.inr hb)
  have hmu (retainOdd : List ℕ → Bool) :
      fixedRoughCoefficient retainOdd N cap w z b =
        if b ∈ fixedRoughSupport retainOdd N cap w z then
          (ArithmeticFunction.moebius b : ℝ) else 0 := by
    simp [fixedRoughCoefficient, fixedRoughSupport, oddFirstExitRetainedCoefficient]
  rw [trueDDeltaRho_eq_actual_difference,
    ← actualSmallRoughRho_eq_on_common_carrier fresh N cap w z L
      (commonRoughSupport old fresh N cap w z) hf,
    ← actualSmallRoughRho_eq_on_common_carrier old N cap w z L
      (commonRoughSupport old fresh N cap w z) ho,
    smallRoughRho_mul hs hr _ _ _ ha hb,
    smallRoughRho_mul hs hr _ _ _ ha hb]
  dsimp only [smallRoughPairCoefficient]
  rw [hmu fresh, hmu old]
  by_cases hnew : b ∈ fixedRoughSupport fresh N cap w z <;>
    by_cases hold : b ∈ fixedRoughSupport old N cap w z <;>
    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient] <;>
      split_ifs <;> rfl

/-- Any complex arithmetic test of the original signed coefficient has
this exact pair sum. Multiplication is injective on the actual separated
supports, so no factorization multiplicity or absolute discrepancy appears. -/
theorem trueDDeltaRho_test_eq_pair_sum
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℂ) :
    (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
      ∑ a ∈ actualSmallRosserSupport N cap w,
        ∑ b ∈ commonRoughSupport old fresh N cap w z,
          (roughMaskDelta old fresh N cap w z b : ℂ) *
            (attachedMobius N cap w L a b : ℂ) * G (a * b) := by
  have hs : ∀ a ∈ actualSmallRosserSupport N cap w, SmallPrimeSupportedAt w a :=
    fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hr : ∀ b ∈ commonRoughSupport old fresh N cap w z, RoughPrimeSupportedAt w b :=
    fun b hb => commonRoughSupport_rough old fresh N cap w z hb
  rw [trueDDeltaSupport_eq_smallRoughModuli, smallRoughModuli,
    Finset.sum_image (smallRough_mul_injOn hs hr)]
  unfold smallRoughPairs
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [trueDDeltaRho_mul old fresh N cap w z L ha hb, Complex.ofReal_mul]

/-- The historical remaining-modulus filter stays on the COMPLETE physical
product a*b. In particular this keeps both panModulusCutoff and the .599
ceiling, with the original union support and original policy order. -/
theorem remaining_trueDDeltaRho_test_eq_pair_sum
    (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (G : ℕ → ℂ) :
    (∑ d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
      (trueDDeltaRho old fresh N cap w z L d : ℂ) * G d) =
      ∑ a ∈ actualSmallRosserSupport N cap w,
        ∑ b ∈ commonRoughSupport old fresh N cap w z,
          (roughMaskDelta old fresh N cap w z b : ℂ) *
            (attachedMobius N cap w L a b : ℂ) *
              (if a * b ∈ remainingModuli B N
                (trueDDeltaSupport old fresh N cap w z) then G (a * b) else 0) := by
  calc
    _ = ∑ d ∈ trueDDeltaSupport old fresh N cap w z,
        (trueDDeltaRho old fresh N cap w z L d : ℂ) *
          (if d ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z)
            then G d else 0) := by
      unfold remainingModuli
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcut : panModulusCutoff N B < d ∧
          (d : ℝ) < (N : ℝ)^(599/1000 : ℝ) <;>
        simp [Finset.mem_filter, hd, hcut]
    _ = _ := trueDDeltaRho_test_eq_pair_sum old fresh N cap w z L _

end

end ImbalancedChen.P1OriginalHistoricalCoefficientDictionary
