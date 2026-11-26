import ImbalancedChen.Part3LiteralReciprocalSource
import ImbalancedChen.Part3OriginalCommonPoissonKernelLanesCore
import ImbalancedChen.Part3PrimaryDyadicAssembly

/- The existing primary assembly already serializes nonzeroSource.eq_1.
Import that owner before the recovered source splits unfold nonzeroSource,
so the same generated equation is reused instead of serialized twice. -/

/-!
# The literal completed reciprocal source and its common Poisson lanes

Source-preserving intake plus new finite composition, 2026-11-26.
The marked recovered fragments keep their original namespaces, names,
statements and proof bodies from these exact original blobs:
* ActualReciprocalSquarePoisson: 58e9a86e0bd60aee30ebc7a15c781f2dd96a49c9;
* ActualCompletedSquarePushforward: 04972fd9774d63bfa5aca69b23d2e389446b448b.
The literal source, carrier, weight, beta and weighted pushforward are reused
from the accepted P3.4 supplier; they are not redeclared or reproved here.
The existing owners supply Inner, fixedUnit, atomCoeff, level, difference,
outputY, Output and completedKernel.

The recovered completedPiece is the actual finite c/f/t/h expression with
its complete integer Poisson series. The same lambda and omega occur before
and after grouping. They have no future Poisson-frequency or spectral-height
argument. The new composition uses one explicit J for every grouped output
and for both signs of y. It leaves the y=0 source with ALL m, and resolves
only y>0 and y<0 into m=0, common positive/negative m blocks and the exact
complementary tail. No zero-y term is paid twice. The negative-m Fourier
argument is the one retained by the accepted physical kernel supplier.

This is the finite source bookkeeping for the 1106 analytic appendix,
lines 667-727: the coefficient is independent of future m, and the signed
m intervals are common across levels. The manuscript's tail estimate and
subsequent spectral normalization are not conclusions of this identity.
The parameter B in completedPiece is retained exactly as in the original
source, although that completed expression only uses M, N, C and F.

This module does not certify sixSmoothMass -> completedPiece, construct or
replace OriginalData, choose the original global cutoff, construct a
spectral PacketData/kernel, instantiate Theorem J/A, or bound the tail.
Strict compilation and formal acceptance of this intake are separate.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

-- BEGIN recovered completed_piece
def completedPiece (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N _B C F : ℝ) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
    if f ≠ 0 then (scaledDyadicCutoff N c : ℂ) *
      (∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
        if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
          (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
            ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0) else 0
-- END recovered completed_piece

end ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

namespace ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly

-- BEGIN recovered signed_y_sources
def zeroSource (U : Finset Source) : Finset Source := U.filter (fun s => (output s).2 = 0)
def positiveSource (U : Finset Source) : Finset Source := U.filter (fun s => 0 < (output s).2)
def negativeSource (U : Finset Source) : Finset Source := U.filter (fun s => (output s).2 < 0)
-- END recovered signed_y_sources

-- BEGIN recovered zero_nonzero_source_split
theorem sum_zero_nonzero (U : Finset Source) (g : Source → ℂ) :
    (∑ s ∈ U, g s) = (∑ s ∈ zeroSource U, g s) + ∑ s ∈ nonzeroSource U, g s := by
  simp only [zeroSource, nonzeroSource, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  by_cases hy : (output s).2 = 0
  · simp [hy]
  · simp [hy]
-- END recovered zero_nonzero_source_split

-- BEGIN recovered positive_negative_source_split
theorem sum_positive_negative (U : Finset Source) (g : Source → ℂ) :
    (∑ s ∈ nonzeroSource U, g s) =
      (∑ s ∈ positiveSource U, g s) + ∑ s ∈ negativeSource U, g s := by
  simp only [nonzeroSource, positiveSource, negativeSource, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  by_cases hz : (output s).2 = 0
  · simp only [hz, ne_eq, not_true_eq_false, if_false, lt_self_iff_false, zero_add]
  · by_cases hp : 0 < (output s).2
    · have hn : ¬(output s).2 < 0 := by omega
      simp only [if_pos hz, if_pos hp, if_neg hn, add_zero]
    · have hn : (output s).2 < 0 := by omega
      simp only [if_pos hz, if_neg hp, if_pos hn, zero_add]
-- END recovered positive_negative_source_split

-- BEGIN recovered completed_source_bridges
theorem completedPiece_eq_source (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    completedPiece A a T H lambda omega M N B C F =
      ∑ s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)),
        weight lambda omega s * completedKernel M N C a (output s) := by
  unfold completedPiece
  rw [sum_comm]
  simp only [carrier, rawCarrier, sum_filter, sum_product]
  apply sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · simp only [if_pos hfn, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    rw [sum_comm]
    apply sum_congr rfl
    intro v hv
    by_cases hfu : fixedUnit A a u.1
    · by_cases hfv : fixedUnit A a v.1
      · have hgate : f ≠ 0 ∧ fixedUnit A a u.1 ∧ fixedUnit A a v.1 := ⟨hfn,hfu,hfv⟩
        simp only [if_pos hgate, completedKernel, mul_sum]
        apply sum_congr rfl
        intro c hc
        change
          (scaledDyadicCutoff N c : ℂ) *
              (if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
                (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
                  ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0) =
            (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
              (if c.Coprime (level u v) then
                (scaledDyadicCutoff N c : ℂ) *
                  ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0)
        by_cases hcz : c.Coprime (level u v)
        · have hpair : fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧
              c.Coprime (level u v) := ⟨hfu,hfv,hcz⟩
          rw [if_pos hpair, if_pos hcz]
          ring
        · have hpair : ¬(fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧
              c.Coprime (level u v)) := fun h => hcz h.2.2
          rw [if_neg hpair, if_neg hcz]
          simp only [mul_zero]
      · simp [hfn,hfu,hfv]
    · simp [hfn,hfu]
  · simp [hfn]
/-- Actual completed piece -> JOINT beta(z,y) on its literal image. -/
theorem completedPiece_eq_joint_beta (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    let U := carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))
    completedPiece A a T H lambda omega M N B C F =
      ∑ zy ∈ U.image output, beta U lambda omega zy * completedKernel M N C a zy := by
  dsimp only
  rw [completedPiece_eq_source]
  exact weighted_pushforward _ _ _ _

/-- Literal completed smooth piece split into y0, positive y and negative y,
with each ORIGINAL weighted joint beta kept on its own finite image. -/
theorem completedPiece_eq_three_joint_betas (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    let U := carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))
    let K := completedKernel M N C a
    completedPiece A a T H lambda omega M N B C F =
      (∑ zy ∈ (zeroSource U).image output, beta (zeroSource U) lambda omega zy*K zy) +
      (∑ zy ∈ (positiveSource U).image output, beta (positiveSource U) lambda omega zy*K zy) +
      (∑ zy ∈ (negativeSource U).image output, beta (negativeSource U) lambda omega zy*K zy) := by
  dsimp only
  rw [completedPiece_eq_source,sum_zero_nonzero,sum_positive_negative]
  simp only [weighted_pushforward]
  ring
-- END recovered completed_source_bridges

open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102

-- BEGIN new finite composition
/-- The same grouped source coefficient on zero m, common signed dyadic
m blocks and the complementary tail. The source is not filtered by m or J. -/
def sourceMLanes (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (J : ℕ) (M N C : ℝ) (a : ℤ) : ℂ :=
  (∑ zy ∈ U.image output, beta U lambda omega zy * zeroMKernel M N C a zy) +
    (∑ j ∈ blockIndices J,
      ((∑ zy ∈ U.image output, beta U lambda omega zy * blockKernel J j false M N C a zy) +
      (∑ zy ∈ U.image output, beta U lambda omega zy * blockKernel J j true M N C a zy))) +
    (∑ zy ∈ U.image output, beta U lambda omega zy * tailKernel J M N C a zy)

/-- New finite composition of the accepted full-kernel decomposition.
The identical beta, J and finite output image occur in every m lane. -/
theorem joint_beta_eq_common_m_lanes (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) (a : ℤ) :
    (∑ zy ∈ U.image output, beta U lambda omega zy * completedKernel M N C a zy) =
      sourceMLanes U lambda omega J M N C a := by
  unfold sourceMLanes
  simp_rw [completedKernel_eq_m_lanes hM J N C a]
  simp only [mul_add, mul_sum, sum_add_distrib]
  rw [sum_comm (s := U.image output) (t := blockIndices J),
    sum_comm (s := U.image output) (t := blockIndices J)]

/-- New actual finite-source endpoint. The y=0 source retains its full
integer m series; the two nonzero-y sources use one common explicit J.
There is no positivity or nonemptiness premise on a source or on J. -/
theorem completedPiece_eq_common_m_lanes (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N B C F : ℝ) :
    let U := carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))
    completedPiece A a T H lambda omega M N B C F =
      (∑ zy ∈ (zeroSource U).image output,
        beta (zeroSource U) lambda omega zy * completedKernel M N C a zy) +
      sourceMLanes (positiveSource U) lambda omega J M N C a +
      sourceMLanes (negativeSource U) lambda omega J M N C a := by
  dsimp only
  rw [completedPiece_eq_three_joint_betas]
  rw [joint_beta_eq_common_m_lanes
        (positiveSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))))
        lambda omega hM J N C a,
      joint_beta_eq_common_m_lanes
        (negativeSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))))
        lambda omega hM J N C a]
-- END new finite composition

end ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
end
