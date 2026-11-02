import ImbalancedChen.Part3ActualZeroPoissonKernel
import ImbalancedChen.Part3ActualCompletedSquarePushforward

/-!
Source only; uncompiled; zero formal credit.

An exact bridge to the already-defined production completedPiece and its
literal floor(10*C) modulus carrier. The actual bump has upper support
5/2, so all three original c-smoothing scales C,2*C,4*C are covered.
The full original signed-f carrier is retained here. Its y=0 part stays
separate from the m=0 part on y!=0. No assumption identifies a new sum
with completedPiece; the finite equality is proved below.
-/

namespace ImbalancedChen.Part3.ActualZeroPoissonNativeSource20261102
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualZeroPoissonKernel20261102
open scoped BigOperators

/-- The existing convenient support theorem uses 3; the actual bump's
center 3/2 and outer radius 1 give the sharper 5/2 used by the six-cover. -/
theorem cutoff_upper_five_halves {N : ℝ} (hN : 0 < N) (c : ℕ)
    (hc : scaledDyadicCutoff N c ≠ 0) : (c : ℝ) ≤ (5/2 : ℝ)*N := by
  have hx : (c : ℝ)/N ∈ tsupport (dyadicBump : ℝ → ℝ) :=
    subset_closure (show dyadicBump ((c : ℝ)/N) ≠ 0 from hc)
  rw [dyadicBump.tsupport_eq] at hx
  change |(c : ℝ)/N-3/2| ≤ 1 at hx
  apply (div_le_iff₀ hN).mp
  linarith [(abs_le.mp hx).2]

/-- Exact equality of finite c carriers for ANY kernel. This covers
all original N=C,2C,4C choices; support, not an estimate, removes terms. -/
theorem smooth_modulus_sum_eq_capped {N C : ℝ} (hN : 0 < N) (hNC : N ≤ 4*C)
    (K : ℕ → ℂ) :
    (∑ c ∈ smoothModuli N, (scaledDyadicCutoff N c : ℂ)*K c) =
      ∑ c ∈ Ioc 0 (Nat.floor (10*C)), (scaledDyadicCutoff N c : ℂ)*K c := by
  let S := smoothModuli N
  let T := Ioc 0 (Nat.floor (10*C))
  have hT (c : ℕ) (hc : scaledDyadicCutoff N c ≠ 0) : c ∈ T := by
    have hlo := (scaledDyadicCutoff_mem_Icc_of_ne_zero hN hc).1
    have hpos : (0 : ℝ) < c := (half_pos hN).trans_le hlo
    have hupper := cutoff_upper_five_halves hN c hc
    exact mem_Ioc.mpr ⟨by exact_mod_cast hpos,Nat.le_floor (by linarith)⟩
  calc
    _ = ∑ c ∈ S ∪ T, (scaledDyadicCutoff N c : ℂ)*K c := by
      apply sum_subset subset_union_left
      intro c hc hnot
      have hw : scaledDyadicCutoff N c = 0 := by
        by_contra hw
        exact hnot (mem_smoothModuli_of_cutoff_ne_zero hN c hw)
      simp only [hw,Complex.ofReal_zero,zero_mul]
    _ = _ := by
      symm
      apply sum_subset subset_union_right
      intro c hc hnot
      have hw : scaledDyadicCutoff N c = 0 := by
        by_contra hw
        exact hnot (hT c hw)
      simp only [hw,Complex.ofReal_zero,zero_mul]

/-- The earlier native completed kernel, with all m and its original
10*C cap, is the same kernel used in the new zero/nonzero split. -/
theorem native_completedKernel_eq {N C : ℝ} (hN : 0 < N) (hNC : N ≤ 4*C)
    (D : ℝ) (a : ℤ) (zy : Output) :
    ActualCompletedSquarePushforwardSourceOnly.completedKernel D N C a zy =
      ActualZeroPoissonKernel20261102.completedKernel N D a zy := by
  calc
    _ = ∑ c ∈ Ioc 0 (Nat.floor (10*C)), (scaledDyadicCutoff N c : ℂ)*
        OriginalSignedCountingNorm20261028.physicalKernel D c a zy := by
      apply sum_congr rfl
      intro c hc
      by_cases h : c.Coprime zy.1 <;>
        simp only [OriginalSignedCountingNorm20261028.physicalKernel,h,if_true,if_false,mul_zero]
    _ = _ := (smooth_modulus_sum_eq_capped hN hNC _).symm

def nativeZeroPiece (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (N D : ℝ) (a : ℤ) : ℂ :=
  ∑ s ∈ U, weight lambda omega s*zeroKernel N D a (output s)

def nativeNonzeroPiece (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (N D : ℝ) (a : ℤ) : ℂ :=
  ∑ s ∈ U, weight lambda omega s*nonzeroKernel N D a (output s)

/-- Real original consumer: exact completedPiece, not a newly assumed
source. y=0 is retained separately, while the y!=0 source is split into
m=0 and m!=0 using actual summability. All signed f and ordered pairs stay. -/
theorem completedPiece_eq_three_parts (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {D N C : ℝ}
    (hD : 0 < D) (hN : 0 < N) (hNC : N ≤ 4*C) (B F : ℝ) :
    completedPiece A a T H lambda omega D N B C F =
      (∑ s ∈ zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))),
        weight lambda omega s*
          ActualCompletedSquarePushforwardSourceOnly.completedKernel D N C a (output s)) +
      nativeZeroPiece (nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))))
        lambda omega N D a +
      nativeNonzeroPiece (nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))))
        lambda omega N D a := by
  rw [completedPiece_eq_source,sum_zero_nonzero]
  rw [show (∑ s ∈ nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))),
      weight lambda omega s*
        ActualCompletedSquarePushforwardSourceOnly.completedKernel D N C a (output s)) =
      nativeZeroPiece (nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))))
        lambda omega N D a +
      nativeNonzeroPiece (nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))))
        lambda omega N D a by
    simp only [native_completedKernel_eq hN hNC,completedKernel_eq_zero_add_nonzero hD,
      mul_add,sum_add_distrib,nativeZeroPiece,nativeNonzeroPiece]]
  ring

def nativeResidueDivisorMaximum (U : Finset Source) (a : ℤ) : ℕ :=
  (U.image output).sup (fun zy => (a*zy.2).natAbs.divisors.card)

def nativeCoefficientNorm (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) : ℝ :=
  ∑ zy ∈ U.image output, ‖beta U lambda omega zy‖^2

/-- The full native signed-f source receives its physical m=0 estimate.
The coefficient is the existing joint pushforward beta. Only finite
support/count costs remain, with no independent beta or bound premise. -/
theorem nativeZeroPiece_sq_le {N D : ℝ} (hN : 0 < N) (hD : 0 ≤ D)
    (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (a : ℤ) (ha : a ≠ 0) (hU : ∀ s ∈ U, (output s).2 ≠ 0) :
    ‖nativeZeroPiece U lambda omega N D a‖^2 ≤
      (6*D*zeroFourierMass*(nativeResidueDivisorMaximum U a : ℝ))^2 *
        ((U.image output).card : ℝ)*nativeCoefficientNorm U lambda omega := by
  let K : ℝ := 6*D*zeroFourierMass*(nativeResidueDivisorMaximum U a : ℝ)
  have hK0 : 0 ≤ K := by unfold K zeroFourierMass; positivity
  have hpoint (zy : Output) (hzy : zy ∈ U.image output) : ‖zeroKernel N D a zy‖ ≤ K := by
    obtain ⟨s,hs,heq⟩ := mem_image.mp hzy
    have hy : zy.2 ≠ 0 := by rw [← heq]; exact hU s hs
    apply (zeroKernel_norm_le hN hD a zy (mul_ne_zero ha hy)).trans
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast (le_sup hzy : (a*zy.2).natAbs.divisors.card ≤ nativeResidueDivisorMaximum U a)
    · unfold zeroFourierMass
      positivity
  rw [nativeZeroPiece,weighted_pushforward]
  have htriangle : ‖∑ zy ∈ U.image output, beta U lambda omega zy*zeroKernel N D a zy‖ ≤
      K*∑ zy ∈ U.image output, ‖beta U lambda omega zy‖ := by
    calc
      _ ≤ ∑ zy ∈ U.image output, ‖beta U lambda omega zy*zeroKernel N D a zy‖ := norm_sum_le _ _
      _ ≤ ∑ zy ∈ U.image output, ‖beta U lambda omega zy‖*K := by
        apply sum_le_sum
        intro zy hzy
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpoint zy hzy) (norm_nonneg _)
      _ = _ := by rw [sum_mul]; ring
  have hcs := sum_mul_sq_le_sq_mul_sq (U.image output) (fun _ => (1 : ℝ))
    (fun zy => ‖beta U lambda omega zy‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  calc
    _ ≤ (K*∑ zy ∈ U.image output, ‖beta U lambda omega zy‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ = K^2*(∑ zy ∈ U.image output, ‖beta U lambda omega zy‖)^2 := mul_pow _ _ _
    _ ≤ K^2*((U.image output).card : ℝ)*nativeCoefficientNorm U lambda omega := by
      simpa only [mul_assoc,nativeCoefficientNorm] using mul_le_mul_of_nonneg_left hcs (sq_nonneg K)

/-- Discharge the source support premise at the actual original nonzero-y
part of completedPiece. This covers every original signed f, including
both signs, without asserting a completed dyadic-f count dictionary. -/
theorem completedPiece_nonzero_y_zero_mode_sq_le (A : ℕ) (a : ℤ) (ha : a ≠ 0)
    (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    {N D : ℝ} (hN : 0 < N) (hD : 0 ≤ D) (F : ℝ) :
    let U := nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)))
    ‖nativeZeroPiece U lambda omega N D a‖^2 ≤
      (6*D*zeroFourierMass*(nativeResidueDivisorMaximum U a : ℝ))^2*
        ((U.image output).card : ℝ)*nativeCoefficientNorm U lambda omega := by
  dsimp only
  apply nativeZeroPiece_sq_le hN hD _ lambda omega a ha
  intro s hs
  exact (mem_filter.mp hs).2

end
end ImbalancedChen.Part3.ActualZeroPoissonNativeSource20261102
