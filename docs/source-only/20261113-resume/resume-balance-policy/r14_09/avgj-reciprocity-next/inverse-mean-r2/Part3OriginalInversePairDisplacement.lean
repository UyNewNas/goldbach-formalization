import ImbalancedChen.Part3OriginalInversePairMatrix
import ImbalancedChen.Part3ActualCompactBruhatKernel

/-! Actual hyperbolic displacement of the lifts in an inverse-residue
rectangle. Reduction bounds follow from the same two-point invariant. -/
namespace ImbalancedChen.Part3.OriginalInversePairDisplacement20261113
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane
open OriginalInversePairMatrix20261113 ActualCompactBruhatKernel20261025a
open ActualInfinityKloostermanSeed20261025a OriginalSmoothPoissonTail
open SmallHeightReducedMatrixBounds20261026b Gamma0GeneralCuspUnitPeriod20261025a

private def displacement (g : SL(2,ℤ)) (z w : ℍ) : ℝ :=
  2*Real.cosh (dist (g • z) w)

/-- Both centered heights enter the physical displacement before conjugating
to fundamental-domain representatives. The four square numerators are the
entries of the two-point normalized real matrix, with common denominator. -/
theorem displacement_entries (g : SL(2,ℤ)) (z w : ℍ) :
    displacement g z w * (z.im*w.im) =
      ((g 0 0:ℝ)*z.re+(g 0 1:ℝ)-w.re*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))^2 +
      (z.im*((g 0 0:ℝ)-w.re*(g 1 0:ℝ)))^2 +
      (z.im*w.im*(g 1 0:ℝ))^2 +
      (w.im*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))^2 := by
  let A : ℂ := (g 0 0:ℂ)*(z:ℂ)+(g 0 1:ℂ)
  let B : ℂ := (g 1 0:ℂ)*(z:ℂ)+(g 1 1:ℂ)
  have hB : B≠0 := by
    simpa [B,UpperHalfPlane.denom] using
      (UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) z)
  have hBnorm : Complex.normSq B ≠ 0 := fun h => hB (Complex.normSq_eq_zero.mp h)
  have val : ((g • z : ℍ):ℂ)=A/B := by
    simpa [A,B] using UpperHalfPlane.coe_specialLinearGroup_apply g z
  have height : (g • z).im*Complex.normSq B=z.im := by
    simpa [B,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two,add_comm,add_left_comm,
      add_assoc,mul_comm,mul_left_comm,mul_assoc] using integral_image_height_denominator g z
  have hi : (g • z).im=z.im/Complex.normSq B := (eq_div_iff hBnorm).mpr height
  have diff : ((g • z : ℍ):ℂ)-(w:ℂ)=(A-(w:ℂ)*B)/B := by
    rw [val]
    field_simp [hB] <;> ring
  have inv : displacement g z w*(z.im*w.im) =
      2*z.im*w.im+Complex.normSq (A-(w:ℂ)*B) := by
    rw [displacement,UpperHalfPlane.cosh_dist,Complex.dist_eq,←Complex.normSq_eq_norm_sq,
      diff,Complex.normSq_div,hi]
    field_simp [hBnorm,z.im_ne_zero,w.im_ne_zero] <;> ring
  have det : (g 0 0:ℝ)*(g 1 1:ℝ)-(g 0 1:ℝ)*(g 1 0:ℝ)=1 := by
    exact_mod_cast (show g 0 0*g 1 1-g 0 1*g 1 0=1 by simpa only [Matrix.det_fin_two] using g.det_coe)
  rw [inv]
  simp [A,B,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  linear_combination -2*z.im*w.im*det

/-- The physical pair lies in a single hyperbolic ball after both widths
have been enlarged to ensure k²αβ≥1. The constant seven is absolute. -/
theorem physical_displacement (k : ℕ+) {u : ℕ} (hk : u<k.val) (hu : Nat.Coprime u k.val)
    (ω : ℝ) (l r : ℤ) {α β : ℝ} (hα : 0<α) (hβ : 0<β)
    (hscale : 1 ≤ (k.val:ℝ)^2*α*β)
    (ha : |(inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω-(l:ℝ)|≤α)
    (hb : |(u:ℝ)/(k.val:ℝ)+ω-(r:ℝ)|≤β) :
    2*Real.cosh (dist (lift k u hu l r • horizontalPoint β hβ ω) (horizontalPoint α hα ω)) ≤
      7*(k.val:ℝ)^2*α*β := by
  let g := lift k u hu l r
  let K := (k.val:ℝ)
  have hK : 0<K := by exact_mod_cast k.property
  have Kinv : 1/K≤K*α*β := by
    apply (div_le_iff₀ hK).mpr
    dsimp [K] at *
    nlinarith only [hscale]
  obtain ⟨C,A,D,B⟩ := lifted_rectangle k hk hu ω l r ha hb
  have B' : |(g 0 0:ℝ)*ω+(g 0 1:ℝ)-ω*(K*ω+(g 1 1:ℝ))|≤2*(K*α*β) := by
    linarith only [B,Kinv]
  have A' : |β*((g 0 0:ℝ)-ω*K)|≤K*α*β := by
    rw [abs_mul,abs_of_pos hβ,mul_comm β]
    exact mul_le_mul_of_nonneg_right A hβ.le
  have D' : |α*(K*ω+(g 1 1:ℝ))|≤K*α*β := by
    rw [abs_mul,abs_of_pos hα]
    calc
      _ ≤ α*(K*β) := mul_le_mul_of_nonneg_left D hα.le
      _ = _ := by ring
  let z := horizontalPoint β hβ ω
  let w := horizontalPoint α hα ω
  have E := displacement_entries g z w
  have CR : (g 1 0:ℝ)=K := by exact_mod_cast C
  rw [CR] at E
  change displacement g z w*(β*α)=_ at E
  have S {y b : ℝ} (hy : |y|≤b) : y^2 ≤ b^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have R : displacement g z w*(β*α) ≤ 7*K^2*α*β*(β*α) := by
    rw [E]
    change ((g 0 0:ℝ)*ω+(g 0 1:ℝ)-ω*(K*ω+(g 1 1:ℝ)))^2+
      (β*((g 0 0:ℝ)-ω*K))^2+(β*α*K)^2+(α*(K*ω+(g 1 1:ℝ)))^2 ≤ _
    nlinarith only [S B',S A',S D']
  exact (mul_le_mul_iff_left₀ (mul_pos hβ hα)).mp R

/-- Recover the centered integral lower row and upper-left entry from the
radius *after* reducing both points; this is the nonparabolic counting box. -/
theorem reduced_entries (g : SL(2,ℤ)) (z w : ℍ) {B : ℝ}
    (h : 2*Real.cosh (dist (g • z) w) ≤ B) :
    ((g 1 0:ℝ)*z.im*w.im)^2 ≤ B*(z.im*w.im) ∧
      (w.im*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))^2 ≤ B*(z.im*w.im) ∧
      (z.im*((g 0 0:ℝ)-w.re*(g 1 0:ℝ)))^2 ≤ B*(z.im*w.im) ∧
      ((g 0 0:ℝ)*z.re+(g 0 1:ℝ)-w.re*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))^2 ≤
        B*(z.im*w.im) := by
  have H := mul_le_mul_of_nonneg_right h (mul_pos z.im_pos w.im_pos).le
  change displacement g z w*(z.im*w.im) ≤ _ at H
  rw [displacement_entries] at H
  constructor
  · nlinarith [sq_nonneg ((g 0 0:ℝ)*z.re+(g 0 1:ℝ)-w.re*((g 1 0:ℝ)*z.re+(g 1 1:ℝ))),
      sq_nonneg (z.im*((g 0 0:ℝ)-w.re*(g 1 0:ℝ))),
      sq_nonneg (w.im*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))]
  constructor
  · linarith [sq_nonneg ((g 0 0:ℝ)*z.re+(g 0 1:ℝ)-w.re*((g 1 0:ℝ)*z.re+(g 1 1:ℝ))),
      sq_nonneg (z.im*((g 0 0:ℝ)-w.re*(g 1 0:ℝ))),sq_nonneg (z.im*w.im*(g 1 0:ℝ))]
  constructor
  · linarith [sq_nonneg ((g 0 0:ℝ)*z.re+(g 0 1:ℝ)-w.re*((g 1 0:ℝ)*z.re+(g 1 1:ℝ))),
      sq_nonneg (z.im*w.im*(g 1 0:ℝ)),sq_nonneg (w.im*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))]
  · linarith [sq_nonneg (z.im*((g 0 0:ℝ)-w.re*(g 1 0:ℝ))),
      sq_nonneg (z.im*w.im*(g 1 0:ℝ)),sq_nonneg (w.im*((g 1 0:ℝ)*z.re+(g 1 1:ℝ)))]

end
end ImbalancedChen.Part3.OriginalInversePairDisplacement20261113
