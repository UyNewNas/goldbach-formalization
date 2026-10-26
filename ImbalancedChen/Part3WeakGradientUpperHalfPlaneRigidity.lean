import ImbalancedChen.Part3WeakGradientRectangleRigidity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
The rectangle constants agree on an actual open overlap of positive planar
measure. A concrete countable exhaustion then gives ONE ae constant on the
whole upper half-plane. No connected-domain rigidity premise is imported. -/
namespace ImbalancedChen.Part3.WeakGradientUpperHalfPlaneRigidity20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a
open ImbalancedChen.Part3.WeakGradientRectangleRigidity20261026a

def exhaustionRadius (n : ℕ) : ℝ := n + 2

def exhaustionRectangle (n : ℕ) : Set (ℝ × ℝ) :=
  openRectangle (-(exhaustionRadius n)) (exhaustionRadius n)
    (1 / exhaustionRadius n) (exhaustionRadius n)

theorem exhaustionRadius_ge_two (n : ℕ) : 2 ≤ exhaustionRadius n := by
  dsimp [exhaustionRadius]; linarith [Nat.cast_nonneg (R := ℝ) n]

theorem exhaustionRadius_pos (n : ℕ) : 0 < exhaustionRadius n :=
  lt_of_lt_of_le (by norm_num) (exhaustionRadius_ge_two n)

theorem exhaustion_height_interval (n : ℕ) : 1 / exhaustionRadius n < exhaustionRadius n := by
  have hr := exhaustionRadius_ge_two n
  have hi : 1 / exhaustionRadius n ≤ (1:ℝ)/2 :=
    one_div_le_one_div_of_le (by norm_num) hr
  linarith

theorem exhaustion_contains_zero_rectangle (n : ℕ) :
    exhaustionRectangle 0 ⊆ exhaustionRectangle n := by
  have hr := exhaustionRadius_ge_two n
  have hi : 1 / exhaustionRadius n ≤ (1:ℝ)/2 :=
    one_div_le_one_div_of_le (by norm_num) hr
  intro p hp
  change p ∈ openRectangle _ _ _ _
  have hp' : p ∈ openRectangle (-2) 2 ((1:ℝ)/2) 2 := by
    simpa [exhaustionRectangle,exhaustionRadius] using hp
  rcases hp' with ⟨⟨hx₁,hx₂⟩,⟨hy₁,hy₂⟩⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨lt_of_le_of_lt hi hy₁,by linarith⟩⟩

theorem exhaustion_covers_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    ∃ n : ℕ, p ∈ exhaustionRectangle n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (max |p.1| p.2) (1/p.2))
  have hrad : (n:ℝ) < exhaustionRadius n := by dsimp [exhaustionRadius]; linarith
  have hx : |p.1| < exhaustionRadius n := lt_trans
    (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn) hrad
  have hy : p.2 < exhaustionRadius n := lt_trans
    (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn) hrad
  have hinv : 1/p.2 < exhaustionRadius n := lt_trans
    (lt_of_le_of_lt (le_max_right _ _) hn) hrad
  refine ⟨n, ?_⟩
  exact ⟨abs_lt.mp hx, (one_div_lt (exhaustionRadius_pos n) hp).mpr hinv, hy⟩

/-- Positive-measure overlap forces literal equality of the two scalars. -/
theorem ae_constants_eq_on_open_overlap {f : (ℝ × ℝ) → ℂ} {S T W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hWne : W.Nonempty) (hWS : W ⊆ S) (hWT : W ⊆ T)
    {C D : ℂ} (hC : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ S → f p = C)
    (hD : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ T → f p = D) : C = D := by
  by_contra hne
  have hnot : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ W := by
    filter_upwards [hC,hD] with p hpC hpD
    intro hpW
    exact hne ((hpC (hWS hpW)).symm.trans (hpD (hWT hpW)))
  have hz : volume W = 0 := by simpa only [not_not] using ae_iff.mp hnot
  exact hW.measure_ne_zero volume hWne hz

/-- The local constants are not independently selected in the conclusion:
all agree with the scalar on the explicit initial rectangle. -/
theorem one_ae_constant_of_exhaustion_constants {f : (ℝ × ℝ) → ℂ}
    (hlocal : ∀ n : ℕ, ∃ C : ℂ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      p ∈ exhaustionRectangle n → f p = C) :
    ∃ C : ℂ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.2 → f p = C := by
  choose C hC using hlocal
  have hcommon : ∀ n, C n = C 0 := by
    intro n
    exact ae_constants_eq_on_open_overlap
      (isOpen_Ioo.prod isOpen_Ioo)
      (show (exhaustionRectangle 0).Nonempty from ⟨(0,1), by
        norm_num [exhaustionRectangle,exhaustionRadius,openRectangle]⟩)
      (exhaustion_contains_zero_rectangle n) subset_rfl (hC n) (hC 0)
  refine ⟨C 0, ?_⟩
  filter_upwards [ae_all_iff.mpr hC] with p hp
  intro hpupper
  obtain ⟨n,hn⟩ := exhaustion_covers_positive hpupper
  exact (hp n hn).trans (hcommon n)

/-- Literal zero weak tensor derivatives on the exhaustion rectangles. -/
def ZeroWeakPartialsOnRectangle (f : (ℝ × ℝ) → ℂ) (a b c d : ℝ) : Prop :=
  (∀ ψ h : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo a b →
    ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ Ioo c d →
    tensorPairing (openRectangle a b c d) f (deriv ψ) h = 0) ∧
  (∀ g ψ : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo c d →
    tensorPairing (openRectangle a b c d) f g (deriv ψ) = 0)

/-- Genuine upper-half-plane rigidity from local L² and the actual tensor
weak equations. There is no global L² assumption (a nonzero constant would
not satisfy it) and no regular-representative assumption. -/
theorem ae_eq_one_const_of_zero_weak_gradient {f : (ℝ × ℝ) → ℂ}
    (hf : ∀ n : ℕ, MemLp f 2 (volume.restrict (exhaustionRectangle n)))
    (hweak : ∀ n : ℕ, ZeroWeakPartialsOnRectangle f (-(exhaustionRadius n))
      (exhaustionRadius n) (1 / exhaustionRadius n) (exhaustionRadius n)) :
    ∃ C : ℂ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.2 → f p = C := by
  apply one_ae_constant_of_exhaustion_constants
  intro n
  exact ae_eq_one_const_of_zero_weak_partials
    (by linarith [exhaustionRadius_pos n]) (exhaustion_height_interval n)
    (le_of_lt (one_div_pos.mpr (exhaustionRadius_pos n)))
    (hf n) (hweak n).1 (hweak n).2

end
end ImbalancedChen.Part3.WeakGradientUpperHalfPlaneRigidity20261026a
