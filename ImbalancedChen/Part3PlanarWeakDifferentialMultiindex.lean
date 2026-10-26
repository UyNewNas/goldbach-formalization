import ImbalancedChen.Part3CompactC2JetCutoffEstimate
import ImbalancedChen.Part3ProductConvolutionSecondDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Shared ordinary-plane weak-jet ABI. All derivatives here are real Frechet
derivatives. Compact test support is preserved through every derivative.
The commutation of test derivatives is proved from native symmetry of
the second Frechet derivative, including the distributional Laplacian
commutation needed by the local elliptic bootstrap.
-/

namespace ImbalancedChen.Part3.PlanarWeakDifferentialMultiindex20261026b
noncomputable section
open Set MeasureTheory Filter
open CompactC2ProductMollifier20261026a

abbrev MultiIndex := ℕ × ℕ

def testPartial (α : MultiIndex) (ψ : Plane → ℂ) : Plane → ℂ :=
  directionalIter ex α.1 (directionalIter ey α.2 ψ)

def HasWeakPartialOn (Ω : Set Plane) (u g : Plane → ℂ) (α : MultiIndex) : Prop :=
  ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    (∫ p, star (ψ p) * g p) =
      (-1 : ℂ)^(α.1+α.2) * ∫ p, star (testPartial α ψ p) * u p

/-- A coherent raw jet, with genuine local L2 at every retained order.
The adjacent-edge identities use ordinary full-plane integrals and
globally smooth compact tests supported inside the indicated open set. -/
structure HasWeakJetOn (Ω : Set Plane) (m : ℕ) (u : Plane → ℂ)
    (J : MultiIndex → Plane → ℂ) : Prop where
  value_ae : J (0,0) =ᵐ[(volume : Measure Plane).restrict Ω] u
  local_memLp : ∀ α : MultiIndex, α.1+α.2 ≤ m → ∀ K : Set Plane,
    IsCompact K → K ⊆ Ω → MemLp (J α) 2 ((volume : Measure Plane).restrict K)
  weak_x : ∀ α : MultiIndex, α.1+α.2 < m → ∀ ψ : Plane → ℂ,
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (directional ex ψ p)*J α p) =
        -(∫ p, star (ψ p)*J (α.1+1,α.2) p)
  weak_y : ∀ α : MultiIndex, α.1+α.2 < m → ∀ ψ : Plane → ℂ,
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (directional ey ψ p)*J α p) =
        -(∫ p, star (ψ p)*J (α.1,α.2+1) p)

theorem directional_support (v : Plane) (ψ : Plane → ℂ) :
    tsupport (directional v ψ) ⊆ tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ v

theorem directionalIter_support (v : Plane) (n : ℕ) (ψ : Plane → ℂ) :
    tsupport (directionalIter v n ψ) ⊆ tsupport ψ := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact (directional_support v _).trans ih

theorem testPartial_smooth (α : MultiIndex) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (testPartial α ψ) :=
  directionalIter_smooth ex _ (directionalIter_smooth ey _ hψ)

theorem testPartial_compact (α : MultiIndex) {ψ : Plane → ℂ}
    (hc : HasCompactSupport ψ) : HasCompactSupport (testPartial α ψ) :=
  directionalIter_compact ex _ (directionalIter_compact ey _ hc)

theorem testPartial_support (α : MultiIndex) (ψ : Plane → ℂ) :
    tsupport (testPartial α ψ) ⊆ tsupport ψ :=
  (directionalIter_support ex _ _).trans (directionalIter_support ey _ _)

theorem directional_commute (v w : Plane) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) :
    directional v (directional w ψ) = directional w (directional v ψ) := by
  funext p
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) p :=
    ((hψ.fderiv_right (by simp)).differentiable (by simp)) p
  have heval (a b : Plane) : directional a (directional b ψ) p =
      fderiv ℝ (fderiv ℝ ψ) p a b := by
    change fderiv ℝ (fun q => (fderiv ℝ ψ q) b) p a = _
    rw [fderiv_clm_apply hd differentiableAt_const]
    simp
  rw [heval v w,heval w v]
  exact hψ.contDiffAt.isSymmSndFDerivAt (by simp) v w

theorem directional_directionalIter (v w : Plane) (n : ℕ) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) :
    directional v (directionalIter w n ψ) = directionalIter w n (directional v ψ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change directional v (directional w (directionalIter w n ψ)) = _
      rw [directional_commute v w (directionalIter_smooth w n hψ),ih]
      rfl

theorem directionalIter_add_orders (v : Plane) (m n : ℕ) (ψ : Plane → ℂ) :
    directionalIter v (m+n) ψ = directionalIter v m (directionalIter v n ψ) := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [Nat.succ_add,directionalIter,ih]

theorem testPartial_x_succ (α : MultiIndex) (ψ : Plane → ℂ) :
    testPartial (α.1+1,α.2) ψ = directional ex (testPartial α ψ) := rfl

theorem testPartial_y_succ (α : MultiIndex) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) :
    testPartial (α.1,α.2+1) ψ = directional ey (testPartial α ψ) := by
  unfold testPartial
  change directionalIter ex α.1 (directional ey (directionalIter ey α.2 ψ)) = _
  exact (directional_directionalIter ey ex α.1
    (directionalIter_smooth ey α.2 hψ)).symm

theorem laplacian_eq_directional (ψ : Plane → ℂ) :
    ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ =
      directional ex (directional ex ψ) + directional ey (directional ey ψ) := rfl

theorem laplacian_smooth {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ) :=
  (directional_smooth ex (directional_smooth ex hψ)).add
    (directional_smooth ey (directional_smooth ey hψ))

theorem laplacian_compact {ψ : Plane → ℂ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ) :=
  (directional_compact ex (directional_compact ex hc)).add
    (directional_compact ey (directional_compact ey hc))

theorem laplacian_support (ψ : Plane → ℂ) :
    tsupport (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ) ⊆ tsupport ψ := by
  exact (tsupport_add _ _).trans (union_subset
    ((directional_support ex _).trans (directional_support ex ψ))
    ((directional_support ey _).trans (directional_support ey ψ)))

theorem directional_laplacian (v : Plane) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) :
    directional v (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ) =
      ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian (directional v ψ) := by
  simp only [laplacian_eq_directional]
  rw [CompactC2JetCutoffEstimate20261026a.directional_add v
    (directional_smooth ex (directional_smooth ex hψ))
    (directional_smooth ey (directional_smooth ey hψ)),
    directional_commute v ex (directional_smooth ex hψ),
    directional_commute v ex hψ,
    directional_commute v ey (directional_smooth ey hψ),
    directional_commute v ey hψ]

/-- Differentiation commutes with the distributional Laplacian. Both
weak first derivatives are genuine test identities, not classical data. -/
theorem weak_laplacian_derivative (Ω : Set Plane) (v : Plane) (u g r s : Plane → ℂ)
    (hu : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ψ p)*g p) = -(∫ p, star (directional v ψ p)*u p))
    (hr : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ψ p)*s p) = -(∫ p, star (directional v ψ p)*r p))
    (hΔ : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p)*u p) =
        ∫ p, star (ψ p)*r p) :
    ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p)*g p) =
        ∫ p, star (ψ p)*s p := by
  intro ψ hψ hc hs
  rw [hu _ (laplacian_smooth hψ) (laplacian_compact hc) ((laplacian_support ψ).trans hs),
    directional_laplacian v hψ,
    hΔ _ (directional_smooth v hψ) (directional_compact v hc) ((directional_support v ψ).trans hs)]
  exact (hr ψ hψ hc hs).symm

end
end ImbalancedChen.Part3.PlanarWeakDifferentialMultiindex20261026b
