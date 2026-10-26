import ImbalancedChen.Part3LocalL2WeakGradientUniqueness

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Countable patching of independently extracted local gradients. The first
cover index chooses a representative; native smooth-test uniqueness makes
it agree a.e. with every local L2 witness. Local L2 and all weak identities
survive this patch. No global L2 bound is asserted or assumed. -/

namespace ImbalancedChen.Part3.CountableLocalWeakGradientPatching20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ProductConvolutionSecondDerivatives20261026a
open PlanarLocalWeakGradientExtraction20261026b LocalL2WeakGradientUniqueness20261026b

def patchComponent (Ω : ℕ → Set Plane) (g : ℕ → PlaneL2) (p : Plane) : ℂ :=
  if hp : ∃ n, p ∈ Ω n then g (Nat.find hp) p else 0

theorem patchComponent_ae_eq_on (Ω : ℕ → Set Plane) (g : ℕ → PlaneL2)
    (hcompat : ∀ n k, ∀ᵐ p ∂(volume : Measure Plane),
      p ∈ Ω n ∩ Ω k → g n p = g k p) (n : ℕ) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ Ω n → patchComponent Ω g p = g n p := by
  have hall : ∀ᵐ p ∂(volume : Measure Plane), ∀ k : ℕ,
      p ∈ Ω n ∩ Ω k → g n p = g k p := ae_all_iff.2 (hcompat n)
  filter_upwards [hall] with p hp
  intro hpn
  unfold patchComponent
  split_ifs with hcover
  · exact (hp (Nat.find hcover) ⟨hpn, Nat.find_spec hcover⟩).symm
  · exact False.elim (hcover ⟨n, hpn⟩)

/-- One pair of genuine scalar functions represents all local weak
gradients, with separate local L2 membership on every open cover set. -/
def HasPatchedLocalWeakGradient (Ω : ℕ → Set Plane) (F : Plane → ℂ)
    (Gx Gy : Plane → ℂ) : Prop :=
  ∀ n : ℕ,
    MemLp F 2 ((volume : Measure Plane).restrict (Ω n)) ∧
    MemLp Gx 2 ((volume : Measure Plane).restrict (Ω n)) ∧
    MemLp Gy 2 ((volume : Measure Plane).restrict (Ω n)) ∧
    ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω n →
      ((∫ p, star (ψ p) * Gx p) = -(∫ p, star (directional xDirection ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * Gy p) = -(∫ p, star (directional yDirection ψ p) * F p))

theorem exists_patched_local_weak_gradient (Ω : ℕ → Set Plane)
    (hΩ : ∀ n, IsOpen (Ω n)) (F : Plane → ℂ)
    (hF : ∀ n, MemLp F 2 ((volume : Measure Plane).restrict (Ω n)))
    (gx gy : ℕ → PlaneL2) (hgrad : ∀ n, IsLocalWeakGradientOn (Ω n) F (gx n) (gy n)) :
    ∃ Gx Gy : Plane → ℂ, HasPatchedLocalWeakGradient Ω F Gx Gy := by
  have hcompat := fun n k => weak_gradients_agree_on_overlap (hΩ n) (hΩ k) F
    (gx n) (gy n) (gx k) (gy k) (hgrad n) (hgrad k)
  have hcx (n k : ℕ) : ∀ᵐ p ∂(volume : Measure Plane),
      p ∈ Ω n ∩ Ω k → gx n p = gx k p := by
    filter_upwards [hcompat n k] with p hp
    exact fun hpin => (hp hpin).1
  have hcy (n k : ℕ) : ∀ᵐ p ∂(volume : Measure Plane),
      p ∈ Ω n ∩ Ω k → gy n p = gy k p := by
    filter_upwards [hcompat n k] with p hp
    exact fun hpin => (hp hpin).2
  let Gx := patchComponent Ω gx
  let Gy := patchComponent Ω gy
  have hx (n : ℕ) : ∀ᵐ p ∂(volume : Measure Plane), p ∈ Ω n → Gx p = gx n p :=
    patchComponent_ae_eq_on Ω gx hcx n
  have hy (n : ℕ) : ∀ᵐ p ∂(volume : Measure Plane), p ∈ Ω n → Gy p = gy n p :=
    patchComponent_ae_eq_on Ω gy hcy n
  refine ⟨Gx, Gy, fun n => ?_⟩
  have hxr : Gx =ᵐ[(volume : Measure Plane).restrict (Ω n)] gx n :=
    (ae_restrict_iff' (hΩ n).measurableSet).2 (hx n)
  have hyr : Gy =ᵐ[(volume : Measure Plane).restrict (Ω n)] gy n :=
    (ae_restrict_iff' (hΩ n).measurableSet).2 (hy n)
  refine ⟨hF n, (memLp_congr_ae hxr).2 ((gx n).memLp.restrict (Ω n)),
    (memLp_congr_ae hyr).2 ((gy n).memLp.restrict (Ω n)), fun ψ hψ hc hs => ?_⟩
  have hpx : (∫ p, star (ψ p) * Gx p) = ∫ p, star (ψ p) * gx n p := by
    apply integral_congr_ae
    filter_upwards [hx n] with p hp
    by_cases hpin : p ∈ tsupport ψ
    · rw [hp (hs hpin)]
    · simp [image_eq_zero_of_notMem_tsupport hpin]
  have hpy : (∫ p, star (ψ p) * Gy p) = ∫ p, star (ψ p) * gy n p := by
    apply integral_congr_ae
    filter_upwards [hy n] with p hp
    by_cases hpin : p ∈ tsupport ψ
    · rw [hp (hs hpin)]
    · simp [image_eq_zero_of_notMem_tsupport hpin]
  obtain ⟨hweakx, hweaky⟩ := hgrad n ψ hψ hc hs
  exact ⟨hpx.trans hweakx, hpy.trans hweaky⟩

end
end ImbalancedChen.Part3.CountableLocalWeakGradientPatching20261026b
