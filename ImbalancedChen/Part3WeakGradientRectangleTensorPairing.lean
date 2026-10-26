import ImbalancedChen.Part3WeakDerivativeIntervalRigidity
import Mathlib.MeasureTheory.Integral.Prod

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
Two actual zero weak coordinate partials determine all compact tensor pairings
on a rectangle by ONE normalized tensor average. The primitive is constructed
in each factor; no slice regularity, Fubini exceptional-set selection, or ae
constant premise is assumed. Tensor-density identification remains downstream. -/
namespace ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
open ImbalancedChen.Part3.WeakGradientCompactPrimitive20261026a
open ImbalancedChen.Part3.WeakDerivativeIntervalRigidity20261026a

abbrev openRectangle (a b c d : ℝ) : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo c d

def tensorTest (g h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := g p.1 * h p.2

def tensorPairing (Q : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℂ) (g h : ℝ → ℝ) : ℂ :=
  ∫ p in Q, tensorTest g h p • f p

theorem tensorTest_continuous {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) :
    Continuous (tensorTest g h) := (hg.comp continuous_fst).mul (hh.comp continuous_snd)

theorem tensorTest_hasCompactSupport {g h : ℝ → ℝ}
    (hg : HasCompactSupport g) (hh : HasCompactSupport h) : HasCompactSupport (tensorTest g h) := by
  apply HasCompactSupport.intro (hg.prod hh)
  intro p hp
  by_cases hx : p.1 ∈ tsupport g
  · have hy : p.2 ∉ tsupport h := fun hy => hp ⟨hx, hy⟩
    simp [tensorTest, image_eq_zero_of_notMem_tsupport hy]
  · simp [tensorTest, image_eq_zero_of_notMem_tsupport hx]

theorem integrable_tensor_pair {Q : Set (ℝ × ℝ)} {f : (ℝ × ℝ) → ℂ}
    (hf : IntegrableOn f Q) {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    Integrable (fun p => tensorTest g h p • f p) (volume.restrict Q) :=
  hf.smul_of_top_right ((tensorTest_continuous hg hh).memLp_top_of_hasCompactSupport
    (tensorTest_hasCompactSupport hgc hhc) (volume.restrict Q))

/-- The centered test has a primitive whose support remains in its interval. -/
theorem exists_centered_test_primitive {a b : ℝ} {g β : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo a b)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo a b)
    (hβi : (∫ x, β x) = 1) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo a b ∧
      deriv ψ = (fun x => g x - (∫ t, g t) * β x) := by
  let G : ℝ → ℝ := fun x => g x - (∫ t, g t) * β x
  have hG : ContDiff ℝ ∞ G := hg.sub (contDiff_const.mul hβ)
  have hGc : HasCompactSupport G := hgc.sub hβc.mul_left
  have hsupport : support G ⊆ tsupport g ∪ tsupport β := by
    intro x hx
    by_contra hnot
    have hg0 := image_eq_zero_of_notMem_tsupport (fun ht => hnot (Or.inl ht))
    have hb0 := image_eq_zero_of_notMem_tsupport (fun ht => hnot (Or.inr ht))
    exact hx (by simp [G, hg0, hb0])
  have hGs : tsupport G ⊆ Ioo a b :=
    (closure_minimal hsupport ((isClosed_tsupport g).union (isClosed_tsupport β))).trans
      (union_subset hgs hβs)
  have hgi := hg.continuous.integrable_of_hasCompactSupport hgc
  have hβint := hβ.continuous.integrable_of_hasCompactSupport hβc
  have hmean : (∫ x, G x) = 0 := by
    dsimp [G]
    rw [integral_sub hgi (hβint.const_mul _), integral_const_mul, hβi]
    simp
  exact exists_compact_primitive_on_interval hG hGc hGs hmean

theorem tensor_pairing_center_horizontal {a b c d : ℝ} {f : (ℝ × ℝ) → ℂ}
    (hf : IntegrableOn f (openRectangle a b c d))
    (hweak : ∀ ψ h : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f (deriv ψ) h = 0)
    {g β h : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo a b)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo a b)
    (hβi : (∫ x, β x) = 1)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) (hhs : tsupport h ⊆ Ioo c d) :
    tensorPairing (openRectangle a b c d) f g h =
      (∫ x, g x) • tensorPairing (openRectangle a b c d) f β h := by
  obtain ⟨ψ, hψ, hψc, hψs, hd⟩ := exists_centered_test_primitive hg hgc hgs hβ hβc hβs hβi
  have hz := hweak ψ h hψ hψc hψs hh hhc hhs
  rw [hd] at hz
  have hgh := integrable_tensor_pair hf hg.continuous hh.continuous hgc hhc
  have hβh := integrable_tensor_pair hf hβ.continuous hh.continuous hβc hhc
  have heq : (fun p => tensorTest (fun x => g x - (∫ t, g t) * β x) h p • f p) =
      (fun p => tensorTest g h p • f p - (∫ t, g t) • (tensorTest β h p • f p)) := by
    funext p
    simp only [tensorTest, sub_mul, sub_smul, mul_smul, mul_assoc]
  change (∫ p in openRectangle a b c d,
    tensorTest (fun x => g x - (∫ t, g t) * β x) h p • f p) = 0 at hz
  rw [heq, integral_sub hgh (hβh.smul _), integral_smul] at hz
  exact sub_eq_zero.mp hz

theorem tensor_pairing_center_vertical {a b c d : ℝ} {f : (ℝ × ℝ) → ℂ}
    (hf : IntegrableOn f (openRectangle a b c d))
    (hweak : ∀ g ψ : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f g (deriv ψ) = 0)
    {g h β : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo a b)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) (hhs : tsupport h ⊆ Ioo c d)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo c d)
    (hβi : (∫ x, β x) = 1) :
    tensorPairing (openRectangle a b c d) f g h =
      (∫ y, h y) • tensorPairing (openRectangle a b c d) f g β := by
  obtain ⟨ψ, hψ, hψc, hψs, hd⟩ := exists_centered_test_primitive hh hhc hhs hβ hβc hβs hβi
  have hz := hweak g ψ hg hgc hgs hψ hψc hψs
  rw [hd] at hz
  have hgh := integrable_tensor_pair hf hg.continuous hh.continuous hgc hhc
  have hgβ := integrable_tensor_pair hf hg.continuous hβ.continuous hgc hβc
  have heq : (fun p => tensorTest g (fun y => h y - (∫ t, h t) * β y) p • f p) =
      (fun p => tensorTest g h p • f p - (∫ t, h t) • (tensorTest g β p • f p)) := by
    funext p
    have hr : g p.1 * (h p.2 - (∫ t, h t) * β p.2) =
        g p.1 * h p.2 - (∫ t, h t) * (g p.1 * β p.2) := by ring
    simp only [tensorTest, hr, sub_smul, mul_smul]
  change (∫ p in openRectangle a b c d,
    tensorTest g (fun y => h y - (∫ t, h t) * β y) p • f p) = 0 at hz
  rw [heq, integral_sub hgh (hgβ.smul _), integral_smul] at hz
  exact sub_eq_zero.mp hz

/-- Both coordinate equations produce ONE scalar for all tensor tests.
This is stronger than independent constants chosen for individual slices. -/
theorem exists_common_tensor_average {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : (ℝ × ℝ) → ℂ} (hf : IntegrableOn f (openRectangle a b c d))
    (hweakX : ∀ ψ h : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f (deriv ψ) h = 0)
    (hweakY : ∀ g ψ : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f g (deriv ψ) = 0) :
    ∃ C : ℂ, ∀ g h : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f g h =
        ((∫ x, g x) * (∫ y, h y)) • C := by
  obtain ⟨β, hβ, hβc, hβs, hβi⟩ := exists_normalized_interval_bump hab
  obtain ⟨γ, hγ, hγc, hγs, hγi⟩ := exists_normalized_interval_bump hcd
  refine ⟨tensorPairing (openRectangle a b c d) f β γ, ?_⟩
  intro g h hg hgc hgs hh hhc hhs
  rw [tensor_pairing_center_horizontal hf hweakX hg hgc hgs hβ hβc hβs hβi hh hhc hhs,
    tensor_pairing_center_vertical hf hweakY hβ hβc hβs hh hhc hhs hγ hγc hγs hγi,
    mul_smul]

end
end ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a