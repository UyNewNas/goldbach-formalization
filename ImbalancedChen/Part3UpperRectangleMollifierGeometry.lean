import ImbalancedChen.Part3NestedRectangleRealCutoff

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual compact upper-half-plane rectangles and a proved common mollifier
tail for every point in the support of the explicit nested cutoff.
No reduced-carrier, orbit-seam, or analytic regularity premise occurs. -/

namespace ImbalancedChen.Part3.UpperRectangleMollifierGeometry20261026b
noncomputable section
open Set Filter
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0TranslatedProductWeakPDE20261026a Gamma0CompactDefectMollifier20261026a
open NestedRectangleRealCutoff20261026b

def upperRectangle (L R a b : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc L R ∧ z.im ∈ Icc a b}

theorem upperRectangle_isCompact (L R a b : ℝ) (ha : 0 < a) :
    IsCompact (upperRectangle L R a b) := by
  let lift : Plane → UpperHalfPlane := fun p =>
    ⟨⟨p.1, max a p.2⟩, ha.trans_le (le_max_left _ _)⟩
  have hc : Continuous lift := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun p : Plane => (⟨p.1, max a p.2⟩ : ℂ))
    fun_prop
  have he : lift '' (Icc L R ×ˢ Icc a b) = upperRectangle L R a b := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change p.1 ∈ Icc L R ∧ max a p.2 ∈ Icc a b
      rw [max_eq_right hp.2.1]
      exact hp
    · intro hz
      refine ⟨(z.re, z.im), hz, ?_⟩
      apply UpperHalfPlane.coe_injective
      apply Complex.ext
      · rfl
      · change max a z.im = z.im
        exact max_eq_right hz.2.1
  rw [← he]
  exact (isCompact_Icc.prod isCompact_Icc).image hc

theorem upperRectangle_height (L R a b : ℝ) {z : UpperHalfPlane}
    (hz : z ∈ upperRectangle L R a b) : a ≤ z.im ∧ z.im ≤ b := hz.2

/-- One common tail works on the entire compact cutoff support. The
outer rectangle has twice the cutoff margin; the lower height stays
strictly positive. There is no premise asking callers to provide n₀. -/
theorem exists_rectangle_mollifier_tail
    (L R c d δ : ℝ) (hLR : L ≤ R) (hcd : c ≤ d)
    (hδ : 0 < δ) (hmargin : 2 * δ < c) :
    ∃ n₀ : ℕ, ∀ n : ℕ,
      (∀ p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ),
        mollifierRadius (n + n₀) < p.2) ∧
      (∀ p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ),
        productRectangle (n + n₀) p.1 p.2 ⊆
          upperRectangle (L - 2*δ) (R + 2*δ) (c - 2*δ) (d + 2*δ)) := by
  have ht : Tendsto mollifierRadius atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : ∀ᶠ m in atTop, mollifierRadius m < δ :=
    ht.eventually (gt_mem_nhds hδ)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp he
  refine ⟨n₀, fun n => ?_⟩
  have hr := hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  have hs := rectangleCutoff_support L R c d δ hLR hcd hδ
  constructor
  · intro p hp
    have hy := (hs hp).2.1
    linarith
  · intro p hp z hz
    have hp' := hs hp
    change (L - δ < p.1 ∧ p.1 < R + δ) ∧
      (c - δ < p.2 ∧ p.2 < d + δ) at hp'
    change (p.1 - mollifierRadius (n + n₀) ≤ z.re ∧
      z.re ≤ p.1 + mollifierRadius (n + n₀)) ∧
      (p.2 - mollifierRadius (n + n₀) ≤ z.im ∧
        z.im ≤ p.2 + mollifierRadius (n + n₀)) at hz
    change (L - 2*δ ≤ z.re ∧ z.re ≤ R + 2*δ) ∧
      (c - 2*δ ≤ z.im ∧ z.im ≤ d + 2*δ)
    constructor <;> constructor <;>
      linarith [hp'.1.1, hp'.1.2, hp'.2.1, hp'.2.2, hz.1.1, hz.1.2, hz.2.1, hz.2.2]

end
end ImbalancedChen.Part3.UpperRectangleMollifierGeometry20261026b
