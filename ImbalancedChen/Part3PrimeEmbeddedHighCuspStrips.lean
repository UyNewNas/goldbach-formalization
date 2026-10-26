import ImbalancedChen.Part3PrimeHighCuspQuotientSeparation
import ImbalancedChen.Part3ActualParabolicHighSeedLocalFinite

/-! Exact half-open high-strip charts in the genuine Gamma0 quotient.
Their injectivity comes from the actual parabolic-deck classification;
integer translation supplies every high neighborhood point. Thus each
chart is a literal set embedding and a bijection onto its neighborhood,
and the two ranges are disjoint. No topological embedding or measure
transport is assumed or asserted. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Set
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.ActualParabolicHighSeedLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b

namespace ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b

def strictHighStrip (Y : ℝ) : Set UpperHalfPlane := strip ∩ strictHeightHalfSpace Y

theorem infinity_high_strip_injOn (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    InjOn (orbitProjection N) (strictHighStrip Y) := by
  intro z hz w hw he
  obtain ⟨k, hk⟩ := (high_projection_eq_iff_translation N Y hY z w hz.2 hw.2).mp he
  apply infinityProjection_injOn_strip N hz.1 hw.1
  rw [hk, infinityProjection_translate]

theorem zero_high_strip_injOn {p : ℕ} (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    InjOn (fun z : UpperHalfPlane => orbitProjection p (frickeSL p hp.pos • z))
      (strictHighStrip Y) := by
  intro z hz w hw he
  obtain ⟨k, hk⟩ :=
    (fricke_high_projection_eq_iff_translation p hp.pos Y hY z w hz.2 hw.2).mp he
  apply infinityProjection_injOn_strip p hz.1 hw.1
  rw [hk, infinityProjection_translate]

theorem infinity_high_strip_surjective (N : ℕ) (Y : ℝ)
    (q : Gamma0OrbitSpace N) (hq : q ∈ infinityHighNeighborhood N Y) :
    ∃ z ∈ strictHighStrip Y, orbitProjection N z = q := by
  obtain ⟨w, hw, rfl⟩ := hq
  obtain ⟨k, hk, hu⟩ := unique_translate_mem_strip w
  refine ⟨translate k w, ⟨hk, ?_⟩, ?_⟩
  · change Y < (translate k w).im
    rw [translate_im]
    exact hw
  · exact orbitProjection_smul N (translationGamma N k) w

theorem zero_high_strip_surjective {p : ℕ} (hp : p.Prime) (Y : ℝ)
    (q : Gamma0OrbitSpace p) (hq : q ∈ zeroHighNeighborhood p hp Y) :
    ∃ z ∈ strictHighStrip Y, orbitProjection p (frickeSL p hp.pos • z) = q := by
  obtain ⟨w, hw, rfl⟩ := hq
  obtain ⟨k, hk, hu⟩ := unique_translate_mem_strip w
  refine ⟨translate k w, ⟨hk, ?_⟩, ?_⟩
  · change Y < (translate k w).im
    rw [translate_im]
    exact hw
  · have he := congrArg (quotientFricke p hp.pos)
      (orbitProjection_smul p (translationGamma p k) w)
    simpa only [translationGamma_smul, quotientFricke_projection] using he

def infinityHighStripEmbedding (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    {z : UpperHalfPlane // z ∈ strictHighStrip Y} ↪ Gamma0OrbitSpace N where
  toFun z := orbitProjection N z.1
  inj' := by
    intro z w he
    apply Subtype.ext
    exact infinity_high_strip_injOn N Y hY z.property w.property he

def zeroHighStripEmbedding (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    {z : UpperHalfPlane // z ∈ strictHighStrip Y} ↪ Gamma0OrbitSpace p where
  toFun z := orbitProjection p (frickeSL p hp.pos • z.1)
  inj' := by
    intro z w he
    apply Subtype.ext
    exact zero_high_strip_injOn hp Y hY z.property w.property he

/-- Actual bijective normalized infinity coordinates, with the literal
half-open period interval retained and no boundary removed as null. -/
def infinityHighStripEquiv (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    {z : UpperHalfPlane // z ∈ strictHighStrip Y} ≃ infinityHighNeighborhood N Y :=
  Equiv.ofBijective (fun z => ⟨orbitProjection N z.1, ⟨z.1, z.property.2, rfl⟩⟩) (by
    constructor
    · intro z w he
      apply Subtype.ext
      exact infinity_high_strip_injOn N Y hY z.property w.property (congrArg Subtype.val he)
    · intro q
      obtain ⟨z, hz, he⟩ := infinity_high_strip_surjective N Y q.1 q.property
      refine ⟨⟨z, hz⟩, ?_⟩
      exact Subtype.ext he)

/-- Actual bijective unit-period Fricke-zero coordinates, with the true
normalized scaling and the same strict height threshold. -/
def zeroHighStripEquiv (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    {z : UpperHalfPlane // z ∈ strictHighStrip Y} ≃ zeroHighNeighborhood p hp Y :=
  Equiv.ofBijective
    (fun z => ⟨orbitProjection p (frickeSL p hp.pos • z.1), ⟨z.1, z.property.2, rfl⟩⟩) (by
      constructor
      · intro z w he
        apply Subtype.ext
        exact zero_high_strip_injOn hp Y hY z.property w.property (congrArg Subtype.val he)
      · intro q
        obtain ⟨z, hz, he⟩ := zero_high_strip_surjective hp Y q.1 q.property
        refine ⟨⟨z, hz⟩, ?_⟩
        exact Subtype.ext he)

theorem high_strip_embedding_ranges_disjoint {p : ℕ} (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    Disjoint (Set.range (infinityHighStripEmbedding p Y hY))
      (Set.range (zeroHighStripEmbedding p hp Y hY)) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z, rfl⟩ ⟨w, he⟩
  exact high_cross_projection_ne hp Y hY z.1 w.1 z.property.2 w.property.2 he.symm

end ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b
