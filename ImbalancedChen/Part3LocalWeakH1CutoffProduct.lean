import ImbalancedChen.Part3LocalH1SecondOrderWeakPDEExtension
import ImbalancedChen.Part3PlanarLocalWeakGradientExtraction

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine local L2 weak gradient gives a GLOBAL compact H1 product after
multiplication by a compact smooth cutoff supported in the local region.
Both Leibniz derivatives, their L2 membership and their compact supports
are proved. Local weak gradients are never silently treated as global.
-/
namespace ImbalancedChen.Part3.LocalWeakH1CutoffProduct20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CompactC2ProductMollifier20261026a
open CompactC2JetCutoffEstimate20261026a
open WeakH1ProductMollifierDerivative20261026a
open PlanarLocalWeakGradientExtraction20261026b

/-- Compact continuous scalar multiplication preserves actual planar L2. -/
theorem compact_multiplier_memLp {χ F : Plane → ℂ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hF : MemLp F 2 volume) :
    MemLp (fun p => χ p * F p) 2 volume := by
  obtain ⟨C,hC⟩ := hχc.exists_bound_of_continuous hχ
  apply hF.of_le_mul (hχ.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC p) (norm_nonneg _)

def productDerivative (χ F g : Plane → ℂ) (v : Plane) (p : Plane) : ℂ :=
  directional v χ p * F p + χ p * g p

theorem productDerivative_memLp {χ F g : Plane → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hF : MemLp F 2 volume) (hg : MemLp g 2 volume) (v : Plane) :
    MemLp (productDerivative χ F g v) 2 volume :=
  (compact_multiplier_memLp (directional_smooth v hχ).continuous
    (directional_compact v hχc) hF).add
      (compact_multiplier_memLp hχ.continuous hχc hg)

theorem productDerivative_tsupport {χ F g : Plane → ℂ} (v : Plane) :
    tsupport (productDerivative χ F g v) ⊆ tsupport χ := by
  apply closure_minimal ?_ isClosed_tsupport
  intro p hp
  by_contra hn
  have hχp := image_eq_zero_of_notMem_tsupport hn
  have hdp : directional v χ p = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hn (tsupport_fderiv_apply_subset ℝ v h))
  exact hp (by simp only [productDerivative, hχp, hdp, zero_mul, add_zero])

/-- A local SESQUILINEAR weak derivative gives the global BILINEAR weak
Leibniz rule after compact multiplication. All integrals are L1 products. -/
theorem local_weak_product {Ω : Set Plane} {F g χ : Plane → ℂ} (v : Plane)
    (hF : MemLp F 2 volume) (hg : MemLp g 2 volume)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hweak : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∫ p, star (ψ p) * g p) =
        -(∫ p, star (directional v ψ p) * F p)) :
    HasWeakDirectionalDerivative (fun p => χ p * F p) (productDerivative χ F g v) v := by
  intro ψ hψ hψc
  let P : Plane → ℂ := fun p => χ p * ψ p
  have hP : ContDiff ℝ ∞ P := hχ.mul hψ
  have hPc : HasCompactSupport P := hχc.mul_right
  have hstar : directional v (fun p => star (P p)) = fun p => star (directional v P p) := by
    funext p
    simp [directional, fderiv_star]
  have hPΩ : tsupport (fun p => star (P p)) ⊆ Ω :=
    (tsupport_comp_subset (g := star) (by simp) P).trans
      (tsupport_mul_subset_left.trans hχΩ)
  have hw := hweak (fun p => star (P p)) hP.star
    (hPc.comp_left (g := star) (by simp)) hPΩ
  simp only [hstar, star_star] at hw
  have hDP : directional v P = fun p => directional v χ p * ψ p + χ p * directional v ψ p :=
    directional_mul v hχ hψ
  let A := ∫ p, χ p * directional v ψ p * F p
  let B := ∫ p, directional v χ p * ψ p * F p
  let C := ∫ p, χ p * ψ p * g p
  have hA : Integrable (fun p => χ p * directional v ψ p * F p) volume :=
    MemLp.integrable_mul (p := 2) (q := 2)
      ((hχ.mul (directional_smooth v hψ)).continuous.memLp_of_hasCompactSupport hχc.mul_right) hF
  have hB : Integrable (fun p => directional v χ p * ψ p * F p) volume :=
    MemLp.integrable_mul (p := 2) (q := 2)
      (((directional_smooth v hχ).mul hψ).continuous.memLp_of_hasCompactSupport
        (directional_compact v hχc).mul_right) hF
  have hC : Integrable (fun p => χ p * ψ p * g p) volume :=
    MemLp.integrable_mul (p := 2) (q := 2)
      (hP.continuous.memLp_of_hasCompactSupport hPc) hg
  have hsplit : (∫ p, directional v P p * F p) = B + A := by
    rw [hDP]
    calc
      _ = ∫ p, directional v χ p * ψ p * F p + χ p * directional v ψ p * F p := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by ring
      _ = _ := integral_add hB hA
  have hrel : C = -(B + A) := by simpa only [P, hsplit] using hw
  have hleft : (∫ p, directional v ψ p * (χ p * F p)) = A := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  have hright : (∫ p, ψ p * productDerivative χ F g v p) = B + C := by
    calc
      _ = ∫ p, directional v χ p * ψ p * F p + χ p * ψ p * g p := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by simp only [productDerivative]; ring
      _ = _ := integral_add hB hC
  rw [hleft,hright]
  linear_combination -hrel

/-- Honest compact H1 Leibniz jet. This constructor uses actual LOCAL
weak identities only where the multiplier lives. -/
def cutoffJet {Ω : Set Plane} {F χ : Plane → ℂ}
    (hF : MemLp F 2 volume) (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p))) :
    CompactH1Jet where
  value p := χ p * F p
  dx := productDerivative χ F gx ex
  dy := productDerivative χ F gy ey
  value_memLp := compact_multiplier_memLp hχ.continuous hχc hF
  dx_memLp := productDerivative_memLp hχ hχc hF (Lp.memLp gx) ex
  dy_memLp := productDerivative_memLp hχ hχc hF (Lp.memLp gy) ey
  value_compact := hχc.mul_right
  weak_dx := local_weak_product ex hF (Lp.memLp gx) hχ hχc hχΩ
    (fun ψ hψ hc hs => (hgrad ψ hψ hc hs).1)
  weak_dy := local_weak_product ey hF (Lp.memLp gy) hχ hχc hχΩ
    (fun ψ hψ hc hs => (hgrad ψ hψ hc hs).2)

theorem cutoffJet_supports {Ω : Set Plane} {F χ : Plane → ℂ}
    (hF : MemLp F 2 volume) (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p))) :
    tsupport (cutoffJet hF gx gy hχ hχc hχΩ hgrad).value ⊆ tsupport χ ∧
    tsupport (cutoffJet hF gx gy hχ hχc hχΩ hgrad).dx ⊆ tsupport χ ∧
    tsupport (cutoffJet hF gx gy hχ hχc hχΩ hgrad).dy ⊆ tsupport χ :=
  ⟨tsupport_mul_subset_left, productDerivative_tsupport ex, productDerivative_tsupport ey⟩

/-- Existence from the installed weak-limit interface, preserving the
literal product and both compact weak derivatives. -/
theorem exists_compact_cutoff_H1Jet {Ω : Set Plane} {F χ : Plane → ℂ}
    (hF : HasLocalL2GradientOn Ω F) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    ∃ J : CompactH1Jet, J.value = (fun p => χ p * F p) ∧
      tsupport J.dx ⊆ tsupport χ ∧ tsupport J.dy ⊆ tsupport χ := by
  obtain ⟨hF,gx,gy,hgrad⟩ := hF
  have hg : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p)) := hgrad
  exact ⟨cutoffJet hF gx gy hχ hχc hχΩ hg, rfl,
    (cutoffJet_supports hF gx gy hχ hχc hχΩ hg).2.1,
    (cutoffJet_supports hF gx gy hχ hχc hχΩ hg).2.2⟩

end
end ImbalancedChen.Part3.LocalWeakH1CutoffProduct20261026b
