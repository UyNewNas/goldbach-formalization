import ImbalancedChen.Part3GenericRealBorelNonrealResolvent

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
For arbitrary measurable real m, the actual bounded reciprocal Borel map
is the genuine two-sided inverse of the native unbounded A_m-z on its
ENTIRE domain, for every nonreal z. Domain membership and graph/action
identities are proved from actual spectral representatives.
-/

namespace ImbalancedChen.Part3.GenericRealBorelNonrealNativeInverse20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericUnboundedRealBorelCalculus20261025a
open ImbalancedChen.Part3.GenericRealBorelNonrealResolvent20261025a

private theorem reciprocal_right_scalar (x : ℝ) (z a : ℂ) (hz : z.im ≠ 0) :
    a + z * (((x : ℂ)-z)⁻¹*a) = (x : ℂ) * (((x : ℂ)-z)⁻¹*a) := by
  have hn := real_sub_nonreal_ne_zero x z hz
  calc
    _ = (((x : ℂ)-z)*((x : ℂ)-z)⁻¹)*a + z*(((x : ℂ)-z)⁻¹*a) := by
      rw [mul_inv_cancel₀ hn, one_mul]
    _ = _ := by ring

private theorem reciprocal_left_scalar (x : ℝ) (z a : ℂ) (hz : z.im ≠ 0) :
    ((x : ℂ)-z)⁻¹*((x : ℂ)*a-z*a) = a := by
  rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (real_sub_nonreal_ne_zero x z hz), one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
variable (m : ResolventSpectrum R → ℝ) (hm : Measurable m)

/-- The reciprocal map sends every vector into the full native domain,
with A_m(S_z f)=f+z S_z f. -/
theorem nonrealResolvent_native_graph (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    (nonrealResolvent R hSA m hm z hz f,
      f + z • nonrealResolvent R hSA m hm z hz f) ∈ (unboundedRealBorel R hSA m hm).graph := by
  apply (unboundedRealBorel_mem_graph_iff R hSA m hm _ _).mpr
  intro i
  let ξ := (spectralUnitary R hSA).symm f
  let η := (spectralUnitary R hSA).symm (nonrealResolvent R hSA m hm z hz f)
  have hcoord : ((spectralUnitary R hSA).symm
      (f + z • nonrealResolvent R hSA m hm z hz f)) i = ξ i + z • η i := by
    simp only [ξ, η, map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply]
  rw [hcoord]
  have hq := nonrealResolvent_coordinates_ae R hSA m hm z hz f i
  change η i =ᵐ[scalarMeasure R hSA (i : H)]
    (fun t => ((m t : ℂ)-z)⁻¹ * ξ i t) at hq
  filter_upwards [hq, Lp.coeFn_add (ξ i) (z • η i), Lp.coeFn_smul z (η i)] with t hqt ha hs
  change (ξ i + z • η i) t = (m t : ℂ) * η i t
  rw [ha, hs, hqt]
  exact reciprocal_right_scalar (m t) z (ξ i t) hz

def nonrealResolventDomainPoint (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    (unboundedRealBorel R hSA m hm).domain :=
  ⟨nonrealResolvent R hSA m hm z hz f,
    LinearPMap.mem_domain_of_mem_graph (nonrealResolvent_native_graph R hSA m hm z hz f)⟩

theorem nonrealResolvent_native_action (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    unboundedRealBorel R hSA m hm (nonrealResolventDomainPoint R hSA m hm z hz f) =
      f + z • nonrealResolvent R hSA m hm z hz f :=
  LinearPMap.mem_graph_snd_inj _ (LinearPMap.mem_graph _ _)
    (nonrealResolvent_native_graph R hSA m hm z hz f) rfl

theorem nonrealResolvent_right_inverse (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    unboundedRealBorel R hSA m hm (nonrealResolventDomainPoint R hSA m hm z hz f) -
      z • (nonrealResolventDomainPoint R hSA m hm z hz f : H) = f := by
  rw [nonrealResolvent_native_action]
  change f + z • nonrealResolvent R hSA m hm z hz f - z • nonrealResolvent R hSA m hm z hz f = f
  abel

/-- The inverse identity holds for every point of the maximal native
domain, without any extra integrability or core-membership hypothesis. -/
theorem nonrealResolvent_left_inverse (z : ℂ) (hz : z.im ≠ 0)
    (u : (unboundedRealBorel R hSA m hm).domain) :
    nonrealResolvent R hSA m hm z hz (unboundedRealBorel R hSA m hm u - z • (u : H)) = (u : H) := by
  apply (spectralUnitary R hSA).symm.injective
  ext i
  apply Lp.ext
  let ξ := (spectralUnitary R hSA).symm (u : H)
  let η := (spectralUnitary R hSA).symm (unboundedRealBorel R hSA m hm u)
  have hcoord : ((spectralUnitary R hSA).symm
      (unboundedRealBorel R hSA m hm u - z • (u : H))) i = η i - z • ξ i := by
    simp only [ξ, η, map_sub, map_smul, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply]
  have hq := nonrealResolvent_coordinates_ae R hSA m hm z hz
    (unboundedRealBorel R hSA m hm u - z • (u : H)) i
  rw [hcoord] at hq
  have hu := unboundedRealBorel_action_ae R hSA m hm u i
  change η i =ᵐ[scalarMeasure R hSA (i : H)] (fun t => (m t : ℂ) * ξ i t) at hu
  filter_upwards [hq, hu, Lp.coeFn_sub (η i) (z • ξ i), Lp.coeFn_smul z (ξ i)] with t hqt hut hs hmz
  rw [hqt, hs, hmz, hut]
  exact reciprocal_left_scalar (m t) z (ξ i t) hz

/-- Native shift A_m-z is bijective from its full domain to H. -/
theorem nonreal_native_shift_bijective (z : ℂ) (hz : z.im ≠ 0) :
    Function.Bijective (fun u : (unboundedRealBorel R hSA m hm).domain =>
      unboundedRealBorel R hSA m hm u - z • (u : H)) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    have h := congrArg (nonrealResolvent R hSA m hm z hz) huv
    simpa only [nonrealResolvent_left_inverse R hSA m hm z hz] using h
  · intro f
    exact ⟨nonrealResolventDomainPoint R hSA m hm z hz f,
      nonrealResolvent_right_inverse R hSA m hm z hz f⟩

/-- The range of the actual bounded reciprocal map is exactly the
maximal native unbounded domain, not just a dense subspace of it. -/
theorem nonrealResolvent_range_eq_domain (z : ℂ) (hz : z.im ≠ 0) :
    Set.range (nonrealResolvent R hSA m hm z hz) = ((unboundedRealBorel R hSA m hm).domain : Set H) := by
  ext u
  constructor
  · rintro ⟨f, rfl⟩
    exact (nonrealResolventDomainPoint R hSA m hm z hz f).property
  · intro hu
    exact ⟨unboundedRealBorel R hSA m hm ⟨u,hu⟩ - z • u,
      nonrealResolvent_left_inverse R hSA m hm z hz ⟨u,hu⟩⟩

end
end ImbalancedChen.Part3.GenericRealBorelNonrealNativeInverse20261025a
