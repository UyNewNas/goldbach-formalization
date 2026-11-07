import ImbalancedChen.Part3Gamma0ReducedSeedReconstruction
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.LocallyCompact

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Every vector in the ACTUAL reduced-carrier L2 space is approximated by a
continuous compactly supported function on H whose CLOSED support stays
inside that precise open reduced carrier. The pinned compact-continuous
Lp density theorem is applied to the actual subtype with the canonical
comap measure. Both local compactness and regularity are transported via
the actual open embedding, not supplied as density/approximation inputs.

Zero extension into H is proved continuous by compact-interior support;
restriction is exactly the original subtype function, so its true actual
reduced L2 distance is preserved. No unrestricted whole-H tensor density,
quotient approximation premise, or target hApprox is used. Tensorization
and the final actual quotient dense-core join are separate next steps.
-/

namespace ImbalancedChen.Part3.Gamma0ReducedContinuousApproximation20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ENNReal
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0ReducedSeedReconstruction20261025a

def carrierZeroExtend (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (z : UpperHalfPlane) : ℂ :=
  if hz : z ∈ reducedCarrier N then g ⟨z, hz⟩ else 0

@[simp] theorem carrierZeroExtend_projection (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (z : reducedCarrier N) :
    carrierZeroExtend N g z = g z := by
  simp only [carrierZeroExtend, dif_pos z.property]

theorem carrierZeroExtend_support_subset_image (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) :
    Function.support (carrierZeroExtend N g) ⊆
      (Subtype.val : reducedCarrier N → UpperHalfPlane) '' tsupport g := by
  intro z hz
  change carrierZeroExtend N g z ≠ 0 at hz
  by_cases hm : z ∈ reducedCarrier N
  · have hg : g ⟨z, hm⟩ ≠ 0 := by simpa only [carrierZeroExtend, dif_pos hm] using hz
    exact ⟨⟨z, hm⟩, subset_closure hg, rfl⟩
  · exact (hz (by simp only [carrierZeroExtend, dif_neg hm])).elim

theorem carrierZeroExtend_hasCompactSupport (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (carrierZeroExtend N g) := by
  have hK : IsCompact ((Subtype.val : reducedCarrier N → UpperHalfPlane) '' tsupport g) :=
    hg.image continuous_subtype_val
  apply hK.of_isClosed_subset isClosed_closure
  exact closure_minimal (carrierZeroExtend_support_subset_image N g) hK.isClosed

/-- The CLOSED support, not merely the nonzero set, is confined to the
actual open carrier. This is the compact-interior support needed later. -/
theorem carrierZeroExtend_tsupport_subset (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (hg : HasCompactSupport g) :
    tsupport (carrierZeroExtend N g) ⊆ reducedCarrier N := by
  have hK : IsCompact ((Subtype.val : reducedCarrier N → UpperHalfPlane) '' tsupport g) :=
    hg.image continuous_subtype_val
  apply (closure_minimal (carrierZeroExtend_support_subset_image N g) hK.isClosed).trans
  rintro z ⟨x, _hx, rfl⟩
  exact x.property

/-- Genuine continuity of zero extension: on the open carrier it is the
given subtype function, and outside its compact interior support it has a
whole neighborhood on which it vanishes. -/
theorem carrierZeroExtend_continuous (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (hcont : Continuous g) (hg : HasCompactSupport g) :
    Continuous (carrierZeroExtend N g) := by
  have hOn : ContinuousOn (carrierZeroExtend N g) (reducedCarrier N) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : reducedCarrier N => carrierZeroExtend N g x)
    simpa only [carrierZeroExtend_projection] using hcont
  have hK : IsCompact ((Subtype.val : reducedCarrier N → UpperHalfPlane) '' tsupport g) :=
    hg.image continuous_subtype_val
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ reducedCarrier N
  · exact (hOn z hz).continuousAt ((reducedCarrier_isOpen N).mem_nhds hz)
  · have hzK : z ∉ (Subtype.val : reducedCarrier N → UpperHalfPlane) '' tsupport g := by
      rintro ⟨x, _hx, hxz⟩
      exact hz (hxz ▸ x.property)
    have heq : carrierZeroExtend N g =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
      by_contra hnonzero
      exact hw (carrierZeroExtend_support_subset_image N g hnonzero)
    exact continuousAt_const.congr_of_eventuallyEq heq

def reducedFunctionL2 (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : MemLp (fun z : reducedCarrier N => f z) 2 (reducedCarrierMeasure N)) :
    Lp ℂ 2 (reducedCarrierMeasure N) := hf.toLp (fun z : reducedCarrier N => f z)

/-- Arbitrary actual reduced-carrier L2 vectors have actual H continuous
compact-interior approximants, with their genuine reduced L2 distance. -/
theorem exists_continuous_compact_inside_reduced_approx
    (N : ℕ) [NeZero N] (F : Lp ℂ 2 (reducedCarrierMeasure N))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ f : UpperHalfPlane → ℂ,
      Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ reducedCarrier N ∧
      ∃ hf : MemLp (fun z : reducedCarrier N => f z) 2 (reducedCarrierMeasure N),
        dist F (reducedFunctionL2 N f hf) < epsilon := by
  letI : LocallyCompactSpace (reducedCarrier N) :=
    (reducedCarrier_isOpen N).isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI : (reducedCarrierMeasure N).Regular := by
    change ((volume : Measure UpperHalfPlane).comap
      (Subtype.val : reducedCarrier N → UpperHalfPlane)).Regular
    exact Measure.Regular.comap' (volume : Measure UpperHalfPlane)
      (reducedCarrier_isOpen N).isOpenEmbedding_subtypeVal
  have hhalf : (ENNReal.ofReal (epsilon / 2) : ℝ≥0∞) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (half_pos hepsilon)).ne'
  obtain ⟨g, hgc, happrox, hgcont, hgmem⟩ :=
    F.memLp.exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hhalf
  let f : UpperHalfPlane → ℂ := carrierZeroExtend N g
  have hfmem : MemLp (fun z : reducedCarrier N => f z) 2 (reducedCarrierMeasure N) := by
    simpa only [f, carrierZeroExtend_projection] using hgmem
  refine ⟨f, carrierZeroExtend_continuous N g hgcont hgc,
    carrierZeroExtend_hasCompactSupport N g hgc,
    carrierZeroExtend_tsupport_subset N g hgc, hfmem, ?_⟩
  have hLp : reducedFunctionL2 N f hfmem = hgmem.toLp g := by
    apply MemLp.toLp_congr hfmem hgmem
    exact Filter.Eventually.of_forall (carrierZeroExtend_projection N g)
  rw [hLp]
  have hed : edist F (hgmem.toLp g) ≤ ENNReal.ofReal (epsilon / 2) := by
    have heq := Lp.edist_toLp_toLp (F : reducedCarrier N → ℂ) g F.memLp hgmem
    rw [Lp.toLp_coeFn] at heq
    exact heq.trans_le happrox
  have hd := ENNReal.toReal_mono (by simp : ENNReal.ofReal (epsilon / 2) ≠ ∞) hed
  rw [← Lp.dist_edist, ENNReal.toReal_ofReal (half_pos hepsilon).le] at hd
  exact hd.trans_lt (by linarith)

end
end ImbalancedChen.Part3.Gamma0ReducedContinuousApproximation20261025a
