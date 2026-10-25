import ImbalancedChen.Part3Gamma0CompactUpperChartExtension
import ImbalancedChen.Part3CanonicalPlanarL2Unitary

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The weighted planar approximation is connected to the ACTUAL canonical
hyperbolic L2 norm by the existing proved spatial unitary, and restriction
to the ACTUAL reduced subtype is proved contractive using its canonical
comap measure. No norm identification or isometry is a supplied premise.
The measure remains dx dy/y^2; no spectral measure enters this module.
-/

namespace ImbalancedChen.Part3.Gamma0CanonicalWeightedNormJoin20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0LocalWeightedTensorApproximation20261025a

theorem forwardFunction_eq_divide_extend (f : UpperHalfPlane→ℂ) :
    forwardFunction f=divideByHeight (extendUpper f) := by
  funext p
  by_cases hp : 0<p.2
  · simp only [forwardFunction,unweightChart,chartPullback,upperChart,
      Set.mem_setOf_eq,hp,dif_pos,extendUpper,divideByHeight,
      Real.smul_def,Complex.real_smul]
  · simp only [forwardFunction,unweightChart,upperChart,Set.mem_setOf_eq,
      hp,dif_neg,extendUpper,divideByHeight,mul_zero]

/-- The actual canonical norm, rather than a proposed weighted norm. -/
theorem canonical_toLp_norm_eq_weighted (f : UpperHalfPlane→ℂ)
    (hf : MemLp f 2 (volume : Measure UpperHalfPlane)) :
    ‖hf.toLp f‖=(eLpNorm (divideByHeight (extendUpper f)) 2
      (volume : Measure (ℝ×ℝ))).toReal := by
  have hp := forwardFunction_memLp hf
  have heq : forwardL2 (hf.toLp f)=hp.toLp (forwardFunction f) := by
    unfold forwardL2
    apply MemLp.toLp_congr
    exact forwardFunction_congr_ae hf.coeFn_toLp
  calc
    _ = ‖forwardL2 (hf.toLp f)‖ := (forwardL2_norm (hf.toLp f)).symm
    _ = ‖hp.toLp (forwardFunction f)‖ := congrArg norm heq
    _ = (eLpNorm (forwardFunction f) 2 (volume : Measure (ℝ×ℝ))).toReal :=
      Lp.norm_toLp _ _
    _ = _ := by rw [forwardFunction_eq_divide_extend]

theorem extendUpper_sub (f g : UpperHalfPlane→ℂ) :
    extendUpper (f-g)=extendUpper f-extendUpper g := by
  funext p
  by_cases hp : 0<p.2 <;> simp only [extendUpper,hp,dif_pos,dif_neg,Pi.sub_apply,sub_self]

theorem canonical_toLp_dist_eq_weighted (f g : UpperHalfPlane→ℂ)
    (hf : MemLp f 2 (volume : Measure UpperHalfPlane))
    (hg : MemLp g 2 (volume : Measure UpperHalfPlane)) :
    dist (hf.toLp f) (hg.toLp g)=
      (eLpNorm (divideByHeight (extendUpper f-extendUpper g)) 2
        (volume : Measure (ℝ×ℝ))).toReal := by
  rw [dist_eq_norm,← MemLp.toLp_sub hf hg,
    canonical_toLp_norm_eq_weighted (f-g) (hf.sub hg),extendUpper_sub]

/-- The literal subtype inclusion preserves the canonical restricted
measure. This is derived from the actual reduced-carrier measurability. -/
theorem reducedInclusion_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (Subtype.val : reducedCarrier N→UpperHalfPlane)
      (reducedCarrierMeasure N) ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) := by
  refine ⟨measurable_subtype_coe,?_⟩
  exact Measure.map_comap_subtype_coe (reducedCarrier_measurable N)

theorem memLp_restrict_reduced (N : ℕ) [NeZero N] (f : UpperHalfPlane→ℂ)
    (hf : MemLp f 2 (volume : Measure UpperHalfPlane)) :
    MemLp (fun z : reducedCarrier N => f z) 2 (reducedCarrierMeasure N) :=
  (hf.mono_measure Measure.restrict_le_self).comp_measurePreserving
    (reducedInclusion_measurePreserving N)

/-- Restriction to the actual representative subtype cannot enlarge the
canonical L2 distance. Both classes use their genuine toLp definitions. -/
theorem reduced_toLp_dist_le_canonical (N : ℕ) [NeZero N]
    (f g : UpperHalfPlane→ℂ)
    (hf : MemLp f 2 (volume : Measure UpperHalfPlane))
    (hg : MemLp g 2 (volume : Measure UpperHalfPlane))
    (hfr : MemLp (fun z : reducedCarrier N => f z) 2 (reducedCarrierMeasure N))
    (hgr : MemLp (fun z : reducedCarrier N => g z) 2 (reducedCarrierMeasure N)) :
    dist (hfr.toLp (fun z => f z)) (hgr.toLp (fun z => g z)) ≤
      dist (hf.toLp f) (hg.toLp g) := by
  have heq := eLpNorm_comp_measurePreserving
    ((hf.sub hg).mono_measure Measure.restrict_le_self).aestronglyMeasurable
    (reducedInclusion_measurePreserving N)
  have hred : dist (hfr.toLp (fun z => f z)) (hgr.toLp (fun z => g z)) =
      (eLpNorm ((f-g)∘(Subtype.val : reducedCarrier N→UpperHalfPlane)) 2
        (reducedCarrierMeasure N)).toReal := by
    rw [Lp.dist_edist,Lp.edist_toLp_toLp]
    rfl
  have hfull : dist (hf.toLp f) (hg.toLp g)=
      (eLpNorm (f-g) 2 (volume : Measure UpperHalfPlane)).toReal := by
    rw [Lp.dist_edist,Lp.edist_toLp_toLp]
  rw [hred,hfull,heq]
  exact ENNReal.toReal_mono (hf.sub hg).eLpNorm_ne_top
    (eLpNorm_mono_measure (f-g) Measure.restrict_le_self)

end
end ImbalancedChen.Part3.Gamma0CanonicalWeightedNormJoin20261025a
