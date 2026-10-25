import ImbalancedChen.Part3GenericUnboundedRealBorelCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The arbitrary real Borel operator agrees with the total bounded calculus
whenever its symbol is bounded. Its shifts by either square root of -1
have explicit bounded two-sided inverses C-zB, proved on the full native
domain. These are operator/domain statements, not formal pointwise aliases.
-/

namespace ImbalancedChen.Part3.GenericUnboundedRealBorelResolvent20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.InjectiveSelfAdjointPartialInverse20261025a
open ImbalancedChen.Part3.NormalizedBoundedPairOperator20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a
open ImbalancedChen.Part3.GenericUnboundedRealBorelCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
variable (m : ResolventSpectrum R → ℝ) (hm : Measurable m)

/-- Equality of native partial maps includes equality of their domains. -/
theorem unbounded_eq_bounded (φ : BoundedBorelFunction (ResolventSpectrum R))
    (hφ : ∀ t, φ t = (m t : ℂ)) :
    unboundedRealBorel R hSA m hm = (borelFunctionalCalculus R hSA φ).toPMap ⊤ := by
  apply LinearPMap.eq_of_eq_graph
  apply SetLike.ext
  rintro ⟨u,v⟩
  rw [unboundedRealBorel_mem_graph_iff, totalR_mem_graph_iff]
  have h := calculus_pair_eq_iff R hSA (BoundedBorelFunction.const 1) φ u v
  simp only [borelFunctionalCalculus_const, one_smul, ContinuousLinearMap.id_apply,
    BoundedBorelFunction.const, one_mul, hφ] at h
  exact h.symm.trans eq_comm

/-- The explicit bounded inverse for A+z when z^2=-1. -/
def imaginaryResolvent (z : ℂ) : H →L[ℂ] H :=
  regularizedMultiplier R hSA m hm - z • regularizer R hSA m hm

theorem imaginaryResolvent_graph (z : ℂ) (hz : z*z = -1) (f : H) :
    (imaginaryResolvent R hSA m hm z f,
      f - z • imaginaryResolvent R hSA m hm z f) ∈ (unboundedRealBorel R hSA m hm).graph := by
  apply (pairOperator_mem_graph_iff _ _ (regularizer_injective R hSA m hm)).mpr
  let B := regularizer R hSA m hm
  let C := regularizedMultiplier R hSA m hm
  have hcomm : B (C f) = C (B f) :=
    congrArg (fun T : H →L[ℂ] H => T f) (regularizers_commute R hSA m hm)
  have hnorm : B (B f) + C (C f) = B f :=
    congrArg (fun T : H →L[ℂ] H => T f) (regularizers_normalized R hSA m hm)
  change B (f - z • (C f - z • B f)) = C (C f - z • B f)
  simp only [map_sub, map_smul, smul_sub, smul_smul, hz, neg_one_smul]
  have hdiff : B f - B (B f) = C (C f) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hnorm.symm
  calc
    _ = (B f - B (B f)) - z • C (B f) := by rw [hcomm]; abel
    _ = _ := by rw [hdiff]

def imaginaryResolventPoint (z : ℂ) (hz : z*z = -1) (f : H) :
    (unboundedRealBorel R hSA m hm).domain :=
  ⟨imaginaryResolvent R hSA m hm z f,
    LinearPMap.mem_domain_of_mem_graph (imaginaryResolvent_graph R hSA m hm z hz f)⟩

theorem imaginaryResolvent_action (z : ℂ) (hz : z*z = -1) (f : H) :
    unboundedRealBorel R hSA m hm (imaginaryResolventPoint R hSA m hm z hz f) =
      f - z • imaginaryResolvent R hSA m hm z f :=
  LinearPMap.mem_graph_snd_inj _ (LinearPMap.mem_graph _ _)
    (imaginaryResolvent_graph R hSA m hm z hz f) rfl

theorem imaginaryResolvent_right_inverse (z : ℂ) (hz : z*z = -1) (f : H) :
    unboundedRealBorel R hSA m hm (imaginaryResolventPoint R hSA m hm z hz f) +
      z • (imaginaryResolventPoint R hSA m hm z hz f : H) = f := by
  rw [imaginaryResolvent_action]
  change f - z • imaginaryResolvent R hSA m hm z f + z • imaginaryResolvent R hSA m hm z f = f
  abel

theorem imaginaryResolvent_left_inverse (z : ℂ) (hz : z*z = -1)
    (u : (unboundedRealBorel R hSA m hm).domain) :
    imaginaryResolvent R hSA m hm z (unboundedRealBorel R hSA m hm u + z • (u : H)) = (u : H) := by
  let B := regularizer R hSA m hm
  let C := regularizedMultiplier R hSA m hm
  let v := unboundedRealBorel R hSA m hm u
  have hg : B v = C (u : H) :=
    (pairOperator_mem_graph_iff _ _ (regularizer_injective R hSA m hm)).mp (LinearPMap.mem_graph _ u)
  have hrec : B (u : H) + C v = (u : H) :=
    pairOperator_graph_reconstruction _ _ (regularizer_injective R hSA m hm)
      (regularizers_commute R hSA m hm) (regularizers_normalized R hSA m hm)
      (LinearPMap.mem_graph _ u)
  change C (v + z • (u : H)) - z • B (v + z • (u : H)) = (u : H)
  simp only [map_add, map_smul, smul_add, smul_smul, hz, neg_one_smul]
  rw [hg]
  calc
    _ = B (u : H) + C v := by abel
    _ = _ := hrec

/-- A true bijection from the FULL native domain, with inverse supplied
by a bounded operator on all H. -/
theorem imaginaryShift_bijective (z : ℂ) (hz : z*z = -1) :
    Function.Bijective (fun u : (unboundedRealBorel R hSA m hm).domain =>
      unboundedRealBorel R hSA m hm u + z • (u : H)) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    have h := congrArg (imaginaryResolvent R hSA m hm z) huv
    simpa only [imaginaryResolvent_left_inverse R hSA m hm z hz] using h
  · intro f
    exact ⟨imaginaryResolventPoint R hSA m hm z hz f,
      imaginaryResolvent_right_inverse R hSA m hm z hz f⟩

theorem plusIShift_bijective :
    Function.Bijective (fun u : (unboundedRealBorel R hSA m hm).domain =>
      unboundedRealBorel R hSA m hm u + Complex.I • (u : H)) :=
  imaginaryShift_bijective R hSA m hm Complex.I Complex.I_mul_I

theorem minusIShift_bijective :
    Function.Bijective (fun u : (unboundedRealBorel R hSA m hm).domain =>
      unboundedRealBorel R hSA m hm u + (-Complex.I) • (u : H)) :=
  imaginaryShift_bijective R hSA m hm (-Complex.I) (by simp only [neg_mul_neg, Complex.I_mul_I])

end
end ImbalancedChen.Part3.GenericUnboundedRealBorelResolvent20261025a

