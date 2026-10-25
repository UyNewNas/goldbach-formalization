import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Module

/-!
Reusable positive-resolvent calculus on an arbitrary complex Hilbert space.
The only operator hypotheses are self-adjointness, positivity and norm <=1.
The shifted family is a total bare CFC function, independent of a proof that
its real parameter is positive. Positive parameters supply the genuine
normalizer inverse, norm bound and shifted graph inverse identities.
No concrete whole-plane Hilbert space or automorphic realization is fixed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a

noncomputable section

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertEnd := H →L[ℂ] H

def denominator (a t : ℝ) : ℝ := 1 + (a - 1) * t
def inverseDenominator (a t : ℝ) : ℝ := 1 / denominator a t
def resolventRatio (a t : ℝ) : ℝ := t / denominator a t

def shiftedResolvent (R : HilbertEnd (H := H)) (a : ℝ) : HilbertEnd (H := H) :=
  cfc (resolventRatio a) R

def normalizer (R : HilbertEnd (H := H)) (a : ℝ) : HilbertEnd (H := H) :=
  1 + (((a - 1 : ℝ) : ℂ) • R)

def inverseNormalizer (R : HilbertEnd (H := H)) (a : ℝ) : HilbertEnd (H := H) :=
  cfc (inverseDenominator a) R

theorem spectrum_mem_unitInterval (R : HilbertEnd (H := H))
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {t : ℝ} (ht : t ∈ spectrum ℝ R) : t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨spectrum_nonneg_of_nonneg hpos ht, ?_⟩
  have hs : ‖t‖ ≤ ‖R‖ * ‖(1 : HilbertEnd (H := H))‖ := spectrum.norm_le_norm_mul_of_mem ht
  have hi : ‖(1 : HilbertEnd (H := H))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (Real.le_norm_self t).trans (hs.trans (by
    simpa only [one_mul] using mul_le_mul hnorm hi (norm_nonneg _) zero_le_one))

theorem denominator_lower {a t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    min 1 a ≤ denominator a t := by
  unfold denominator
  by_cases ha : 1 ≤ a
  · rw [min_eq_left ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) ht.1]
  · have ha' : a ≤ 1 := (lt_of_not_ge ha).le
    rw [min_eq_right ha']
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr ht.2)]

theorem denominator_pos {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < denominator a t := (lt_min zero_lt_one ha).trans_le (denominator_lower ht)

theorem continuousOn_denominator (R : HilbertEnd (H := H)) (a : ℝ) :
    ContinuousOn (denominator a) (spectrum ℝ R) := by
  have h : Continuous (denominator a) := by unfold denominator; fun_prop
  exact h.continuousOn

theorem continuousOn_inverseDenominator (R : HilbertEnd (H := H))
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (inverseDenominator a) (spectrum ℝ R) :=
  continuousOn_const.div (continuousOn_denominator R a)
    (fun t ht => (denominator_pos ha (spectrum_mem_unitInterval R hpos hnorm ht)).ne')

theorem continuousOn_resolventRatio (R : HilbertEnd (H := H))
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (resolventRatio a) (spectrum ℝ R) :=
  continuousOn_id.div (continuousOn_denominator R a)
    (fun t ht => (denominator_pos ha (spectrum_mem_unitInterval R hpos hnorm ht)).ne')

theorem cfc_denominator (R : HilbertEnd (H := H)) (hSA : IsSelfAdjoint R) (a : ℝ) :
    cfc (denominator a) R = normalizer R a := by
  unfold denominator normalizer
  rw [cfc_add, cfc_const_one ℝ R hSA, cfc_const_mul_id (a - 1) R hSA]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem inverseNormalizer_mul_normalizer (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) : inverseNormalizer R a * normalizer R a = 1 := by
  have hcont := continuousOn_inverseDenominator R hpos hnorm ha
  rw [inverseNormalizer, ← cfc_denominator R hSA a,
    ← cfc_mul (inverseDenominator a) (denominator a) R hcont (continuousOn_denominator R a)]
  have heq : (spectrum ℝ R).EqOn
      (fun t => inverseDenominator a t * denominator a t) (fun _ => 1) := by
    intro t ht
    exact one_div_mul_cancel (denominator_pos ha (spectrum_mem_unitInterval R hpos hnorm ht)).ne'
  rw [cfc_congr heq, cfc_const_one ℝ R hSA]

theorem normalizer_mul_inverseNormalizer (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) : normalizer R a * inverseNormalizer R a = 1 := by
  have hcont := continuousOn_inverseDenominator R hpos hnorm ha
  rw [inverseNormalizer, ← cfc_denominator R hSA a,
    ← cfc_mul (denominator a) (inverseDenominator a) R (continuousOn_denominator R a) hcont]
  have heq : (spectrum ℝ R).EqOn
      (fun t => denominator a t * inverseDenominator a t) (fun _ => 1) := by
    intro t ht
    exact mul_one_div_cancel (denominator_pos ha (spectrum_mem_unitInterval R hpos hnorm ht)).ne'
  rw [cfc_congr heq, cfc_const_one ℝ R hSA]

theorem shiftedResolvent_eq_inverseNormalizer_mul (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) : shiftedResolvent R a = inverseNormalizer R a * R := by
  have heq : resolventRatio a = fun t => inverseDenominator a t * t := by
    funext t
    unfold resolventRatio inverseDenominator
    ring
  rw [shiftedResolvent, heq, cfc_mul (inverseDenominator a) (fun t : ℝ => t) R
    (continuousOn_inverseDenominator R hpos hnorm ha) continuousOn_id, cfc_id' ℝ R hSA]
  rfl

theorem normalizer_mul_shiftedResolvent (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) : normalizer R a * shiftedResolvent R a = R := by
  rw [shiftedResolvent_eq_inverseNormalizer_mul R hSA hpos hnorm ha, ← mul_assoc,
    normalizer_mul_inverseNormalizer R hSA hpos hnorm ha, one_mul]

theorem resolventRatio_nonneg_le {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ resolventRatio a t ∧ resolventRatio a t ≤ 1 / a := by
  have hd := denominator_pos ha ht
  constructor
  · exact div_nonneg ht.1 hd.le
  · apply (div_le_div_iff₀ hd ha).2
    unfold denominator
    nlinarith [ht.2]

theorem shiftedResolvent_norm_le (R : HilbertEnd (H := H))
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ‖shiftedResolvent R a‖ ≤ 1 / a := by
  change ‖cfc (resolventRatio a) R‖ ≤ 1 / a
  apply norm_cfc_le (by positivity)
  intro t ht
  have h := resolventRatio_nonneg_le ha (spectrum_mem_unitInterval R hpos hnorm ht)
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- The actual shifted inverse relation, generic over the Hilbert space. -/
def resolventGraph (R : HilbertEnd (H := H)) : Set (H × H) :=
  {p | R (p.1 + p.2) = p.1}

theorem resolventGraph_right_unique (R : HilbertEnd (H := H)) (hinj : Function.Injective R)
    {u v w : H} (huv : (u, v) ∈ resolventGraph R) (huw : (u, w) ∈ resolventGraph R) : v = w := by
  change R (u + v) = u at huv
  change R (u + w) = u at huw
  have h := hinj (huv.trans huw.symm)
  exact add_left_cancel h

theorem shiftedResolvent_on_graph (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) {u v : H} (hgraph : (u, v) ∈ resolventGraph R) :
    shiftedResolvent R a ((a : ℂ) • u + v) = u := by
  change R (u + v) = u at hgraph
  have hv : R v = u - R u := by
    apply (eq_sub_iff_add_eq).2
    simpa only [map_add, add_comm] using hgraph
  have hN : R ((a : ℂ) • u + v) = normalizer R a u := by
    rw [map_add, map_smul, hv]
    change (a : ℂ) • R u + (u - R u) = u + (((a - 1 : ℝ) : ℂ) • R u)
    push_cast
    module
  rw [shiftedResolvent_eq_inverseNormalizer_mul R hSA hpos hnorm ha]
  change inverseNormalizer R a (R ((a : ℂ) • u + v)) = u
  rw [hN]
  exact congrArg (fun T : HilbertEnd (H := H) => T u)
    (inverseNormalizer_mul_normalizer R hSA hpos hnorm ha)

theorem shiftedResolvent_graph_pair (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) (f : H) :
    (shiftedResolvent R a f, f - (a : ℂ) • shiftedResolvent R a f) ∈ resolventGraph R := by
  let u := shiftedResolvent R a f
  have hN : normalizer R a u = R f := congrArg (fun T : HilbertEnd (H := H) => T f)
    (normalizer_mul_shiftedResolvent R hSA hpos hnorm ha)
  change R (u + (f - (a : ℂ) • u)) = u
  rw [map_add, map_sub, map_smul, ← hN]
  change R u + (u + (((a - 1 : ℝ) : ℂ) • R u) - (a : ℂ) • R u) = u
  push_cast
  module

theorem existsUnique_shifted_graph_solution (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) (f : H) :
    ∃! u : H, (u, f - (a : ℂ) • u) ∈ resolventGraph R := by
  refine ⟨shiftedResolvent R a f, shiftedResolvent_graph_pair R hSA hpos hnorm ha f, ?_⟩
  intro u hu
  have h := shiftedResolvent_on_graph R hSA hpos hnorm ha hu
  have hs : (a : ℂ) • u + (f - (a : ℂ) • u) = f := by abel
  rw [hs] at h
  exact h.symm

end

end ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
