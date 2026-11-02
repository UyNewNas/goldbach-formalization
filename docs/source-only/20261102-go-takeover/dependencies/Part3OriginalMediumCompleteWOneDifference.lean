import ImbalancedChen.Part3OriginalMediumWeight0Normalized
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One exact finite-difference payment of the actual complete-W face
along a positive normalized coordinate segment. The derivative is
the next literal allocation face, bounded by the previously proved
single fifth-power envelope; the norm difference follows from the
one-dimensional mean-value/FTC inequality on the segment. No bound
on a finite difference or on E3 is a premise. This is the local leaf
to iterate over q,w1,w2,n1,h.
-/

namespace ImbalancedChen.Part3.OriginalMediumCompleteWOneDifference

open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumSmoothWeightInput
open ImbalancedChen.Part3.OriginalMediumCompleteWAllSubsetSteps
open ImbalancedChen.Part3.OriginalMediumCompleteWDegreeBound
open ImbalancedChen.Part3.OriginalMediumSubsetLeibnizStep

noncomputable section

def NormBox (v : Vector5) : Prop :=
  1 ≤ v 0 ∧ 1 ≤ v 1 ∧ 1 ≤ v 2 ∧ 1 ≤ v 3 ∧ |v 4| ≤ 1

def fifthEnvelope (B : FixedBlock) (S : SmoothInput B)
    (L A : ℝ) : ℝ :=
  243 * (2 * S.psi0Seminorm) *
    (15 * S.psiHat0Seminorm) * (commonScale L A) ^ 5

theorem fifthEnvelope_nonneg (B : FixedBlock) (S : SmoothInput B)
    (L A : ℝ) : 0 ≤ fifthEnvelope B S L A := by
  unfold fifthEnvelope
  positivity

theorem fullWFace_box_bound
    (B : FixedBlock) (Smooth : SmoothInput B)
    (L A : ℝ) (S : Finset Coordinate) (v : Vector5)
    (hv : NormBox v) :
    ‖fullWFace B L A S v‖ ≤ fifthEnvelope B Smooth L A := by
  rcases hv with ⟨hq,h1,h2,hn,hh⟩
  exact fullWFace_fifth_bound B Smooth L A S v hq h1 h2 hn hh

/-- One coordinate of the 32-face mixed finite difference, with
the derivative bound obtained from literal complete W. -/
theorem fullWFace_difference_bound
    (B : FixedBlock) (Smooth : SmoothInput B)
    (L A : ℝ) (S : Finset Coordinate)
    (i : Coordinate) (hiS : i ∉ S)
    (v : Vector5) (a b : ℝ) (hab : a ≤ b)
    (hsegment : ∀ t ∈ Set.Icc a b,
      NormBox (Function.update v i t)) :
    ‖fullWFace B L A S (Function.update v i b) -
        fullWFace B L A S (Function.update v i a)‖ ≤
      fifthEnvelope B Smooth L A * (b - a) := by
  let f : ℝ → ℂ :=
    fun t => fullWFace B L A S (Function.update v i t)
  let f' : ℝ → ℂ :=
    fun t => fullWFace B L A (insert i S) (Function.update v i t)
  have hder : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt f (f' t) (Set.Icc a b) t := by
    intro t ht
    have hv := hsegment t ht
    rcases hv with ⟨hq,h1,h2,hn,_hh⟩
    have hstep := fullWFace_step_all B Smooth L A S i hiS
      (Function.update v i t)
      (lt_of_lt_of_le zero_lt_one hq)
      (lt_of_lt_of_le zero_lt_one h1)
      (lt_of_lt_of_le zero_lt_one h2)
      (lt_of_lt_of_le zero_lt_one hn)
    have hstep' : HasDerivAt f (f' t) t := by
      simpa [f, f', Function.update_same, Function.update_idem] using hstep
    exact hstep'.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc a b,
      ‖f' t‖ ≤ fifthEnvelope B Smooth L A := by
    intro t ht
    exact fullWFace_box_bound B Smooth L A (insert i S)
      (Function.update v i t) (hsegment t ht)
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (convex_Icc a b)
    (show a ∈ Set.Icc a b by simp [hab])
    (show b ∈ Set.Icc a b by simp [hab])
  simpa [f, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    using hmean

end

end ImbalancedChen.Part3.OriginalMediumCompleteWOneDifference
