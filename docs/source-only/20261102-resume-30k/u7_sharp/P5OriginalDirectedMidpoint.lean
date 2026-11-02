import ImbalancedChen.P5OriginalSignedMidpoint
import ImbalancedChen.P2DirectedLogRounding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Adapter to the EXISTING directed rational arithmetic for the original
`(value(mid) + second(cell)*I(step*step/24))*I(step)` expression.
Rational constants and both multiplications round outward at 80 bits;
addition is exact, as in certify_conservative_chen.I. No finite output,
log endpoint, or second-derivative range is authenticated in this adapter.
The substantive analytic theorem is the imported signed Peano identity.
-/

namespace ImbalancedChen.P5OriginalDirectedMidpoint

noncomputable section
open Set MeasureTheory
open P5OriginalSignedMidpoint Certificates.P2DirectedLogRounding

def cellEnclosure (l r : ℚ) (value second : Enclosure) : Enclosure :=
  ((value.add
    ((second.mul ((Enclosure.point ((r - l) ^ 2 / 24)).round 80)).round 80)).mul
      ((Enclosure.point (r - l)).round 80)).round 80

private theorem cellEnclosure_contains_value {l r : ℚ} {V D : Enclosure} {v d : ℝ}
    (hv : V.Contains v) (hd : D.Contains d) :
    (cellEnclosure l r V D).Contains
      ((v + d * ((r : ℝ) - (l : ℝ)) ^ 2 / 24) * ((r : ℝ) - (l : ℝ))) := by
  have hscale := Enclosure.round_contains
    (Enclosure.point_contains ((r - l) ^ 2 / 24)) 80
  have hstep := Enclosure.round_contains (Enclosure.point_contains (r - l)) 80
  have h := Enclosure.round_contains
    (Enclosure.mul_contains (Enclosure.add_contains hv
      (Enclosure.round_contains (Enclosure.mul_contains hd hscale) 80)) hstep) 80
  simpa only [cellEnclosure, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_ofNat,
    mul_div_assoc] using h

/-- Soundness of the literal directed midpoint expression. A caller must
still prove its actual point and whole-cell derivative boxes; neither is
silently asserted here. Signed negative curvature is accepted unchanged. -/
theorem cellEnclosure_contains_integral {f f' f'' : ℝ → ℝ} {l r : ℚ}
    (hlr : l ≤ r) (V D : Enclosure)
    (hf : ∀ x ∈ Icc (l : ℝ) (r : ℝ), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (l : ℝ) (r : ℝ), HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc (l : ℝ) (r : ℝ)))
    (hvalue : V.Contains (f (((l : ℝ) + (r : ℝ)) / 2)))
    (hsecond : ∀ x ∈ Icc (l : ℝ) (r : ℝ), D.Contains (f'' x)) :
    (cellEnclosure l r V D).Contains (∫ x in (l : ℝ)..(r : ℝ), f x) := by
  have hlrR : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
  have horder : (D.lower : ℝ) ≤ (D.upper : ℝ) :=
    (hsecond l ⟨le_rfl, hlrR⟩).1.trans (hsecond l ⟨le_rfl, hlrR⟩).2
  have hL := cellEnclosure_contains_value hvalue
    (show D.Contains (D.lower : ℝ) from ⟨le_rfl, horder⟩)
  have hU := cellEnclosure_contains_value hvalue
    (show D.Contains (D.upper : ℝ) from ⟨horder, le_rfl⟩)
  have hbound := midpoint_bounds hlrR hf hf' hc hsecond
  constructor
  · exact hL.1.trans (by simpa only [mul_comm] using hbound.1)
  · exact hbound.2.trans (by simpa only [mul_comm] using hU.2)

end
end ImbalancedChen.P5OriginalDirectedMidpoint
