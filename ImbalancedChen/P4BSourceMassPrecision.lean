import ImbalancedChen.RealHalfProductMassSuppliers

/-!
# P4B: precision of the literal manuscript source mass

YELLOW / SOURCE ONLY / UNCOMPILED.

These consequences use the existing audited PNT and weighted Mertens supplier.
The mass is the actual finite source at `manuscriptHalfProductCutoff`, with its
strict badness wall, ordering and prime-square convention.  No source-mass
limit is introduced as an assumption.  All parameters are fixed before the
`atTop` quantifier; no uniformity as `b` tends to one is claimed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- The original manuscript coefficient is strictly positive on its full
fixed-parameter range. -/
theorem p4b_manuscriptSource_logCoefficient_pos {b : ℝ}
    (hbHalf : (1 : ℝ) / 2 < b) (hb1 : b < 1) :
    0 < Real.log (1 / b) := by
  have hb : 0 < b := by linarith
  apply Real.log_pos
  exact (lt_div_iff₀ hb).mpr (by simpa using hb1)

/-- Absolute source-mass error on the original `N / log N` scale, together
with positivity of that scale.  This controls the actual cardinality, rather
than merely the prime-prefix approximation. -/
theorem p4b_eventually_manuscriptSource_absolute_mass_error
    {b κ : ℝ} (hbHalf : (1 : ℝ) / 2 < b) (hb1 : b < 1) (hκ : 0 < κ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      0 < (N : ℝ) / Real.log (N : ℝ) ∧
      |((realHalfProductSource b N
          (manuscriptHalfProductCutoff κ N)).card : ℝ) -
        Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))| <
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hb : 0 < b := by linarith
  have hlimit :=
    tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hb hb1 hκ
  have hnear := (Metric.tendsto_nhds.mp hlimit) epsilon hepsilon
  filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with N hnearN hN
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  refine ⟨hscale, ?_⟩
  rw [Real.dist_eq] at hnearN
  have heq :
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b) =
      (((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) -
          Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))) /
            ((N : ℝ) / Real.log (N : ℝ)) := by
    rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hscale)]
  rw [heq, abs_div, abs_of_pos hscale] at hnearN
  exact (div_lt_iff₀ hscale).mp hnearN

/-- Relative signed error, normalized by the full original main term,
tends to zero.  The logarithmic coefficient is retained in the denominator;
its positivity is proved from the manuscript parameter range. -/
theorem p4b_tendsto_manuscriptSource_relative_mass_error
    {b κ : ℝ} (hbHalf : (1 : ℝ) / 2 < b) (hb1 : b < 1) (hκ : 0 < κ) :
    Tendsto (fun N : ℕ =>
      (((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) -
          Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))) /
        (Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))))
      atTop (nhds 0) := by
  have hL := p4b_manuscriptSource_logCoefficient_pos hbHalf hb1
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards
    [p4b_eventually_manuscriptSource_absolute_mass_error hbHalf hb1 hκ
      (epsilon * Real.log (1 / b)) (mul_pos hepsilon hL)]
    with N hN
  rcases hN with ⟨hscale, herr⟩
  rw [Real.dist_eq, sub_zero, abs_div,
    abs_of_pos (mul_pos hL hscale)]
  apply (div_lt_iff₀ (mul_pos hL hscale)).mpr
  simpa only [mul_assoc] using herr

/-- The literal mass divided by the full main term tends to one.  This is
the useful multiplicative normalization of the existing additive-coefficient
supplier, with the original coefficient displayed explicitly. -/
theorem p4b_tendsto_manuscriptSource_mass_div_mainTerm
    {b κ : ℝ} (hbHalf : (1 : ℝ) / 2 < b) (hb1 : b < 1) (hκ : 0 < κ) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          (Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))))
      atTop (nhds 1) := by
  have hL := p4b_manuscriptSource_logCoefficient_pos hbHalf hb1
  have herror :=
    p4b_tendsto_manuscriptSource_relative_mass_error hbHalf hb1 hκ
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hnear := (Metric.tendsto_nhds.mp herror) epsilon hepsilon
  filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with N hnearN hN
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have hmain : Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) ≠ 0 :=
    ne_of_gt (mul_pos hL hscale)
  rw [Real.dist_eq, sub_zero] at hnearN
  rw [Real.dist_eq]
  have heq :
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          (Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))) - 1 =
      (((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) -
          Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))) /
        (Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ))) := by
    rw [sub_div, div_self hmain]
  rw [heq]
  exact hnearN

/-- One eventual conjunction supplies the positive scale, positive full
main term, positive literal mass and both multiplicative bounds.  The
relative tolerance is fixed in `(0,1)` before taking `N` sufficiently large. -/
theorem p4b_eventually_manuscriptSource_positive_mass_two_sided
    {b κ delta : ℝ} (hbHalf : (1 : ℝ) / 2 < b) (hb1 : b < 1)
    (hκ : 0 < κ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ N : ℕ in atTop,
      0 < (N : ℝ) / Real.log (N : ℝ) ∧
      0 < Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) ∧
      0 < ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) ∧
      (1 - delta) * Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) ≤
        ((realHalfProductSource b N
          (manuscriptHalfProductCutoff κ N)).card : ℝ) ∧
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) ≤
        (1 + delta) * Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hL := p4b_manuscriptSource_logCoefficient_pos hbHalf hb1
  filter_upwards
    [p4b_eventually_manuscriptSource_absolute_mass_error hbHalf hb1 hκ
      (delta * Real.log (1 / b)) (mul_pos hdelta hL)]
    with N hN
  rcases hN with ⟨hscale, herr⟩
  have herrors := abs_lt.mp herr
  have hlower :
      (1 - delta) * Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) <
        ((realHalfProductSource b N
          (manuscriptHalfProductCutoff κ N)).card : ℝ) := by
    nlinarith [herrors.1]
  have hupper :
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) <
        (1 + delta) * Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) := by
    nlinarith [herrors.2]
  have hlowerpos :
      0 < (1 - delta) * Real.log (1 / b) * ((N : ℝ) / Real.log (N : ℝ)) :=
    mul_pos (mul_pos (by linarith) hL) hscale
  exact ⟨hscale, mul_pos hL hscale, hlowerpos.trans hlower,
    hlower.le, hupper.le⟩

end

end ImbalancedChen