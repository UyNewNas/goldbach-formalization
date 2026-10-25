import ImbalancedChen.Part3EvenCompactContinuousDensity
import ImbalancedChen.Part3ActualKCompactCoordinateFactor
import ImbalancedChen.Part3ActualKWeightedPolynomialClosure

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The actual profiles exp(-q*cosh u), already at q=1,2,3,..., have closed span
equal to actual evenL2. Compact even density, coordinate factorization, and
weighted polynomial approximation are all proved sources, not premises.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualKProfileTotalitySourceOnly

open Set MeasureTheory
open EvenFourierHilbertSourceOnly HalfCosinePlancherelSourceOnly
open ActualKWeightedPolynomialClosureSourceOnly
open ActualKCompactCoordinateFactorSourceOnly
open EvenCompactContinuousDensitySourceOnly

/-- Compactly supported continuous even tests belong to the closed span of
the actual profiles at the positive integers. -/
theorem compactEven_toLp_mem_integerProfileClosure {f : ℝ → ℂ}
    (h₂ : MemLp f 2) (hf : Continuous f) (hc : HasCompactSupport f)
    (heven : ∀ u : ℝ, f (-u) = f u) :
    h₂.toLp f ∈ integerProfileSpan.topologicalClosure := by
  obtain ⟨φ, hφ, hfactor⟩ := exists_continuous_coordinate_factor hf hc heven
  have heq : h₂.toLp f = weightedProfileL2 φ hφ :=
    h₂.toLp_congr (weightedProfile_memLp hφ)
      (Filter.Eventually.of_forall fun u => by
        simpa only [weightedProfile, coshCoordinate] using hfactor u)
  rw [heq]
  exact weightedProfileL2_mem_closure hφ

theorem integerProfile_mem_evenL2 (n : ℕ) : integerProfile n ∈ evenL2 := by
  change (evenKProfile ((n : ℝ) + 1) (by positivity) : ComplexL2) ∈ evenL2
  exact (evenKProfile ((n : ℝ) + 1) (by positivity)).property

theorem integerProfileSpan_le_evenL2 : integerProfileSpan ≤ evenL2 := by
  apply Submodule.span_le.2
  rintro v ⟨n, rfl⟩
  exact integerProfile_mem_evenL2 n

/-- The reverse inclusion uses actual compact-even approximation, so the
weighted-coordinate restriction does not become an assumed density premise. -/
theorem evenL2_le_integerProfileClosure : evenL2 ≤ integerProfileSpan.topologicalClosure := by
  intro f hf
  have happrox : f ∈ closure (closure (integerProfileSpan : Set ComplexL2)) := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨g, hg, hgc, hgs, hge, herr⟩ :=
      exists_even_compact_continuous_approx (⟨f, hf⟩ : evenL2) hε
    refine ⟨hg.toLp g, ?_, ?_⟩
    · exact compactEven_toLp_mem_integerProfileClosure hg hgc hgs hge
    · simpa only [dist_eq_norm, norm_sub_rev] using herr
  simpa only [closure_closure] using happrox

/-- Genuine totality of the concrete positive-integer exponential-cosh
profiles in the actual even full-line L2 subspace. -/
theorem integerProfileClosure_eq_evenL2 :
    integerProfileSpan.topologicalClosure = evenL2 := by
  apply le_antisymm
  · intro f hf
    exact (closure_minimal
      (show (integerProfileSpan : Set ComplexL2) ⊆ (evenL2 : Set ComplexL2)
        from integerProfileSpan_le_evenL2) isClosed_evenL2) hf
  · exact evenL2_le_integerProfileClosure

/-- The full family uses the literal actual evenKProfile at every q>0. -/
def positiveProfileSpan : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range fun q : {q : ℝ // 0 < q} =>
    (evenKProfile q.val q.property : ComplexL2))

theorem integerProfileSpan_le_positiveProfileSpan :
    integerProfileSpan ≤ positiveProfileSpan := by
  apply Submodule.span_le.2
  rintro v ⟨n, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨(n : ℝ) + 1, by positivity⟩, rfl⟩

theorem positiveProfileSpan_le_evenL2 : positiveProfileSpan ≤ evenL2 := by
  apply Submodule.span_le.2
  rintro v ⟨q, rfl⟩
  exact (evenKProfile q.val q.property).property

/-- Totality of the full actual q>0 exponential-cosh family. This is
Euclidean profile totality and asserts no automorphic or KL decomposition. -/
theorem positiveProfileClosure_eq_evenL2 :
    positiveProfileSpan.topologicalClosure = evenL2 := by
  apply le_antisymm
  · intro f hf
    exact (closure_minimal
      (show (positiveProfileSpan : Set ComplexL2) ⊆ (evenL2 : Set ComplexL2)
        from positiveProfileSpan_le_evenL2) isClosed_evenL2) hf
  · intro f hf
    have hfi : f ∈ closure (integerProfileSpan : Set ComplexL2) :=
      evenL2_le_integerProfileClosure hf
    exact closure_mono
      (show (integerProfileSpan : Set ComplexL2) ⊆ (positiveProfileSpan : Set ComplexL2)
        from integerProfileSpan_le_positiveProfileSpan) hfi

end ImbalancedChen.Part3.ActualKProfileTotalitySourceOnly
