import ImbalancedChen.P0RationalQueryPublicAPI
import ImbalancedChen.ActualThirdOriginalSymmetricClippedMean
import ImbalancedChen.ActualThirdOriginalRoundedNewMean
import ImbalancedChen.Part4ActualThirdOriginalFirstChordQuery

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Concrete query specialization of the existing symmetric clipped-mean candidate.
The OLD endpoints are the exact rational geometric expressions; their integer
lower queries and the NEW integer upper query are actual original queries.
The raw OLD weight, box geometry and logarithm operand remain explicit source
dependencies. No semantic endpoint or factor-query enclosure is an input.
-/

namespace ImbalancedChen.P0OriginalClippedChordConcreteAPI

noncomputable section
open Set MeasureTheory
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdClippedChordSourceOnly
open OriginalThirdSymmetricClippedMeanSourceOnly
open OriginalThirdRoundedNewSourceOnly
open OriginalU2RationalQueryPublicAPIP0SourceOnly

/-- Literal OLD lower and upper geometric endpoints before sieve.at. -/
def oldLowQ (b d : ℚ) : ℚ := (57/64-(7/2)*b)/d-1

def oldHighQ (a c : ℚ) : ℚ := (57/64-(7/2)*a)/c-1

theorem oldLowQ_cast (b d : ℚ) :
    (oldLowQ b d : ℝ) = oldLow (b : ℝ) (d : ℝ) := by
  simp only [oldLowQ, oldLow, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_one]

theorem oldHighQ_cast (a c : ℚ) :
    (oldHighQ a c : ℝ) = oldHigh (a : ℝ) (c : ℝ) := by
  simp only [oldHighQ, oldHigh, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_one]

/-- Same original signed lower chord and nonnegative candidate operation.
The endpoint integers and output integer are definitions, not parameters. -/
def queriedMeanHigh (a b c d : ℚ) (l u : ℤ) (qnew : ℚ) : ℤ :=
  meanHigh l u (pointQuery (oldLowQ b d)).lo
    (pointQuery (oldHighQ a c)).lo (pointQuery qnew).hi

/-- Real endpoint/query premises of the generic theorem are discharged by
the original compact query theorem on [2,12]. -/
theorem symmetric_clipped_mean_with_original_queries
    (a b c d : ℚ) (l u : ℤ) (qnew : ℚ)
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hmu : VariableEnvelope.mu ≤ (a : ℝ))
    (hlo : 2 ≤ oldLowQ b d) (hspan : oldLowQ b d < oldHighQ a c)
    (hhi : oldHighQ a c ≤ 12)
    (hwtlo : value l ≤ oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hwthi : oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) ≤ value u)
    (hq2 : 2 ≤ qnew) (hq12 : qnew ≤ 12)
    (hnew : newMean (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) ≤ (qnew : ℝ)) :
    (∫ t in compactRegion ∩ symmetricBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ),
      compactKernel t) ≤
      prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) *
        value (queriedMeanHigh a b c d l u qnew) := by
  have hfl := (pointQuery_sound hlo (hspan.le.trans hhi)).1
  have hfh := (pointQuery_sound (hlo.trans hspan.le) hhi).1
  rw [oldLowQ_cast] at hfl
  rw [oldHighQ_cast] at hfh
  have hloR : (2 : ℝ) ≤ oldLow (b : ℝ) (d : ℝ) := by
    have h : (2 : ℝ) ≤ (oldLowQ b d : ℝ) := by exact_mod_cast hlo
    simpa only [oldLowQ_cast] using h
  have hspanR : oldLow (b : ℝ) (d : ℝ) < oldHigh (a : ℝ) (c : ℝ) := by
    have h : (oldLowQ b d : ℝ) < (oldHighQ a c : ℝ) := by exact_mod_cast hspan
    simpa only [oldLowQ_cast, oldHighQ_cast] using h
  exact original_symmetric_clipped_mean_candidate hg hmu hloR hspanR
    hwtlo hwthi hfl hfh hnew (pointQuery_sound hq2 hq12).2

/-- The original interval expression for NEW supplies the outward argument,
so hnew, hfl, hfh and hquery all disappear from this consumer interface. -/
theorem symmetric_clipped_mean_with_rounded_new_query
    (a b c d : ℚ) (l u : ℤ) (lx : IV)
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hmu : VariableEnvelope.mu ≤ (a : ℝ))
    (hlo : 2 ≤ oldLowQ b d) (hspan : oldLowQ b d < oldHighQ a c)
    (hhi : oldHighQ a c ≤ 12)
    (hwtlo : value l ≤ oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hwthi : oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) ≤ value u)
    (hlog : Encloses lx (Real.log ((b : ℝ)/(a : ℝ)))) (hpositive : 0 < lx.lo)
    (hq2 : 2 ≤ symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) lx)
    (hq12 : symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) lx ≤ 12) :
    (∫ t in compactRegion ∩ symmetricBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ),
      compactKernel t) ≤
      prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) *
        value (queriedMeanHigh a b c d l u
          (symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) lx)) := by
  exact symmetric_clipped_mean_with_original_queries a b c d l u _ hg hmu
    hlo hspan hhi hwtlo hwthi hq2 hq12
    (actual_newMean_le_original_rounded_query hlog hpositive)

/-- Finite log-certificate specialization uses the same lx integers. Only
the explicit check and rational identities are needed for that operand. -/
theorem symmetric_clipped_mean_with_checked_log
    (a b c d : ℚ) (l u : ℤ) (lx : IV) (cert : Certificates.RationalLogCertificate)
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hmu : VariableEnvelope.mu ≤ (a : ℝ))
    (hlo : 2 ≤ oldLowQ b d) (hspan : oldLowQ b d < oldHighQ a c)
    (hhi : oldHighQ a c ≤ 12)
    (hwtlo : value l ≤ oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hwthi : oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) ≤ value u)
    (harg : cert.argument = b/a)
    (hlower : cert.lower = (lx.lo : ℚ)/(P160 : ℚ))
    (hupper : cert.upper = (lx.hi : ℚ)/(P160 : ℚ))
    (hcheck : cert.check = true) (hpositive : 0 < lx.lo)
    (hq2 : 2 ≤ symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) lx)
    (hq12 : symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) lx ≤ 12) :
    (∫ t in compactRegion ∩ symmetricBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ),
      compactKernel t) ≤
      prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) *
        value (queriedMeanHigh a b c d l u
          (symmetricNewQuery (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) lx)) := by
  exact symmetric_clipped_mean_with_original_queries a b c d l u _ hg hmu
    hlo hspan hhi hwtlo hwthi hq2 hq12
    (actual_newMean_le_query_of_checked_log a b c d lx cert harg hlower hupper
      hcheck hpositive)

/-- Independent first-cell supplier: this uses the explicit logarithm-node
proof in Part4, without assuming soundness of the entire compact table. -/
def firstCellPointQuery (q : ℚ) : IV :=
  ⟨OriginalU2FirstChordCellSourceOnly.queryLo q * 2^48,
    OriginalU2FirstChordCellSourceOnly.queryHi q * 2^48⟩

theorem firstCellPointQuery_sound {q : ℚ}
    (hq2 : 2 < q) (hqcell : q < 2+1/16384) :
    Encloses (firstCellPointQuery q) (actualExtendedThirdLowerFactor (q : ℝ)) := by
  simpa only [Encloses, firstCellPointQuery, value, P160, Int.cast_pow, Int.cast_ofNat]
    using OriginalU2FirstChordCellSourceOnly.original_first_cell_160bit_query_encloses
      hq2 hqcell

def firstCellMeanHigh (a b c d : ℚ) (l u : ℤ) (qnew : ℚ) : ℤ :=
  meanHigh l u (firstCellPointQuery (oldLowQ b d)).lo
    (firstCellPointQuery (oldHighQ a c)).lo (firstCellPointQuery qnew).hi

/-- A separate first-cell concrete specialization of the actual consumer.
It uses only the proved first chord's two rounds for all three factor queries. -/
theorem symmetric_clipped_mean_with_first_cell_queries
    (a b c d : ℚ) (l u : ℤ) (qnew : ℚ)
    (hg : SymmetricFullBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hmu : VariableEnvelope.mu ≤ (a : ℝ))
    (hlo : 2 < oldLowQ b d) (hspan : oldLowQ b d < oldHighQ a c)
    (hhi : oldHighQ a c < 2+1/16384)
    (hwtlo : value l ≤ oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (hwthi : oldWeight (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) ≤ value u)
    (hq2 : 2 < qnew) (hqcell : qnew < 2+1/16384)
    (hnew : newMean (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) ≤ (qnew : ℝ)) :
    (∫ t in compactRegion ∩ symmetricBox (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ),
      compactKernel t) ≤
      prismMass (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) *
        value (firstCellMeanHigh a b c d l u qnew) := by
  have hfl := (firstCellPointQuery_sound hlo (hspan.trans hhi)).1
  have hfh := (firstCellPointQuery_sound (hlo.trans hspan) hhi).1
  rw [oldLowQ_cast] at hfl
  rw [oldHighQ_cast] at hfh
  have hloR : (2 : ℝ) ≤ oldLow (b : ℝ) (d : ℝ) := by
    have h : (2 : ℝ) ≤ (oldLowQ b d : ℝ) := by exact_mod_cast hlo.le
    simpa only [oldLowQ_cast] using h
  have hspanR : oldLow (b : ℝ) (d : ℝ) < oldHigh (a : ℝ) (c : ℝ) := by
    have h : (oldLowQ b d : ℝ) < (oldHighQ a c : ℝ) := by exact_mod_cast hspan
    simpa only [oldLowQ_cast, oldHighQ_cast] using h
  exact original_symmetric_clipped_mean_candidate hg hmu hloR hspanR
    hwtlo hwthi hfl hfh hnew (firstCellPointQuery_sound hq2 hqcell).2

end
end ImbalancedChen.P0OriginalClippedChordConcreteAPI
