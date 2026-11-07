import ImbalancedChen.P2N48PriorityHalfGridDictionary
import ImbalancedChen.OriginalPairedN48AllNativeQueryGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The real n96 children query the unchanged original Omega8192 producer.
The original producer decisions are inherited UNEXECUTED proposals.
No child floor, saved numerator or final enclosure is an input.
-/
namespace ImbalancedChen.P2N96PriorityRawOmegaQuery
noncomputable section
open Set
open LiLiuPrereqBuchstab OriginalN48Q112LocalProduct
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48PriorityHalfGridDictionary P2N48OriginalQ80DirectedRowSoundness
open P2N48OriginalStrictLogMassAndOmegaPorts
open OriginalPairedN48AllNativeQueryGeometry OriginalPairedN48RawQueryFamily
open OriginalPairedN48CanonicalArrays OriginalPairedN48CanonicalArrayProofProposals
open OriginalPairedN48PreallocatedProducerIdentity
open P5Z.U11Canonical

def childLowerQ (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℚ :=
  if b j=0 then lowerQ r j else (lowerQ r j+upperQ r j)/2

def childUpperQ (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℚ :=
  if b j=0 then (lowerQ r j+upperQ r j)/2 else upperQ r j

theorem childLowerQ_cast (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    (childLowerQ r b j : ℝ)=childLower r b j := by
  by_cases h : b j=0 <;>
    simp [childLowerQ,childLower,h,rowMid,lowerQ_cast,upperQ_cast]

theorem childUpperQ_cast (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    (childUpperQ r b j : ℝ)=childUpper r b j := by
  by_cases h : b j=0 <;>
    simp [childUpperQ,childUpper,h,rowMid,lowerQ_cast,upperQ_cast]

/-- Exact source endpoint denominator5000*96, with the high slot fixed. -/
theorem child_rational_wire_dictionary (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    childLowerQ r b j=(wireLeft96 r b j : ℚ)/480000 ∧
      childUpperQ r b j=(wireRight96 r b j : ℚ)/480000 := by
  have h := original_child_real_endpoint_dictionary r b j
  rw [←childLowerQ_cast,←childUpperQ_cast] at h
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem child_endpoint_nesting (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    lowerQ r j≤childLowerQ r b j ∧ childLowerQ r b j≤childUpperQ r b j ∧
      childUpperQ r b j≤upperQ r j := by
  have hp : lowerQ r j≤upperQ r j := by
    exact_mod_cast (show (lowerQ r j : ℝ)≤(upperQ r j : ℝ) by
      rw [lowerQ_cast,upperQ_cast]; exact rowLower_le_upper r j)
  by_cases h : b j=0 <;> simp only [childLowerQ,childUpperQ,h,ite_true,ite_false]
    <;> constructor <;> try constructor <;> linarith

theorem child_lower_pos (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    (0 : ℚ)<childLowerQ r b j := by
  have hp : (0 : ℚ)<lowerQ r j := by
    exact_mod_cast (show (0 : ℝ)<(lowerQ r j : ℝ) by
      rw [lowerQ_cast]; exact rowLower_pos r j)
  exact hp.trans_le (child_endpoint_nesting r b j).1

def childRawLower (r : SourceRow) (b : HalfBits) : ℚ :=
  (1-(childUpperQ r b 0+childUpperQ r b 1+childUpperQ r b 2+childUpperQ r b 3))/
    childUpperQ r b 2

def childRawUpper (r : SourceRow) (b : HalfBits) : ℚ :=
  (1-(childLowerQ r b 0+childLowerQ r b 1+childLowerQ r b 2+childLowerQ r b 3))/
    childLowerQ r b 2

/-- All half-children, including empty/nonordered ones, have valid raw
queries. Only the actual weak-ordered child family is integrated later. -/
theorem child_raw_query_range (r : SourceRow) (b : HalfBits) :
    (2 : ℚ)≤childRawLower r b ∧ childRawLower r b≤childRawUpper r b ∧
      childRawUpper r b≤8 := by
  have h0 := child_endpoint_nesting r b 0
  have h1 := child_endpoint_nesting r b 1
  have h2 := child_endpoint_nesting r b 2
  have h3 := child_endpoint_nesting r b 3
  have hl := child_lower_pos r b 2
  have hu := hl.trans_le h2.2.1
  have hpu : (0 : ℚ)<upperQ r 2 := by
    exact_mod_cast (show (0 : ℝ)<(upperQ r 2 : ℝ) by
      rw [upperQ_cast]; exact P2N48TiedParentMassReduction.rowUpper_pos r 2)
  have hpl : (0 : ℚ)<lowerQ r 2 := by
    exact_mod_cast (show (0 : ℝ)<(lowerQ r 2 : ℝ) by
      rw [lowerQ_cast]; exact rowLower_pos r 2)
  have hp := all_native_raw_query_range r
  have hparentLo := (le_div_iff₀ hpu).mp hp.1
  have hparentHi := (div_le_iff₀ hpl).mp hp.2.2
  change 2*upperQ r 2≤1-(upperQ r 0+upperQ r 1+upperQ r 2+upperQ r 3) at hparentLo
  change 1-(lowerQ r 0+lowerQ r 1+lowerQ r 2+lowerQ r 3)≤8*lowerQ r 2 at hparentHi
  have hL : 2*childUpperQ r b 2≤
      1-(childUpperQ r b 0+childUpperQ r b 1+childUpperQ r b 2+childUpperQ r b 3) := by
    linarith only [hparentLo,h0.2.2,h1.2.2,h2.2.2,h3.2.2]
  have hU : 1-(childLowerQ r b 0+childLowerQ r b 1+childLowerQ r b 2+childLowerQ r b 3)≤
      8*childLowerQ r b 2 := by
    linarith only [hparentHi,h0.1,h1.1,h2.1,h3.1]
  have hLU : 1-(childUpperQ r b 0+childUpperQ r b 1+childUpperQ r b 2+childUpperQ r b 3)≤
      1-(childLowerQ r b 0+childLowerQ r b 1+childLowerQ r b 2+childLowerQ r b 3) := by
    linarith only [h0.2.1,h1.2.1,h2.2.1,h3.2.1]
  have hUnonneg : (0 : ℚ)≤
      1-(childLowerQ r b 0+childLowerQ r b 1+childLowerQ r b 2+childLowerQ r b 3) := by
    linarith only [hL,hLU,hu]
  refine ⟨(le_div_iff₀ hu).2 hL,?_,(div_le_iff₀ hl).2 hU⟩
  exact (div_le_div_of_nonneg_right hLU hu.le).trans
    (div_le_div_of_nonneg_left hUnonneg hl h2.2.1)

theorem actual_child_raw_query_contains (r : SourceRow) (b : HalfBits)
    {v : LogFour} (hv : v∈childBox r b) :
    omegaArgument v∈Icc (childRawLower r b : ℝ) (childRawUpper r b : ℝ) := by
  have hb := mem_logPrimeBox.mp hv
  have hl : 0<childLower r b 2 := by
    rw [←childLowerQ_cast]; exact_mod_cast child_lower_pos r b 2
  have hzu : v 2≤childUpper r b 2 := (hb 2).2.le
  have hzl : childLower r b 2≤v 2 := (hb 2).1
  have hz := hl.trans_le hzl
  have hu := hz.trans_le hzu
  let n : ℝ := 1-(v 0+v 1+v 2+v 3)
  let l : ℝ := 1-(childUpper r b 0+childUpper r b 1+childUpper r b 2+childUpper r b 3)
  let u : ℝ := 1-(childLower r b 0+childLower r b 1+childLower r b 2+childLower r b 3)
  have hln : l≤n := by dsimp [l,n]; linarith only [(hb 0).2,(hb 1).2,(hb 2).2,(hb 3).2]
  have hnu : n≤u := by dsimp [n,u]; linarith only [(hb 0).1,(hb 1).1,(hb 2).1,(hb 3).1]
  have hraw : (0 : ℝ)≤(childRawLower r b : ℝ) := by
    exact_mod_cast (show (0 : ℚ)≤childRawLower r b by
      linarith only [(child_raw_query_range r b).1])
  have hdiv : 0≤l/childUpper r b 2 := by
    simpa only [childRawLower,Rat.cast_div,Rat.cast_sub,Rat.cast_one,Rat.cast_add,
      childUpperQ_cast,l] using hraw
  have hl0 : 0≤l := by simpa only [zero_mul] using (le_div_iff₀ hu).mp hdiv
  have hu0 := hl0.trans (hln.trans hnu)
  have hLo := (div_le_div_of_nonneg_left hl0 hz hzu).trans
    (div_le_div_of_nonneg_right hln hz.le)
  have hHi := (div_le_div_of_nonneg_right hnu hz.le).trans
    (div_le_div_of_nonneg_left hu0 hl hzl)
  simpa only [omegaArgument,childRawLower,childRawUpper,Rat.cast_div,Rat.cast_sub,
    Rat.cast_one,Rat.cast_add,childLowerQ_cast,childUpperQ_cast,n,l,u] using And.intro hLo hHi

def childOriginalQueryToken (r : SourceRow) (b : HalfBits) : Token :=
  rawQueryToken originalFixedFields (childRawLower r b) (childRawUpper r b)

/-- Same original array and raw scan as the parent source, now with its
actual n96 endpoints. No clipped query or asserted query enclosure. -/
theorem child_query_upper_proposal (r : SourceRow) (b : HalfBits)
    {v : LogFour} (hv : v∈childBox r b) :
    buchstab (omegaArgument v)≤uniformOmegaUpper (childOriginalQueryToken r b) := by
  have hr := child_raw_query_range r b
  unfold childOriginalQueryToken
  rw [original_fixed_fields_identity]
  exact raw_query_token_upper canonicalSourceArrays canonical_producer_valid_proposal
    (childRawLower r b) (childRawUpper r b) hr.1 hr.2.1
    (by linarith only [hr.2.2]) (actual_child_raw_query_contains r b hv)

end
end ImbalancedChen.P2N96PriorityRawOmegaQuery
