import ImbalancedChen.P2CanonicalTentDynamicQueryReceiver
import ImbalancedChen.P2OriginalSelectedPairNativeData

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual production L5/L6 root has TWO old external primes, but its
cutoff is a=417/5000, not the last old marked prime. Its root level is the
literal original piecewise level, with the existing double cap buffer.
Each root's query is proved from this independently defined root. No
candidate plan or successful selector is used to supply the identity.

The identity is local to each physical root Q. Grouping variable root
levels into the manuscript's one fixed-Q finite marked families, and
proving H/h table estimates on those families, remain separate work.
-/

namespace ImbalancedChen.P2OriginalPairRootActualQuery

noncomputable section
open scoped Classical BigOperators
open P2LowerCapPlanIntegerRetention P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData P2ActualSameQResidualQuery
open P2CanonicalTentDynamicQueryReceiver

def a : ℝ := 417/5000
def pairPoint (N : ℕ) (p : ℕ×ℕ) : Fin 2 → ℝ :=
  ![coordinate N p.1,coordinate N p.2]

def rootQuery (sixth : Bool) (buffer : ℚ) (N : ℕ) (p : ℕ×ℕ) : ℝ :=
  queryAtTrace (pairRoot N p (rootSeed sixth buffer N p)) a

def actualRootCutoff (sixth : Bool) (N : ℕ) : ℝ :=
  if sixth then P5CausalRhoQuotientBridge.cutoff N else P5OriginalU5CausalFinite.cutoff N

theorem actualRootCutoff_is_original (sixth : Bool) (N : ℕ) :
    actualRootCutoff sixth N = (N:ℝ)^a := by
  cases sixth <;> rfl

theorem actual_root_word (sixth : Bool) (buffer : ℚ) (N : ℕ) (p : ℕ×ℕ) :
    (pairRoot N p (rootSeed sixth buffer N p)).word = physicalWord N [p.1,p.2] := by
  simp [pairRoot,physicalWord]

theorem actual_root_query_complete_prefix (sixth : Bool) (buffer : ℚ)
    (N : ℕ) (p : ℕ×ℕ) :
    rootQuery sixth buffer N p =
      residualQuery N (rootSeed sixth buffer N p) a [p.1,p.2] := by
  simp [rootQuery,queryAtTrace,residualQuery,residualExponent,prefixExponent,
    pairRoot,physicalWord] <;> ring

theorem actual_root_query_level_formula (sixth : Bool) (buffer : ℚ)
    (N : ℕ) (p : ℕ×ℕ) :
    rootQuery sixth buffer N p =
      (rootLevel sixth N p-coordinate N p.1-coordinate N p.2-2*(buffer:ℝ))/a := by
  simp [rootQuery,queryAtTrace,pairRoot,rootSeed] <;> ring

/-- Exact double-buffer shift from the independent original L5 argument. -/
theorem actual_L5_root_query (buffer : ℚ) (N : ℕ) (p : ℕ×ℕ) :
    rootQuery false buffer N p =
      Part5OriginalUpsilon5CausalDictionary.argument (pairPoint N p) - 2*(buffer:ℝ)/a := by
  rw [actual_root_query_level_formula]
  simp [rootLevel,Part5OriginalUpsilon5CausalDictionary.argument,
    Part5OriginalUpsilon5CausalDictionary.residual,Part5OriginalUpsilon5CausalDictionary.a,
    pairPoint,a] <;> ring

/-- L6 keeps its original piecewise physicalLevel, including the mu wall. -/
theorem actual_L6_root_query (buffer : ℚ) (N : ℕ) (p : ℕ×ℕ) :
    rootQuery true buffer N p =
      P5U6CausalLevelGeometry.argument (pairPoint N p) - 2*(buffer:ℝ)/a := by
  rw [actual_root_query_level_formula]
  simp [rootLevel,P5U6CausalLevelGeometry.argument,P5U6CausalLevelGeometry.residual,
    P5U6CausalLevelGeometry.a,pairPoint,a] <;> ring

/-- Actual Phi cutoff at this production root equals the ORIGINAL a
    cutoff. The external smaller prime is not used as the divisor. -/
theorem actual_root_Phi_cutoff {N : ℕ} (hN : (1:ℝ) < N)
    (sixth : Bool) (buffer : ℚ) (p : ℕ×ℕ) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hL : 0 < rootSeed sixth buffer N p-coordinate N p.1-coordinate N p.2) :
    P2EnhancedTwentyOneSameQWeighted.cutoff ((N:ℝ)^(rootSeed sixth buffer N p))
      (p.1*p.2) (rootQuery sixth buffer N p) = actualRootCutoff sixth N := by
  have hpos : ∀ q ∈ ([p.1,p.2] : List ℕ), 0 < q := by
    intro q hq
    simp only [List.mem_cons,List.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption
  have hL' : 0 < residualExponent N (rootSeed sixth buffer N p) [p.1,p.2] := by
    have hsum : prefixExponent N [p.1,p.2] = coordinate N p.1+coordinate N p.2 := by
      simp [prefixExponent,physicalWord] <;> ring
    rw [residualExponent,hsum]
    linarith
  have hc := original_cutoff_of_actual_query hN (rootSeed sixth buffer N p) a
    [p.1,p.2] hpos hL' (by norm_num [a])
  rw [actual_root_query_complete_prefix,actualRootCutoff_is_original]
  simpa using hc

/-- The original retained product margin, rather than a last-prime
    surrogate, supplies an actual buffered lower-query gate. -/
theorem actual_L6_buffered_query_gt_two {eta : ℝ} (heta : 0 ≤ eta)
    (buffer : ℚ) (hb : 2*(buffer:ℝ) ≤ eta) (N : ℕ) (p : ℕ×ℕ)
    (hx : pairPoint N p ∈ currentChenUpsilon6LogDomain eta) :
    2 < rootQuery true buffer N p := by
  have hr := (P5U6CausalLevelGeometry.domain_bounds heta hx).1
  rw [actual_L6_root_query]
  have ha : 0 < a := by norm_num [a]
  have harg : 2*a+eta < P5U6CausalLevelGeometry.residual (pairPoint N p) := by
    simpa [P5U6CausalLevelGeometry.a,a] using hr
  have heq : P5U6CausalLevelGeometry.argument (pairPoint N p) - 2*(buffer:ℝ)/a =
      (P5U6CausalLevelGeometry.residual (pairPoint N p)-2*(buffer:ℝ))/a := by
    unfold P5U6CausalLevelGeometry.argument
    simp only [P5U6CausalLevelGeometry.a,a]
    ring
  rw [heq]
  apply (lt_div_iff₀ ha).2
  linarith

theorem actual_L6_retained_selector_query {N : ℕ} (hN : (1:ℝ) < N)
    {eta : ℝ} (heta : 0 ≤ eta) (buffer : ℚ) (hb : 2*(buffer:ℝ) ≤ eta)
    (E : ℕ×ℕ → Prop) (p : ℕ×ℕ)
    (hp : p ∈ currentChenUpsilon6RetainedSelector N E eta) :
    2 < rootQuery true buffer N p := by
  have hlog := (mem_currentChenUpsilon6RetainedSelector_log_iff hN E eta p).mp hp
  have hx : pairPoint N p ∈ currentChenUpsilon6LogDomain eta := by
    simpa [pairPoint,currentChenUpsilon6LogCoordinates,coordinate] using hlog.2.2.2
  exact actual_L6_buffered_query_gt_two heta buffer hb N p hx

end
end ImbalancedChen.P2OriginalPairRootActualQuery
