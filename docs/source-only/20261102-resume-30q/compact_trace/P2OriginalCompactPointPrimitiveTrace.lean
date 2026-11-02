import ImbalancedChen.P2OriginalCompactQ80Arithmetic

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED / NO FINITE QUERY EVALUATED.

One complete original primitive segment: SieveTable.point and its actual
non-convex numerator call, at mesh 16384 and maximum 12. Events preserve the
Python evaluation order, the explicit numerator assertion, all performed
LL/LH/HH array reads, integer divisions and calls to ceildiv. The uninstrumented
result is exactly L.point. Every event is proved safe from the rational
denominator being positive; no table value, enclosure or target guard is a
premise. The index conversion reuses the production literal-divmod dictionary
and query geometry already used in L's numerator soundness proof.

The interpolation-error constant is computed once during table construction.
Its use below is a scalar read event, not another Python ceildiv invocation;
the pure L value expression retains the definition of that same constant.

This covers the point/numerator segment, not I, log, Jensen or the entire
producer. The convex=True numerator arm is unreachable from original point
and is outside this segment.
-/
namespace ImbalancedChen.P2OriginalCompactPointPrimitiveTraceSourceOnly

open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2HistoricSieveTableSemantics
open OriginalU2CoupledRecurrenceSourceOnly

inductive PointEvent where
  | divmod (n d : ℤ)
  | numeratorAssertion (q : ℤ)
  | llRead (index : ℕ)
  | lhRead (index : ℕ)
  | hhRead (index : ℕ)
  | interpolationErrorRead
  | floorDivision (n d : ℤ)
  | ceilingDivision (n d : ℤ)

/-- Positivity for integer arithmetic; Python's explicit q<=maximum*n
assertion; and actual initialized-array index bounds. Nonnegativity of q
also ensures the natural-index port does not use Python negative indexing. -/
def PointEvent.Safe : PointEvent → Prop
  | .divmod _ d => 0 < d
  | .numeratorAssertion q => 0 ≤ q ∧ q ≤ 196608
  | .llRead i => i ≤ 196608
  | .lhRead i => i ≤ 196608
  | .hhRead i => i ≤ 196608
  | .interpolationErrorRead => True
  | .floorDivision _ d => 0 < d
  | .ceilingDivision _ d => 0 < d

structure PointTrace where
  value : I80
  events : List PointEvent

/-- The exact non-convex numerator body reached by Python point. A node
read records the original lower/upper array access, not an analytic value. -/
def numeratorTrace (a b : ℤ) : PointTrace :=
  let quotient := (a * 16384) / b
  let q := quotient.toNat
  let r := (a * 16384) % b
  let prefix : List PointEvent := [.divmod (a * 16384) b,.numeratorAssertion quotient]
  if r = 0 then
    ⟨⟨(sourceTable q).ll,(sourceTable q).lh⟩,
      prefix ++ [.llRead q,.lhRead q]⟩
  else
    let lowNumerator := (sourceTable q).ll * (b-r) + (sourceTable (q+1)).ll * r
    let highNumerator := (sourceTable q).lh * (b-r) + (sourceTable (q+1)).lh * r
    ⟨⟨lowNumerator/b,up highNumerator b + up scale (8*(16384 : ℤ)^2)⟩,
      prefix ++ [.llRead q,.llRead (q+1),.floorDivision lowNumerator b,
        .lhRead q,.lhRead (q+1),.ceilingDivision highNumerator b,
        .interpolationErrorRead]⟩

def pointTrace (a b : ℤ) : PointTrace :=
  if a ≤ 2*b then ⟨⟨0,0⟩,[]⟩ else
  if a > 12*b then
    ⟨⟨(sourceTable (12*16384)).ll/12,up (sourceTable (12*16384)).hh 12⟩,
      [.llRead (12*16384),
        .floorDivision (sourceTable (12*16384)).ll 12,
        .hhRead (12*16384),
        .ceilingDivision (sourceTable (12*16384)).hh 12]⟩
  else
    let p := numeratorTrace a b
    ⟨⟨p.value.lo*b/a,up (p.value.hi*b) a⟩,
      p.events ++ [.floorDivision (p.value.lo*b) a,.ceilingDivision (p.value.hi*b) a]⟩

theorem numeratorTrace_value (a b : ℤ) : (numeratorTrace a b).value = sourceNumerator a b := by
  by_cases hr : (a * 16384) % b = 0 <;> simp [numeratorTrace,sourceNumerator,hr]

/-- Exact integer result in all branches, even before supplying validity. -/
theorem pointTrace_value (a b : ℤ) : (pointTrace a b).value = point a b := by
  by_cases hlow : a ≤ 2*b
  · simp [pointTrace,point,hlow]
  · by_cases hhigh : a > 12*b
    · simp [pointTrace,point,hlow,hhigh]
    · simp [pointTrace,point,hlow,hhigh,numeratorTrace_value]

/-- Expose the existing literal-query dictionary as the source assertion and
read-index licence. This is an integer/API conversion, not another proof of
the delayed-function interpolation estimate. -/
theorem numerator_index_licence (a b : ℤ) (hb : 0 < b)
    (ha2 : 2*b < a) (ha12 : a ≤ 12*b) :
    let quotient := (a*16384)/b
    let q := quotient.toNat
    0 ≤ quotient ∧ quotient ≤ 196608 ∧ q ≤ 196608 ∧
      ((a*16384)%b ≠ 0 → q+1 ≤ 196608) := by
  have ha0 : 0 ≤ a := by omega
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  let ratio : ℚ := (a : ℚ)/(b : ℚ)
  have hratio2 : (2 : ℚ) < ratio := by
    apply (lt_div_iff₀ hbQ).2
    exact_mod_cast ha2
  have hratio12 : ratio ≤ (12 : ℚ) := by
    apply (div_le_iff₀ hbQ).2
    exact_mod_cast ha12
  let i := queryIndex 16384 a b
  let r := queryResidual 16384 a b
  have hidx : originalQueryIndex ratio = i := by
    have h := congrArg Int.toNat (original_query_index_literal_divmod a b hb ha0)
    simpa only [Int.toNat_natCast,queryIndex,ratio,i] using h
  obtain ⟨_,hi12,_,_,hql,_⟩ := original_query_cell_geometry hratio2.le hratio12
  rw [hidx] at hi12 hql
  have hquot0 : 0 ≤ (a*16384)/b :=
    Int.ediv_nonneg (mul_nonneg ha0 (by norm_num)) hb.le
  have hquotMax : (a*16384)/b ≤ 196608 := by
    have hiZ : (i : ℤ) ≤ 196608 := by exact_mod_cast hi12
    simpa only [i,queryIndex,Int.toNat_of_nonneg hquot0] using hiZ
  refine ⟨hquot0,hquotMax,hi12,?_⟩
  intro hr
  have hw : queryCellWeight i ratio = (r : ℚ)/(b : ℚ) := by
    simpa only [hidx,queryResidual,ratio,r] using
      original_query_weight_literal_divmod a b hb ha0
  by_contra hn
  have hieq : i = 196608 := by omega
  have hratioGe : (12 : ℚ) ≤ ratio := by
    have hh := hql
    norm_num [hieq] at hh
    exact hh
  have hratioEq : ratio = 12 := le_antisymm hratio12 hratioGe
  have hwz : queryCellWeight i ratio = 0 := by
    norm_num [hieq,hratioEq,queryCellWeight]
  have hrz : r = 0 := by
    rw [hw] at hwz
    have hz := (div_eq_zero_iff.mp hwz).resolve_right (ne_of_gt hbQ)
    exact_mod_cast hz
  exact hr hrz

theorem numeratorTrace_safe (a b : ℤ) (hb : 0 < b)
    (ha2 : 2*b < a) (ha12 : a ≤ 12*b) :
    ∀ event ∈ (numeratorTrace a b).events, event.Safe := by
  obtain ⟨hq0,hqMax,hiMax,hnext⟩ := numerator_index_licence a b hb ha2 ha12
  by_cases hr : (a*16384)%b = 0
  · simp [numeratorTrace,hr,PointEvent.Safe,hb,hq0,hqMax,hiMax]
  · have hiNext := hnext hr
    simp [numeratorTrace,hr,PointEvent.Safe,hb,hq0,hqMax,hiMax,hiNext]

/-- All explicit primitive assertions and all denominator/index obligations
inside this complete point/numerator segment are discharged uniformly. -/
theorem pointTrace_safe (a b : ℤ) (hb : 0 < b) :
    ∀ event ∈ (pointTrace a b).events, event.Safe := by
  by_cases hlow : a ≤ 2*b
  · simp [pointTrace,hlow]
  · by_cases hhigh : a > 12*b
    · norm_num [pointTrace,hlow,hhigh,PointEvent.Safe]
    · have ha2 : 2*b < a := by omega
      have ha12 : a ≤ 12*b := by omega
      have ha : 0 < a := by omega
      have hn := numeratorTrace_safe a b hb ha2 ha12
      intro event he
      have hm : event ∈ (numeratorTrace a b).events ∨
          event ∈ [PointEvent.floorDivision ((numeratorTrace a b).value.lo*b) a,
            PointEvent.ceilingDivision ((numeratorTrace a b).value.hi*b) a] := by
        simpa [pointTrace,hlow,hhigh] using he
      rcases hm with hm | hm
      · exact hn event hm
      · simp only [List.mem_cons,List.mem_singleton] at hm
        rcases hm with rfl | rfl <;> exact ha

/-- A complete source-segment refinement theorem: exact L result plus all
logged primitive licences, with no finite guard or target estimate premise. -/
theorem point_segment_refines (a b : ℤ) (hb : 0 < b) :
    (pointTrace a b).value = point a b ∧
      ∀ event ∈ (pointTrace a b).events, event.Safe :=
  ⟨pointTrace_value a b,pointTrace_safe a b hb⟩

end ImbalancedChen.P2OriginalCompactPointPrimitiveTraceSourceOnly
