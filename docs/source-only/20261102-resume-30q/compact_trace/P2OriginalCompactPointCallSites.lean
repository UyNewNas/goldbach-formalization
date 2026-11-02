import ImbalancedChen.P2OriginalCompactMainCallTrace
import ImbalancedChen.P2OriginalCompactPointPrimitiveTrace

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED / FINITE TRACES UNEVALUATED.

Bind the complete point/numerator primitive segment to every semantic
SieveTable.point call in the original fixed-argument producer. This records
the original Python's eager queries, including fnlo and fohi even where the
lazy L expressions do not need their returned values. Each site is licensed
without a new guard premise. This is the point-call projection of the source
trace; intervening d_upper, I, log, arithmetic and cache events are not claimed
to be logged by this list.
-/
namespace ImbalancedChen.P2OriginalCompactPointCallSitesSourceOnly

open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P2OriginalCompactMainCallTraceSourceOnly
open P2OriginalCompactPointPrimitiveTraceSourceOnly

abbrev PointCall := ℤ × ℤ

/-- Python enclosure lines 296-317, in its eager execution order. The four
initial point calls occur before the inside test and before zero_loss.
The two correlated-lower calls also occur before the zero_loss exit. -/
def preJensenPointCalls (box : RawBox) : List PointCall :=
  let cap := phiRange box
  let nlo := thetaInteger-box.2 0-box.2 1-box.2 2
  let nhi := thetaInteger-box.1 0-box.1 1-box.1 2
  let olo := cap.lo-box.2 0-box.2 1-box.2 2
  let ohi := cap.hi-box.1 0-box.1 1-box.1 2
  let sa := max (2*box.2 2) olo
  [(nlo,box.2 2),(nhi,box.1 2),(olo,box.2 2),(ohi,box.1 2),
    (sa*box.1 2+(thetaInteger-cap.lo)*box.2 2,box.2 2*box.1 2),
    (sa,box.2 2)] ++
    if inside box ∧ 2*box.2 2 ≤ olo then
      [(ohi*box.2 2+(thetaInteger-cap.hi)*box.1 2,box.1 2*box.2 2),
        (ohi,box.1 2)]
    else []

/-- Point calls inside the actual Jensen branch, retaining fl then fh even
when old_lo=old_hi. Other operations in that branch are not point calls. -/
def jensenPointCalls (box : RawBox) : List PointCall :=
  match affineCapLower box with
  | none => []
  | some p =>
      if jensenEligible box p then
        [((newMean box).hi,scale)] ++
          if oldHigh box p ≤ 2 then [] else
            [((oldLow box p).num,((oldLow box p).den : ℤ)),
              ((oldHigh box p).num,((oldHigh box p).den : ℤ))]
      else []

/-- The complete point-call projection of one original enclosure call.
Early returns suppress only queries which Python actually skips. -/
def enclosurePointCalls (box : RawBox) : List PointCall :=
  if outside box then [] else
  if thetaInteger ≤ (phiRange box).lo then [] else
    preJensenPointCalls box ++
      if upperBeforeJensen box = 0 then [] else
        if inside box then jensenPointCalls box else []

theorem preJensenPointCalls_denominator (box : RawBox) (g : Geometry box) :
    ∀ query ∈ preJensenPointCalls box, 0 < query.2 := by
  have hz0 := g.raw_positive (2 : Fin 3)
  have hz1 : 0 < box.2 2 := hz0.trans (g.width 2)
  have hprod0 := mul_pos hz0 hz1
  have hprod1 := mul_pos hz1 hz0
  by_cases hc : inside box ∧
      2*box.2 2 ≤ (phiRange box).lo-box.2 0-box.2 1-box.2 2 <;>
    simp [preJensenPointCalls,hc,hz0,hz1,hprod0,hprod1]

theorem jensenPointCalls_denominator (box : RawBox) :
    ∀ query ∈ jensenPointCalls box, 0 < query.2 := by
  have hs : (0 : ℤ) < scale := by norm_num [scale]
  have hden (q : ℚ) : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  cases hp : affineCapLower box with
  | none => simp [jensenPointCalls,hp]
  | some p =>
      by_cases he : jensenEligible box p
      · by_cases hh : oldHigh box p ≤ 2 <;>
          simp [jensenPointCalls,hp,he,hh,hs,hden]
      · simp [jensenPointCalls,hp,he]

theorem enclosurePointCalls_denominator (box : RawBox) (g : Geometry box) :
    ∀ query ∈ enclosurePointCalls box, 0 < query.2 := by
  have hpre := preJensenPointCalls_denominator box g
  have hjensen := jensenPointCalls_denominator box
  by_cases ho : outside box
  · simp [enclosurePointCalls,ho]
  · by_cases hc : thetaInteger ≤ (phiRange box).lo
    · simp [enclosurePointCalls,ho,hc]
    · by_cases hz : upperBeforeJensen box = 0
      · simpa [enclosurePointCalls,ho,hc,hz] using hpre
      · by_cases hi : inside box
        · simpa [enclosurePointCalls,ho,hc,hz,hi] using And.intro hpre hjensen
        · simpa [enclosurePointCalls,ho,hc,hz,hi] using hpre

/-- The four constructor diagnostic calls precede all seed calls. -/
def initializationPointCalls : List PointCall :=
  ([5/2,3,7/2,4] : List ℚ).map fun q => (q.num,(q.den : ℤ))

def originalPointCalls : List PointCall :=
  initializationPointCalls ++ originalCallTrace.flatMap enclosurePointCalls

/-- One no-guard-premise statement covers constructor, seed, retired-parent
history, every zero/empty child, pre-Jensen and selected Jensen point calls. -/
theorem originalPointCalls_denominator :
    ∀ query ∈ originalPointCalls, 0 < query.2 := by
  intro query hq
  rcases List.mem_append.mp hq with hinit | hrun
  · obtain ⟨q,_,hq⟩ := List.mem_map.mp hinit
    subst query
    exact_mod_cast q.den_pos
  · obtain ⟨box,hbox,hquery⟩ := List.mem_flatMap.mp hrun
    exact enclosurePointCalls_denominator box
      (originalCallTrace_geometry box hbox) query hquery

/-- Every logged point site has exactly its L point value, and all explicit
point/numerator assertions, divisions and initialized-array reads are safe.
The trace and finite original run are never evaluated by this proof. -/
theorem originalPointCalls_refine : ∀ query ∈ originalPointCalls,
    (pointTrace query.1 query.2).value = point query.1 query.2 ∧
      ∀ event ∈ (pointTrace query.1 query.2).events, event.Safe := by
  intro query hq
  exact point_segment_refines query.1 query.2 (originalPointCalls_denominator query hq)

end ImbalancedChen.P2OriginalCompactPointCallSitesSourceOnly
