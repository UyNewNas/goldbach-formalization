import ImbalancedChen.P2OriginalCompactQ80ArrayTable

/-!
SOURCE ONLY / UNCOMPILED / ALL FINITE GUARDS UNEVALUATED.

Cache-backed specialization of the literal original Q80 interpreter. The
explicit Array argument permits a driver to build and share the table once.
All signed divisions, operand order, minima, guards and early returns are
copied from the original interpreter, then identified by symbolic proofs.
No analytic enclosure estimate or historical numerical endpoint is assumed
or asserted by the implementation-equivalence theorems in this file.
-/
namespace ImbalancedChen.P2OriginalCompactQ80CacheEncloserSourceOnly

open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalCompactQ80EncloserSourceOnly

abbrev tableArray := P2OriginalCompactQ80ArrayTableSourceOnly.tableArray
abbrev lookup := P2OriginalCompactQ80ArrayTableSourceOnly.lookup

theorem tableArray_lookup : lookup tableArray = sourceTable :=
  P2OriginalCompactQ80ArrayTableSourceOnly.tableArray_lookup

namespace WithTable

def sourceNumerator (nodes : Array Node) (a b : ℤ) : I80 :=
  let q := ((a*(16384 : ℤ))/b).toNat
  let r := (a*(16384 : ℤ)) % b
  if r = 0 then ⟨(lookup nodes q).ll,(lookup nodes q).lh⟩ else
    ⟨((lookup nodes q).ll*(b-r)+(lookup nodes (q+1)).ll*r)/b,
      up ((lookup nodes q).lh*(b-r)+(lookup nodes (q+1)).lh*r) b+
        up scale (8*(16384 : ℤ)^2)⟩

def point (nodes : Array Node) (a b : ℤ) : I80 :=
  if a ≤ 2*b then ⟨0,0⟩ else
  if a > 12*b then
    ⟨(lookup nodes (12*16384)).ll/12,up (lookup nodes (12*16384)).hh 12⟩ else
  let p := sourceNumerator nodes a b
  ⟨p.lo*b/a,up (p.hi*b) a⟩

def dInteger (nodes : Array Node) (s : ℕ) : ℤ :=
  up ((lookup nodes (s * 16384)).hh - (lookup nodes (s * 16384)).ll) (s : ℤ)

def decayTerm (nodes : Array Node) (a b : ℤ) (s : ℕ) : ℤ :=
  up (dInteger nodes s * (s : ℤ) * (s : ℤ) * b * b) (a * a)

def dUpper (nodes : Array Node) (a b : ℤ) : ℤ :=
  minimum ((decayIndices a b).map (decayTerm nodes a b))

def chordLower (nodes : Array Node) (box : RawBox) (p : Plane) : ℤ :=
  let lo := oldLow box p
  let hi := oldHigh box p
  let fl := (point nodes lo.num (lo.den : ℤ)).lo
  let fh := (point nodes hi.num (hi.den : ℤ)).lo
  if lo = hi then fl else
    ((I80.raw fl).add ((chordWeight box p).mul (I80.raw (fh-fl)))).lo

def jensenDifferenceUpper (nodes : Array Node) (box : RawBox) : Option ℤ := do
  let p ← affineCapLower box
  if jensenEligible box p then
    let nh := (point nodes (newMean box).hi scale).hi
    if oldHigh box p ≤ 2 then some nh
    else some (max 0 (nh - chordLower nodes box p))
  else none

def lowerDifference (nodes : Array Node) (box : RawBox) : ℤ :=
  let cap := phiRange box
  let nlo := thetaInteger-box.2 0-box.2 1-box.2 2
  let olo := cap.lo-box.2 0-box.2 1-box.2 2
  let ohi := cap.hi-box.1 0-box.1 1-box.1 2
  let dl := if inside box then
    max 0 ((point nodes nlo (box.2 2)).lo-(point nodes ohi (box.1 2)).hi) else 0
  if inside box ∧ 2*box.2 2 ≤ olo then
    max dl (max 0 ((point nodes (ohi*box.2 2+(thetaInteger-cap.hi)*box.1 2)
      (box.1 2*box.2 2)).lo-(point nodes ohi (box.1 2)).hi))
  else dl

def upperBeforeJensen (nodes : Array Node) (box : RawBox) : ℤ :=
  let cap := phiRange box
  let nhi := thetaInteger-box.1 0-box.1 1-box.1 2
  let olo := cap.lo-box.2 0-box.2 1-box.2 2
  let dh := max 0 ((point nodes nhi (box.1 2)).hi-(point nodes olo (box.2 2)).lo)
  let sa := max (2*box.2 2) olo
  let paired := max 0 ((point nodes (sa*box.1 2+(thetaInteger-cap.lo)*box.2 2)
    (box.2 2*box.1 2)).hi-(point nodes sa (box.2 2)).lo)
  let dh := min dh paired
  let dh := if 3*box.2 2 ≤ olo then min dh (dUpper nodes olo (box.2 2)) else dh
  if 4*box.2 2 ≤ olo then min dh
    (up (dUpper nodes (olo-box.2 2) (box.2 2)*(thetaInteger-cap.lo)*box.2 2)
      (box.1 2*olo))
  else dh

def upperDifference (nodes : Array Node) (box : RawBox) : ℤ :=
  let dh := upperBeforeJensen nodes box
  if inside box then
    match jensenDifferenceUpper nodes box with
    | none => dh
    | some j => min dh j
  else dh

def enclosureResult (nodes : Array Node) (box : RawBox) : Result :=
  if outside box then ⟨⟨0,0⟩,.outside⟩ else
  if thetaInteger ≤ (phiRange box).lo then ⟨⟨0,0⟩,.fullCap⟩ else
  if upperBeforeJensen nodes box = 0 then ⟨⟨0,0⟩,.zeroLoss⟩ else
    let mass := chargedMass box
    ⟨⟨lowerDifference nodes box*mass.lo/scale,
      up (upperDifference nodes box*mass.hi) scale⟩,
      if inside box then .interior else .boundary⟩

def enclose (nodes : Array Node) (box : RawBox) : Bounds :=
  (enclosureResult nodes box).bounds

def tailInterval (nodes : Array Node) : I80 :=
  let d0 := I80.raw (dInteger nodes 10)
  let ell := logI (rho/cutoff)
  let poly := (ell.mul ell).add ((I80.point 2).mul ell) |>.add (I80.point 2)
  historicalDiv
    (((((I80.point 2).mul d0).mul (I80.point (10^2))).mul
      (I80.point cutoff)).mul poly)
    (I80.point ((rho-cutoff)^2))

def tailUpper (nodes : Array Node) : ℤ := (tailInterval nodes).hi

def fixedUpper (nodes : Array Node) : ℚ :=
  4/theta + ((firstBounds.upper+tailUpper nodes : ℤ) : ℚ)/(scale : ℚ)

def tableAssertions (nodes : Array Node) : Bool :=
  ((List.range 10).map (· + 3)).all (fun s => decide (0 < dInteger nodes s)) &&
  ([5/2,3,7/2,4] : List ℚ).all (fun s =>
    let p := point nodes s.num (s.den : ℤ)
    let exact := historicalDiv
      (logI (s-1)) (I80.point s)
    decide (p.lo ≤ exact.lo ∧ exact.lo ≤ exact.hi ∧ exact.hi ≤ p.hi))

def sourceAssertions (nodes : Array Node) (box : RawBox) : Prop :=
  outside box ∨
    ((box.2 0 ≤ muInteger ∨ muInteger ≤ box.1 0) ∧
      (thetaInteger ≤ (phiRange box).lo ∨
        (box.2 0+box.2 1 < (phiRange box).lo ∧
          (upperBeforeJensen nodes box = 0 ∨
            ((inside box → jensenAssertions box) ∧
              0 ≤ (enclose nodes box).lower ∧
                (enclose nodes box).lower ≤ (enclose nodes box).upper)))))

instance sourceAssertionsDecidable (nodes : Array Node) (box : RawBox) :
    Decidable (sourceAssertions nodes box) := by
  unfold sourceAssertions P2OriginalCompactQ80EncloserSourceOnly.jensenAssertions
  cases affineCapLower box <;> infer_instance

def sourceCheck (nodes : Array Node) (box : RawBox) : Bool :=
  decide (sourceAssertions nodes box)

theorem sourceNumerator_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    sourceNumerator nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceNumerator := by
  funext a b
  simp only [sourceNumerator, P2OriginalCompactQ80EncloserSourceOnly.sourceNumerator, h]

theorem point_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    point nodes = P2OriginalCompactQ80EncloserSourceOnly.point := by
  funext a b
  simp only [point, P2OriginalCompactQ80EncloserSourceOnly.point,
    sourceNumerator_eq nodes h, h]

theorem dInteger_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    dInteger nodes = P2OriginalCompactQ80EncloserSourceOnly.dInteger := by
  funext s
  simp only [dInteger, P2OriginalCompactQ80EncloserSourceOnly.dInteger, h]

theorem decayTerm_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    decayTerm nodes = P2OriginalCompactQ80EncloserSourceOnly.decayTerm := by
  funext a b s
  simp only [decayTerm, P2OriginalCompactQ80EncloserSourceOnly.decayTerm, dInteger_eq nodes h]

theorem dUpper_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    dUpper nodes = P2OriginalCompactQ80EncloserSourceOnly.dUpper := by
  funext a b
  simp only [dUpper, P2OriginalCompactQ80EncloserSourceOnly.dUpper, decayTerm_eq nodes h]

theorem chordLower_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    chordLower nodes = P2OriginalCompactQ80EncloserSourceOnly.chordLower := by
  funext box p
  simp only [chordLower, P2OriginalCompactQ80EncloserSourceOnly.chordLower, point_eq nodes h]

theorem jensenDifferenceUpper_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    jensenDifferenceUpper nodes =
      P2OriginalCompactQ80EncloserSourceOnly.jensenDifferenceUpper := by
  funext box
  simp only [jensenDifferenceUpper,
    P2OriginalCompactQ80EncloserSourceOnly.jensenDifferenceUpper,
    point_eq nodes h, chordLower_eq nodes h]

theorem lowerDifference_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    lowerDifference nodes = P2OriginalCompactQ80EncloserSourceOnly.lowerDifference := by
  funext box
  simp only [lowerDifference, P2OriginalCompactQ80EncloserSourceOnly.lowerDifference,
    point_eq nodes h]

theorem upperBeforeJensen_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    upperBeforeJensen nodes = P2OriginalCompactQ80EncloserSourceOnly.upperBeforeJensen := by
  funext box
  simp only [upperBeforeJensen, P2OriginalCompactQ80EncloserSourceOnly.upperBeforeJensen,
    point_eq nodes h, dUpper_eq nodes h]

theorem upperDifference_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    upperDifference nodes = P2OriginalCompactQ80EncloserSourceOnly.upperDifference := by
  funext box
  simp only [upperDifference, P2OriginalCompactQ80EncloserSourceOnly.upperDifference,
    upperBeforeJensen_eq nodes h, jensenDifferenceUpper_eq nodes h]

theorem enclosureResult_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    enclosureResult nodes = P2OriginalCompactQ80EncloserSourceOnly.enclosureResult := by
  funext box
  simp only [enclosureResult, P2OriginalCompactQ80EncloserSourceOnly.enclosureResult,
    upperBeforeJensen_eq nodes h, lowerDifference_eq nodes h, upperDifference_eq nodes h]

theorem enclose_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    enclose nodes = P2OriginalCompactQ80EncloserSourceOnly.enclose := by
  funext box
  simp only [enclose, P2OriginalCompactQ80EncloserSourceOnly.enclose,
    enclosureResult_eq nodes h]

theorem tailInterval_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    tailInterval nodes = P2OriginalCompactQ80EncloserSourceOnly.tailInterval := by
  simp only [tailInterval, P2OriginalCompactQ80EncloserSourceOnly.tailInterval, dInteger_eq nodes h]

theorem tailUpper_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    tailUpper nodes = P2OriginalCompactQ80EncloserSourceOnly.tailUpper := by
  simp only [tailUpper, P2OriginalCompactQ80EncloserSourceOnly.tailUpper, tailInterval_eq nodes h]

theorem fixedUpper_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    fixedUpper nodes = P2OriginalCompactQ80EncloserSourceOnly.fixedUpper := by
  simp only [fixedUpper, P2OriginalCompactQ80EncloserSourceOnly.fixedUpper, tailUpper_eq nodes h]

theorem tableAssertions_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    tableAssertions nodes = P2OriginalCompactQ80EncloserSourceOnly.tableAssertions := by
  simp only [tableAssertions, P2OriginalCompactQ80EncloserSourceOnly.tableAssertions,
    dInteger_eq nodes h, point_eq nodes h]

theorem sourceAssertions_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    sourceAssertions nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions := by
  funext box
  simp only [sourceAssertions, P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions,
    upperBeforeJensen_eq nodes h, enclose_eq nodes h]

end WithTable

abbrev encloseWith := WithTable.enclose
abbrev fixedUpperWith := WithTable.fixedUpper
abbrev tableAssertionsWith := WithTable.tableAssertions
abbrev sourceAssertionsWith := WithTable.sourceAssertions
abbrev sourceCheckWith := WithTable.sourceCheck

theorem encloseWith_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    encloseWith nodes = P2OriginalCompactQ80EncloserSourceOnly.enclose :=
  WithTable.enclose_eq nodes h

theorem fixedUpperWith_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    fixedUpperWith nodes = P2OriginalCompactQ80EncloserSourceOnly.fixedUpper :=
  WithTable.fixedUpper_eq nodes h

theorem tableAssertionsWith_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    tableAssertionsWith nodes = P2OriginalCompactQ80EncloserSourceOnly.tableAssertions :=
  WithTable.tableAssertions_eq nodes h

theorem sourceAssertionsWith_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    sourceAssertionsWith nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions :=
  WithTable.sourceAssertions_eq nodes h

/-- Cached queries retain the actual normalized lower-factor enclosure of
the original maximum-twelve Q80 interpreter. Full leaf soundness is separate. -/
theorem pointWith_contains_actual (nodes : Array Node) (h : lookup nodes = sourceTable)
    (a b : ℤ) (hb : 0 < b) :
    (WithTable.point nodes a b).Contains
      (actualExtendedThirdLowerFactor ((a : ℝ) / (b : ℝ))) := by
  rw [WithTable.point_eq nodes h,
    P2OriginalCompactQ80EncloserSourceOnly.point_eq_historical]
  exact P2OriginalCompactQ80TableSourceOnly.point12_contains_actual a b hb

instance originalSourceAssertionsDecidable (box : RawBox) :
    Decidable (P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions box) := by
  unfold P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions
    P2OriginalCompactQ80EncloserSourceOnly.jensenAssertions
  cases affineCapLower box <;> infer_instance

theorem sourceCheckWith_eq (nodes : Array Node) (h : lookup nodes = sourceTable) :
    sourceCheckWith nodes =
      fun box => decide (P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions box) := by
  funext box
  by_cases hs : P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions box
  · have hs' : sourceAssertionsWith nodes box := by
      simpa only [sourceAssertionsWith_eq nodes h] using hs
    simp only [sourceCheckWith, WithTable.sourceCheck, hs, hs', decide_true]
  · have hs' : ¬ sourceAssertionsWith nodes box := by
      simpa only [sourceAssertionsWith_eq nodes h] using hs
    simp only [sourceCheckWith, WithTable.sourceCheck, hs, hs', decide_false]

/-- Closed convenience specialization. The fast driver binds the explicit
Array and fixedUpper once, rather than rebuilding them at individual calls. -/
def fastEnclose : RawBox → Bounds :=
  let nodes := tableArray
  encloseWith nodes

def fastFixedUpper : ℚ := fixedUpperWith tableArray
def fastTableAssertions : Bool := tableAssertionsWith tableArray
def fastSourceCheck : RawBox → Bool := sourceCheckWith tableArray

theorem fastEnclose_eq : fastEnclose = P2OriginalCompactQ80EncloserSourceOnly.enclose :=
  encloseWith_eq tableArray tableArray_lookup

theorem fastFixedUpper_eq : fastFixedUpper = P2OriginalCompactQ80EncloserSourceOnly.fixedUpper :=
  fixedUpperWith_eq tableArray tableArray_lookup

theorem fastTableAssertions_eq :
    fastTableAssertions = P2OriginalCompactQ80EncloserSourceOnly.tableAssertions :=
  tableAssertionsWith_eq tableArray tableArray_lookup

theorem fastSourceCheck_eq (box : RawBox) : fastSourceCheck box =
    decide (P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions box) :=
  congrFun (sourceCheckWith_eq tableArray tableArray_lookup) box

end ImbalancedChen.P2OriginalCompactQ80CacheEncloserSourceOnly
