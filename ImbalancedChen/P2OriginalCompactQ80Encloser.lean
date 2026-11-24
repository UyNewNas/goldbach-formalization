import ImbalancedChen.P2OriginalCompactQ80Table
import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.P2HistoricI80DivisionSoundness
import ImbalancedChen.P2OriginalPrioritySerialQueue
import ImbalancedChen.P2OriginalCompactBoundaryCapFloor

/-!
SOURCE ONLY / UNCOMPILED / FULL LEAF SOUNDNESS OPEN.

Literal executable operations of certify_extended_prefix.py, including its
SieveTable(16384,12), Q80 log32, all minima, original Jensen option, symmetric
half mass and first/tail computations. There is no caller-supplied evaluator.
Memoization is omitted: it changes cost, not integer results. The definitions
are totalized outside the Python assertions; no validity of those inputs is
claimed. `sourceAssertions` and `tableAssertions` display remaining checks.

The separate analytic files prove actual table queries, original cap-floor
binding, empty/full-cap branches and original rounding steps. They DO NOT
prove the complete all-candidate enclosure or the historical endpoint. No
P160 substitute or original-charge comparison premise is introduced.
-/

namespace ImbalancedChen.P2OriginalCompactQ80EncloserSourceOnly

open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalPrioritySerialQueueSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalCompactBoundaryCapFloorSourceOnly

abbrev RawBox := SeedCell

def scale : ℤ := 2 ^ 80
def denominator : ℤ := 48000 * 2 ^ 24
def thetaInteger : ℤ := 481573208064
def muInteger : ℤ := 157286400000
def rhoInteger : ℤ := 159383552000
def cutoffInteger : ℤ := 8053063680
def theta : ℚ := 299 / 500
def rho : ℚ := 19 / 96
def cutoff : ℚ := 1 / 100

def up (n d : ℤ) : ℤ := -((-n) / d)
noncomputable def val (n : ℤ) : ℝ := (n : ℝ) / (scale : ℝ)

abbrev Node := P2HistoricSieveTableSemantics.HistoricNode
def initialNode : Node := ⟨0,0,scale,scale⟩
def trapLower (g j : ℕ) (x y : ℤ) : ℤ :=
  (x*(g : ℤ)/((j : ℤ)-1)+y*(g : ℤ)/(j : ℤ))/(2*(g : ℤ))
def trapUpper (g j : ℕ) (x y : ℤ) : ℤ :=
  up (up (x*(g : ℤ)) ((j : ℤ)-1)+up (y*(g : ℤ)) (j : ℤ)) (2*(g : ℤ))

def nodeUpdate (g i : ℕ) (old : ℕ → Node) : Node :=
  if i ≤ 2*g then initialNode else
  let j := i-g
  let p := old (i-1)
  let lo := trapLower g j (old (j-1)).hl (old j).hl
  let hi := trapUpper g j (old (j-1)).hh (old j).hh
  { ll := max p.ll (p.ll+lo-up scale (6*(g : ℤ)^3))
    lh := p.lh+hi
    hl := if i ≤ 3*g then scale else
      p.hl+trapLower g j (old (j-1)).ll (old j).ll
    hh := if i ≤ 3*g then scale else
      p.hh+trapUpper g j (old (j-1)).lh (old j).lh+up scale (12*(g : ℤ)^3) }

/-- A pure integer recursion, separately executable from the analytic
predecessor's noncomputable section. This is the complete table, not literals. -/
def sourceState (g : ℕ) : ℕ → (ℕ → Node) :=
  Nat.rec (motive := fun _ => ℕ → Node) (fun _ => initialNode)
    (fun k old i => if i = k+1 then nodeUpdate g (k+1) old else old i)

def sourceTable : ℕ → Node := sourceState 16384 (12*16384)

def sourceNumerator (a b : ℤ) : I80 :=
  let q := ((a*(16384 : ℤ))/b).toNat
  let r := (a*(16384 : ℤ)) % b
  if r = 0 then ⟨(sourceTable q).ll,(sourceTable q).lh⟩ else
    ⟨((sourceTable q).ll*(b-r)+(sourceTable (q+1)).ll*r)/b,
      up ((sourceTable q).lh*(b-r)+(sourceTable (q+1)).lh*r) b+
        up scale (8*(16384 : ℤ)^2)⟩

def point (a b : ℤ) : I80 :=
  if a ≤ 2*b then ⟨0,0⟩ else
  if a > 12*b then
    ⟨(sourceTable (12*16384)).ll/12,up (sourceTable (12*16384)).hh 12⟩ else
  let p := sourceNumerator a b
  ⟨p.lo*b/a,up (p.hi*b) a⟩

theorem sourceState_eq_historical (g n : ℕ) :
    sourceState g n = P2HistoricSieveTableSemantics.state g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      change (if i = n+1 then nodeUpdate g (n+1) (sourceState g n)
        else sourceState g n i) = _
      rw [ih]
      rfl

theorem sourceTable_eq_historical :
    sourceTable = P2HistoricSieveTableSemantics.table 16384 12 :=
  sourceState_eq_historical 16384 (12*16384)

theorem point_eq_historical (a b : ℤ) :
    point a b = P2HistoricSieveTableSemantics.point 16384 12 a b := by
  simp only [point,sourceNumerator,sourceTable_eq_historical]
  rfl

abbrev LogState := Certificates.P2HistoricLogPointInterpreter.OddState

def logSquare (ul uh : ℤ) : I80 := ⟨ul*ul/scale,up (uh*uh) scale⟩
def logStep (square : I80) (j : ℕ) (s : LogState) : LogState :=
  ⟨⟨s.power.lo*square.lo/scale,up (s.power.hi*square.hi) scale⟩,
    s.total.add ⟨s.power.lo/((2*j+1 : ℕ) : ℤ),up s.power.hi ((2*j+1 : ℕ) : ℤ)⟩⟩
def logLoop (square : I80) (ul uh : ℤ) : ℕ → LogState
  | 0 => ⟨⟨ul,uh⟩,I80.raw 0⟩
  | n+1 => logStep square n (logLoop square ul uh n)
def atanhBounds (ul uh : ℤ) : I80 :=
  let sq := logSquare ul uh
  let st := logLoop sq ul uh 32
  ⟨2*st.total.lo,2*st.total.hi+up (2*st.power.hi*scale) (65*(scale-sq.hi))⟩
def logTwo : I80 := atanhBounds (scale/3) (up scale 3)
def logPoint (q : ℤ) : I80 :=
  if q = scale then I80.raw 0 else
    let k := Certificates.P2HistoricLogRangeReduction.sourceShift q
    let rl := Certificates.P2HistoricLogRangeReduction.sourceRL q
    let rh := Certificates.P2HistoricLogRangeReduction.sourceRH q
    let lo := (rl-scale)*scale/(rh+scale)
    let hi := up ((rh-scale)*scale) (rl+scale)
    (atanhBounds lo hi).add
      (if 0 ≤ k then ⟨k*logTwo.lo,k*logTwo.hi⟩ else ⟨k*logTwo.hi,k*logTwo.lo⟩)
def logI (q : ℚ) : I80 :=
  let x := I80.point q
  ⟨(logPoint x.lo).lo,(logPoint x.hi).hi⟩

theorem logLoop_eq_historical (sq : I80) (ul uh : ℤ) (n : ℕ) :
    logLoop sq ul uh n =
      Certificates.P2HistoricLogPointInterpreter.oddLoop sq ul uh n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [logLoop,Certificates.P2HistoricLogPointInterpreter.oddLoop,ih]
      rfl

theorem atanhBounds_eq_historical (ul uh : ℤ) :
    atanhBounds ul uh =
      Certificates.P2HistoricLogPointInterpreter.atanhBounds ul uh := by
  simp only [atanhBounds,logLoop_eq_historical]
  rfl

theorem logPoint_eq_historical (q : ℤ) :
    logPoint q = Certificates.P2HistoricLogPointInterpreter.logPoint q := by
  simp only [logPoint,logTwo,atanhBounds_eq_historical]
  rfl

theorem logI_eq_historical (q : ℚ) :
    logI q = Certificates.P2HistoricLogPointInterpreter.logI q := by
  simp only [logI,logPoint_eq_historical]
  rfl

def dInteger (s : ℕ) : ℤ :=
  up ((sourceTable (s * 16384)).hh - (sourceTable (s * 16384)).ll) (s : ℤ)

/-- Python min(range(3,last+1)); the empty default is unreachable at a>=3b,
b>0. The first term is kept as the initial minimum, never the number zero. -/
def minimum (xs : List ℤ) : ℤ :=
  match xs with
  | [] => 0
  | x :: ys => ys.foldl min x

def decayIndices (a b : ℤ) : List ℕ :=
  (List.range 10).map (· + 3) |>.filter (fun s => decide ((s : ℤ) ≤ a / b))

def decayTerm (a b : ℤ) (s : ℕ) : ℤ :=
  up (dInteger s * (s : ℤ) * (s : ℤ) * b * b) (a * a)

def dUpper (a b : ℤ) : ℤ := minimum ((decayIndices a b).map (decayTerm a b))

def vLower (lo hi : ℤ) : ℤ :=
  min ((denominator + lo) / 2) ((57 * denominator - 96 * hi) / 64)

def vPointUpper (t : ℤ) : ℤ :=
  min (up (denominator + t) 2) (up (57 * denominator - 96 * t) 64)

def vUpper (lo hi : ℤ) : ℤ :=
  if lo ≤ muInteger ∧ muInteger ≤ hi then up (153 * denominator) 256
  else max (vPointUpper lo) (vPointUpper hi)

/-- Literal operand order x,y,xy,xyz,xz,yz. -/
def sumRanges (c : RawBox) : List (ℤ × ℤ) :=
  [(c.1 0,c.2 0), (c.1 1,c.2 1),
   (c.1 0+c.1 1,c.2 0+c.2 1),
   (c.1 0+c.1 1+c.1 2,c.2 0+c.2 1+c.2 2),
   (c.1 0+c.1 2,c.2 0+c.2 2),
   (c.1 1+c.1 2,c.2 1+c.2 2)]

/-- The final max with B is commuted into the fold seed. The accompanying
proof identifies this exactly with the author's original lower formula. -/
def phiRange (c : RawBox) : I80 :=
  if muInteger ≤ c.1 0 then
    ⟨min thetaInteger (vLower (c.1 0) (c.2 0)),
      min thetaInteger (vUpper (c.1 0) (c.2 0))⟩
  else
    ⟨min thetaInteger (((sumRanges c).map (fun p => vLower p.1 p.2)).foldr max
        ((153 * denominator - 96 * c.2 2) / 256)),
      min thetaInteger (((sumRanges c).map (fun p => vUpper p.1 p.2)).foldr max
        (up (153 * denominator - 96 * c.1 2) 256))⟩

def logarithmicWidth (lo hi : ℤ) : I80 :=
  logI ((hi : ℚ) / (lo : ℚ))

/-- Source has two specialized positive products, not general I.mul. -/
def densityMass (c : RawBox) : I80 :=
  let a := logarithmicWidth (c.1 0) (c.2 0)
  let b := logarithmicWidth (c.1 1) (c.2 1)
  let lo := a.lo * b.lo / scale
  let hi := up (a.hi * b.hi) scale
  let n := 4 * denominator * (c.2 2 - c.1 2)
  let d := c.1 2 * c.2 2
  ⟨lo * n / d, up (hi * n) d⟩

structure Plane where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  deriving DecidableEq, Repr

def affineExtreme (box : RawBox) (p : Plane) (maximum : Bool) : ℤ :=
  let endpoint := if maximum then box.2 else box.1
  let opposite := if maximum then box.1 else box.2
  p.a * denominator +
    p.b * (if 0 ≤ p.b then endpoint 0 else opposite 0) +
    p.c * (if 0 ≤ p.c then endpoint 1 else opposite 1) +
    p.d * (if 0 ≤ p.d then endpoint 2 else opposite 2)

def planeDifference (p q : Plane) : Plane :=
  ⟨p.a*q.e-q.a*p.e, p.b*q.e-q.b*p.e,
    p.c*q.e-q.c*p.e, p.d*q.e-q.d*p.e, 1⟩

def activeMinPlane (box : RawBox) (planes : List Plane) : Option Plane :=
  planes.find? (fun p => planes.all
    (fun q => decide (affineExtreme box (planeDifference p q) true ≤ 0)))

def vPlanes (b c d : ℤ) : List Plane :=
  [⟨1,b,c,d,2⟩,⟨57,-96*b,-96*c,-96*d,64⟩]

def planeDirections : List (ℤ × ℤ × ℤ) :=
  [(1,0,0),(0,1,0),(1,1,0),(1,1,1),(1,0,1),(0,1,1)]

def atMid (box : RawBox) (p : Plane) : ℤ :=
  p.a * denominator + p.b * ((box.1 0 + box.2 0) / 2) +
    p.c * ((box.1 1 + box.2 1) / 2) +
    p.d * ((box.1 2 + box.2 2) / 2)

def affineChoices (box : RawBox) : List Plane :=
  ((planeDirections.filterMap (fun p => activeMinPlane box (vPlanes p.1 p.2.1 p.2.2))) ++
    [⟨153,0,0,-96,256⟩]).filter
      (fun p => decide (affineExtreme box p true ≤ thetaInteger * p.e))

/-- Strict > preserves the first encountered plane on midpoint ties. The
above-mu source branch does not run the below-mu theta filter. -/
def affineCapLower (box : RawBox) : Option Plane :=
  if muInteger ≤ box.1 0 then some ⟨57,-96,0,0,64⟩ else
  match affineChoices box with
  | [] => none
  | first :: rest => some (rest.foldl (fun best p =>
      if atMid box p * best.e > atMid box best * p.e then p else best) first)

def outside (c : RawBox) : Prop :=
  c.2 0 < c.1 1 ∨ c.2 1 < c.1 2 ∨
    thetaInteger < c.1 0 + c.1 1 + 3 * c.1 2

instance (c : RawBox) : Decidable (outside c) := by unfold outside; infer_instance

def symmetricHalf (c : RawBox) : Prop :=
  c.1 0 = c.1 1 ∧ c.2 0 = c.2 1 ∧ c.2 2 ≤ c.1 1

instance (c : RawBox) : Decidable (symmetricHalf c) := by
  unfold symmetricHalf; infer_instance

def inside (c : RawBox) : Prop :=
  (c.2 1 ≤ c.1 0 ∨ symmetricHalf c) ∧ c.2 2 ≤ c.1 1 ∧
    c.2 0 + c.2 1 + 3 * c.2 2 ≤ thetaInteger

instance (c : RawBox) : Decidable (inside c) := by unfold inside; infer_instance

def aboveSymmetric (c : RawBox) : Prop :=
  muInteger ≤ c.1 0 ∧ symmetricHalf c

instance (c : RawBox) : Decidable (aboveSymmetric c) := by
  unfold aboveSymmetric; infer_instance

def oldLow (box : RawBox) (p : Plane) : ℚ :=
  ((p.a*denominator+(p.b-p.e)*box.2 0+(p.c-p.e)*box.2 1+
    (p.d-p.e)*box.2 2 : ℤ) : ℚ) / ((p.e*box.2 2 : ℤ) : ℚ)

def oldHigh (box : RawBox) (p : Plane) : ℚ :=
  ((p.a*denominator+(p.b-p.e)*box.1 0+(p.c-p.e)*box.1 1+
    (p.d-p.e)*box.1 2 : ℤ) : ℚ) / ((p.e*box.1 2 : ℤ) : ℚ)

def xMean (box : RawBox) : I80 := historicalDiv
  (I80.point ((box.2 0-box.1 0 : ℤ) : ℚ)) (logarithmicWidth (box.1 0) (box.2 0))
def yMean (box : RawBox) : I80 := historicalDiv
  (I80.point ((box.2 1-box.1 1 : ℤ) : ℚ)) (logarithmicWidth (box.1 1) (box.2 1))
def invZMean (box : RawBox) : I80 := I80.point
  (((box.1 2+box.2 2 : ℤ) : ℚ) / ((2*box.1 2*box.2 2 : ℤ) : ℚ))

def newMean (box : RawBox) : I80 :=
  let base := ((I80.point (thetaInteger : ℚ)).sub (xMean box)).sub (yMean box)
  (base.mul (invZMean box)).sub (I80.point 1)

def maxMean (box : RawBox) : I80 :=
  let lx := logarithmicWidth (box.1 0) (box.2 0)
  let numerator := (((I80.point (box.2 0 : ℚ)).mul lx).sub
    (I80.point (box.2 0 : ℚ))).add (I80.point (box.1 0 : ℚ))
  historicalDiv ((I80.point 2).mul numerator) (lx.mul lx)

def oldMean (box : RawBox) (p : Plane) : I80 :=
  if aboveSymmetric box then
    let base := (((I80.point (((57*denominator : ℤ) : ℚ)/64)).sub (xMean box)).sub
      (yMean box)).sub ((I80.point (3/2)).mul (maxMean box))
    (base.mul (invZMean box)).sub (I80.point 1)
  else
    let base := ((I80.point (((p.a*denominator : ℤ) : ℚ)/(p.e : ℚ))).add
      ((I80.point (((p.b-p.e : ℤ) : ℚ)/(p.e : ℚ))).mul (xMean box))).add
      ((I80.point (((p.c-p.e : ℤ) : ℚ)/(p.e : ℚ))).mul (yMean box))
    (base.mul (invZMean box)).add (I80.point (((p.d-p.e : ℤ) : ℚ)/(p.e : ℚ)))

def chordWeight (box : RawBox) (p : Plane) : I80 :=
  let w := historicalDiv ((oldMean box p).sub (I80.point (oldLow box p)))
    (I80.point (oldHigh box p - oldLow box p))
  ⟨max 0 w.lo, min scale w.hi⟩

def chordLower (box : RawBox) (p : Plane) : ℤ :=
  let lo := oldLow box p
  let hi := oldHigh box p
  let fl := (point lo.num (lo.den : ℤ)).lo
  let fh := (point hi.num (hi.den : ℤ)).lo
  if lo = hi then fl else
    ((I80.raw fl).add ((chordWeight box p).mul (I80.raw (fh-fl)))).lo

def jensenEligible (box : RawBox) (p : Plane) : Prop :=
  p.b ≤ p.e ∧ p.c ≤ p.e ∧
    0 < p.a*denominator+(p.b-p.e)*box.2 0+(p.c-p.e)*box.2 1 ∧
    ¬ (oldLow box p < 2 ∧ 2 < oldHigh box p)

instance (box : RawBox) (p : Plane) : Decidable (jensenEligible box p) := by
  unfold jensenEligible; infer_instance

def jensenDifferenceUpper (box : RawBox) : Option ℤ := do
  let p ← affineCapLower box
  if jensenEligible box p then
    let nh := (point (newMean box).hi scale).hi
    if oldHigh box p ≤ 2 then some nh
    else some (max 0 (nh - chordLower box p))
  else none

def lowerDifference (box : RawBox) : ℤ :=
  let cap := phiRange box
  let nlo := thetaInteger-box.2 0-box.2 1-box.2 2
  let olo := cap.lo-box.2 0-box.2 1-box.2 2
  let ohi := cap.hi-box.1 0-box.1 1-box.1 2
  let dl := if inside box then
    max 0 ((point nlo (box.2 2)).lo-(point ohi (box.1 2)).hi) else 0
  if inside box ∧ 2*box.2 2 ≤ olo then
    max dl (max 0 ((point (ohi*box.2 2+(thetaInteger-cap.hi)*box.1 2)
      (box.1 2*box.2 2)).lo-(point ohi (box.1 2)).hi))
  else dl

def upperBeforeJensen (box : RawBox) : ℤ :=
  let cap := phiRange box
  let nhi := thetaInteger-box.1 0-box.1 1-box.1 2
  let olo := cap.lo-box.2 0-box.2 1-box.2 2
  let dh := max 0 ((point nhi (box.1 2)).hi-(point olo (box.2 2)).lo)
  let sa := max (2*box.2 2) olo
  let paired := max 0 ((point (sa*box.1 2+(thetaInteger-cap.lo)*box.2 2)
    (box.2 2*box.1 2)).hi-(point sa (box.2 2)).lo)
  let dh := min dh paired
  let dh := if 3*box.2 2 ≤ olo then min dh (dUpper olo (box.2 2)) else dh
  if 4*box.2 2 ≤ olo then min dh
    (up (dUpper (olo-box.2 2) (box.2 2)*(thetaInteger-cap.lo)*box.2 2)
      (box.1 2*olo))
  else dh

def upperDifference (box : RawBox) : ℤ :=
  let dh := upperBeforeJensen box
  if inside box then
    match jensenDifferenceUpper box with
    | none => dh
    | some j => min dh j
  else dh

def chargedMass (box : RawBox) : I80 :=
  let m := densityMass box
  if symmetricHalf box then ⟨m.lo/2,up m.hi 2⟩ else m

inductive Kind where
  | outside | fullCap | zeroLoss | interior | boundary
  deriving DecidableEq, Repr

structure Result where
  bounds : Bounds
  kind : Kind

def enclosureResult (box : RawBox) : Result :=
  if outside box then ⟨⟨0,0⟩,.outside⟩ else
  if thetaInteger ≤ (phiRange box).lo then ⟨⟨0,0⟩,.fullCap⟩ else
  if upperBeforeJensen box = 0 then ⟨⟨0,0⟩,.zeroLoss⟩ else
    let mass := chargedMass box
    ⟨⟨lowerDifference box*mass.lo/scale,
      up (upperDifference box*mass.hi) scale⟩,
      if inside box then .interior else .boundary⟩

/-- Concrete K queue interface. All zero/empty leaves retain their bounds. -/
def enclose (box : RawBox) : Bounds := (enclosureResult box).bounds

/-- Source first_integral(20), preserving the recurrence and the consecutive
even/odd partial sums. No stored historical output is accepted here. -/
def firstSeries : ℕ → ℚ × ℚ
  | 0 => (1/2,0)
  | n+1 =>
    let prev := firstSeries n
    let k := n+1
    let coefficient := if k = 1 then (1/2 : ℚ)
      else prev.1/2 + 1/(2*(k : ℚ))
    let term := coefficient * (theta/rho-3)^(k+1)/((k+1 : ℕ) : ℚ)
    (coefficient,prev.2 + if k % 2 = 1 then term else -term)

def firstBounds : Bounds :=
  let lo := 4 * (firstSeries 20).2 / theta
  let hi := 4 * (firstSeries 21).2 / theta
  ⟨lo.num*scale/(lo.den : ℤ), up (hi.num*scale) (hi.den : ℤ)⟩

/-- Literal tail_upper with s0=10 and the source I operations in order. -/
def tailInterval : I80 :=
  let d0 := I80.raw (dInteger 10)
  let ell := logI (rho/cutoff)
  let poly := (ell.mul ell).add ((I80.point 2).mul ell) |>.add (I80.point 2)
  historicalDiv
    (((((I80.point 2).mul d0).mul (I80.point (10^2))).mul
      (I80.point cutoff)).mul poly)
    (I80.point ((rho-cutoff)^2))

def tailUpper : ℤ := tailInterval.hi
def fixedLower : ℚ := 4/theta + (firstBounds.lower : ℚ)/(scale : ℚ)
def fixedUpper : ℚ := 4/theta + ((firstBounds.upper+tailUpper : ℤ) : ℚ)/(scale : ℚ)

/-- Exact initialization assertions, not an asserted successful guard. -/
def tableAssertions : Bool :=
  ((List.range 10).map (· + 3)).all (fun s => decide (0 < dInteger s)) &&
  ([5/2,3,7/2,4] : List ℚ).all (fun s =>
    let p := point s.num (s.den : ℤ)
    let exact := historicalDiv
      (logI (s-1)) (I80.point s)
    decide (p.lo ≤ exact.lo ∧ exact.lo ≤ exact.hi ∧ exact.hi ≤ p.hi))

/-- Selected Jensen I.__truediv__ assertions. These are operation guards,
not a hypothesis that the claimed integral estimate is already true. -/
def jensenAssertions (box : RawBox) : Prop :=
  match affineCapLower box with
  | none => True
  | some p => jensenEligible box p →
    0 < (logarithmicWidth (box.1 0) (box.2 0)).lo ∧
    0 < (logarithmicWidth (box.1 1) (box.2 1)).lo ∧
    (aboveSymmetric box → oldHigh box p > 2 →
      0 < ((logarithmicWidth (box.1 0) (box.2 0)).mul
        (logarithmicWidth (box.1 0) (box.2 0))).lo) ∧
    (oldHigh box p > 2 → oldLow box p ≠ oldHigh box p →
      0 < (I80.point (oldHigh box p-oldLow box p)).lo)

/-- Explicit outstanding source checks at a cell. Constructor endpoint
order and internal log guards follow from primitive correctness where proved;
this predicate is NOT claimed to be a complete Python refinement theorem. -/
def sourceAssertions (box : RawBox) : Prop :=
  outside box ∨
    ((box.2 0 ≤ muInteger ∨ muInteger ≤ box.1 0) ∧
      (thetaInteger ≤ (phiRange box).lo ∨
        (box.2 0+box.2 1 < (phiRange box).lo ∧
          (upperBeforeJensen box = 0 ∨
            ((inside box → jensenAssertions box) ∧
              0 ≤ (enclose box).lower ∧ (enclose box).lower ≤ (enclose box).upper)))))

theorem fixedUpper_source_formula :
    fixedUpper = 4/(299/500 : ℚ) +
      ((firstBounds.upper+tailUpper : ℤ) : ℚ)/(2^80 : ℚ) := by
  rfl

theorem enclose_outside (box : RawBox) (h : outside box) :
    enclose box = ⟨0,0⟩ := by simp [enclose,enclosureResult,h]

theorem enclose_fullCap (box : RawBox) (h : thetaInteger ≤ (phiRange box).lo) :
    enclose box = ⟨0,0⟩ := by
  by_cases ho : outside box <;> simp [enclose,enclosureResult,ho,h]

theorem enclose_zeroLoss (box : RawBox) (h : upperBeforeJensen box = 0) :
    enclose box = ⟨0,0⟩ := by
  by_cases ho : outside box
  · exact enclose_outside box ho
  · by_cases hc : thetaInteger ≤ (phiRange box).lo <;>
      simp [enclose,enclosureResult,ho,hc,h]

end ImbalancedChen.P2OriginalCompactQ80EncloserSourceOnly
