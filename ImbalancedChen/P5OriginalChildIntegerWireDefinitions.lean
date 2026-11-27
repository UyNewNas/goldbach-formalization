import ImbalancedChen.P5OldFifthChildGapIntegral

/-! Exact original producer integer definitions extracted for consumers.
No original certificate theorem or stored data claim is included here. -/
namespace ImbalancedChen.P5OriginalChildIntegerWireBinding

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OldFifthExact64ChildTiling P5OldFifthChildGapIntegral
open P5OldFifthFrozenUpperSurrogate

/-- Source widths for divisions=(2,2,2,2,4), independent of the geometry API. -/
def wireWidth (i : Fin 5) : ℤ := ![2, 2, 2, 2, 1] i

def wireLo (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℤ :=
  4 * raw.lo i + wireWidth i * ((c i).val : ℤ)

def wireHi (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℤ :=
  wireLo raw c i + wireWidth i

/-- Exact source product((0,1),repeat=5) order: last coordinate is fastest. -/
def producerBits : List Word :=
  [false, true].flatMap fun e0 =>
  [false, true].flatMap fun e1 =>
  [false, true].flatMap fun e2 =>
  [false, true].flatMap fun e3 =>
  [false, true].map fun e4 => (e0, e1, e2, e3, e4)

def vertexNumer (raw : FifthWireRow) (c : ChildIndex) (w : Word) (i : Fin 5) : ℤ :=
  wireLo raw c i + if wordChoice w i then wireWidth i else 0

/-- Original parent_picks INTEGER score columns; numpy.argmin tie order
is A then C then cap. These are not the rational sourcePick definition. -/
def originalPick (raw : FifthWireRow) (I : OldMask) : Fin 3 :=
  let ss : ℤ := ∑ i ∈ I, (2 * raw.lo i.castSucc + 1)
  let a := 32 * raw.grid + 16 * ss
  let c := 57 * raw.grid - 48 * ss
  let k := 153 * raw.grid / 4
  if a ≤ c ∧ a ≤ k then 0 else if c ≤ k then 1 else 2

/-- Source geometry uses n=1600 and the common affine scale32*n. -/
def oldPlaneNumer (pick : Fin 3) (ss : ℤ) : ℤ :=
  if pick.val = 0 then 25600 + 16 * ss
  else if pick.val = 1 then 45600 - 48 * ss else 30600

def oldNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  let seed := 30600 - 12 * v 2
  let values := (Finset.range 15).image fun k =>
    let I := maskSlots 4 (k + 1)
    oldPlaneNumer (originalPick raw I) (∑ i ∈ I, v i.castSucc)
  (insert seed values).max' ⟨seed, Finset.mem_insert_self _ _⟩

def selectedNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  ∑ i ∈ maskSlots 5 raw.mask.toNat, v i

def capNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  min (25600 + 16 * selectedNumer raw v) (45600 - 48 * selectedNumer raw v)

def gapNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  capNumer raw v - max (oldNumer raw v) (32 * ((∑ i : Fin 5, v i) + 2 * v 4))

def originalD (raw : FifthWireRow) (c : ChildIndex) : ℤ :=
  (producerBits.map (fun w => gapNumer raw (vertexNumer raw c w))).sum

structure RatioPair where
  num : ℤ
  den : ℤ
  deriving DecidableEq

def planeRatioPair (raw : FifthWireRow) (c : ChildIndex) (side : Bool) (w : Word) : RatioPair :=
  let v := vertexNumer raw c w
  let ss := selectedNumer raw v
  let plane := if side then 45600 - 48 * ss else 25600 + 16 * ss
  ⟨plane - 32 * ∑ i : Fin 5, v i, 32 * v 4⟩

/-- Strict original update retains the earlier unreduced pair at a tie. -/
def updatePair (old next : RatioPair) : RatioPair :=
  if old.num * next.den < next.num * old.den then next else old

def originalPlaneMax (raw : FifthWireRow) (c : ChildIndex) (side : Bool) : RatioPair :=
  let first := planeRatioPair raw c side (false, false, false, false, false)
  producerBits.tail.foldl (fun old w => updatePair old (planeRatioPair raw c side w)) first

/-- Source geometry finally takes the smaller of the TWO vertex maxima;
its strict comparison retains the A pair at a tie. -/
def originalAB (raw : FifthWireRow) (c : ChildIndex) : RatioPair :=
  let a := originalPlaneMax raw c false
  let cc := originalPlaneMax raw c true
  if cc.num * a.den < a.num * cc.den then cc else a

structure OriginalChildFields where
  n : ℤ
  lo : Fin 5 → ℤ
  hi : Fin 5 → ℤ
  mask : ℤ
  d : ℤ
  A : ℤ
  B : ℤ

def originalFields (raw : FifthWireRow) (c : ChildIndex) : OriginalChildFields :=
  let ab := originalAB raw c
  ⟨1600, wireLo raw c, wireHi raw c, raw.mask, originalD raw c, ab.num, ab.den⟩

/-- The original expanded exact_floor expression with log_terms=4.
Python // with the proved positive denominator is represented by Int /.
The d<=0 source fallback is exactly preserved. -/
def originalExactFloor (row : OriginalChildFields) : ℤ :=
  if row.d ≤ 0 then 0 else
  let H := 1024 * row.hi 4
  let C := H * row.A - row.d * row.B
  let z := row.d * row.B
  let den := 2 * H * (row.A - row.B) - z
  let rn := 2 * z * (15 * den ^ 4 + 5 * z ^ 2 * den ^ 2 + 3 * z ^ 4)
  let rd := 15 * den ^ 5
  let y := C - 2 * H * row.B
  let cc := C ^ 2
  let yy := y ^ 2
  let ln := 2 * y * (315 * cc ^ 4 - 210 * yy * cc ^ 3 -
    42 * yy ^ 2 * cc ^ 2 - 18 * yy ^ 3 * cc - 10 * yy ^ 4)
  let ld := 315 * C ^ 7 * (cc - yy)
  let dn := row.B * (C * rn * ld - row.d * row.B * ln * rd)
  let dd := C * row.A * rd * ld
  let numerator := 4 * row.n * (∏ i : Fin 5, wireWidth i) * dn
  let denominator := (∏ i : Fin 5, row.hi i) * row.hi 4 * dd
  numerator * (2 : ℤ) ^ 80 / denominator

end ImbalancedChen.P5OriginalChildIntegerWireBinding
