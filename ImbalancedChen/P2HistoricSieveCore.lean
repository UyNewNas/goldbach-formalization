import ImbalancedChen.P2HistoricI80Core
import Mathlib.Data.Rat.Defs

/-! Literal executable historical Q80 state and source sf interpreter.
Declarations below are moved byte-for-byte from SieveTableSemantics, with
the original namespace, types, bodies and defaults. Analytic interpretation
remains in the legacy module. This core imports no external project. -/
namespace ImbalancedChen.P2HistoricSieveTableSemantics

noncomputable section
open Certificates.P2HistoricQ80DefectLookup

def scale : ℤ := 2 ^ 80
def ceilDiv (x d : ℤ) : ℤ := -((-x) / d)
structure HistoricNode where
  ll : ℤ
  lh : ℤ
  hl : ℤ
  hh : ℤ
  deriving DecidableEq, Repr

def initial : HistoricNode := ⟨0, 0, scale, scale⟩

def errL (g : ℕ) : ℤ := ceilDiv scale (6 * (g : ℤ) ^ 3)
def errH (g : ℕ) : ℤ := ceilDiv scale (12 * (g : ℤ) ^ 3)
def interpError (g : ℕ) : ℤ := ceilDiv scale (8 * (g : ℤ) ^ 2)

/-- The TWO nested floors, not one floor of the rational trapezoid. -/
def trapLo (g j : ℕ) (x y : ℤ) : ℤ :=
  (x * (g : ℤ) / ((j : ℤ) - 1) + y * (g : ℤ) / (j : ℤ)) / (2 * (g : ℤ))

/-- The TWO inner ceilings and the outer ceiling are all retained. -/
def trapHi (g j : ℕ) (x y : ℤ) : ℤ :=
  ceilDiv (ceilDiv (x * (g : ℤ)) ((j : ℤ) - 1) +
    ceilDiv (y * (g : ℤ)) (j : ℤ)) (2 * (g : ℤ))

def update (g i : ℕ) (old : ℕ → HistoricNode) : HistoricNode :=
  if i ≤ 2 * g then initial else
  let j := i - g
  let p := old (i - 1)
  let llo := trapLo g j (old (j - 1)).hl (old j).hl
  let lhi := trapHi g j (old (j - 1)).hh (old j).hh
  { ll := max p.ll (p.ll + llo - errL g)
    lh := p.lh + lhi
    hl := if i ≤ 3 * g then scale else
      p.hl + trapLo g j (old (j - 1)).ll (old j).ll
    hh := if i ≤ 3 * g then scale else
      p.hh + trapHi g j (old (j - 1)).lh (old j).lh + errH g }

def state (g : ℕ) : ℕ → (ℕ → HistoricNode) :=
  Nat.rec (motive := fun _ => ℕ → HistoricNode) (fun _ => initial)
    (fun k old i => if i = k + 1 then update g (k + 1) old else old i)

def table (g maximum : ℕ) : ℕ → HistoricNode := state g (maximum * g)

def queryIndex (g : ℕ) (a b : ℤ) : ℕ := ((a * (g : ℤ)) / b).toNat
def queryResidual (g : ℕ) (a b : ℤ) : ℤ := (a * (g : ℤ)) % b

def numerator (g : ℕ) (a b : ℤ) (lo hi : ℕ → ℤ) (convex : Bool := false) : I80 :=
  let q := queryIndex g a b
  let r := queryResidual g a b
  if r = 0 then ⟨lo q, hi q⟩ else
  let l := (lo q * (b - r) + lo (q + 1) * r) / b
  let h := ceilDiv (hi q * (b - r) + hi (q + 1) * r) b
  if convex then ⟨l - interpError g, h⟩ else ⟨l, h + interpError g⟩

/-- Exact source point interpreter, including the >maximum monotone tail. -/
def point (g maximum : ℕ) (a b : ℤ) : I80 :=
  if a ≤ 2 * b then ⟨0, 0⟩ else
  if a > (maximum : ℤ) * b then
    ⟨(table g maximum (maximum * g)).ll / (maximum : ℤ),
      ceilDiv (table g maximum (maximum * g)).hh (maximum : ℤ)⟩ else
  let p := numerator g a b (fun i => (table g maximum i).ll)
    (fun i => (table g maximum i).lh)
  ⟨p.lo * b / a, ceilDiv (p.hi * b) a⟩

/-- This is Ordinary.f's raw I80 result; paired-v2 supplies maximum=8. -/
def sf (g maximum : ℕ) (q : ℚ) : I80 := point g maximum q.num (q.den : ℤ)

end

end ImbalancedChen.P2HistoricSieveTableSemantics
