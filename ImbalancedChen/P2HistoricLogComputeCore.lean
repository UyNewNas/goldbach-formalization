import ImbalancedChen.P2HistoricQ80DefectLookup
import ImbalancedChen.P2HistoricLogRangeReduction

/-! Original exact executable Q80 logarithm backend, separated from its
analytic proof facade. Every numeric formula is preserved. oddLoop uses
the same Nat recursion through the native-supported primitive recursor. -/
namespace ImbalancedChen.Certificates.P2HistoricLogPointInterpreter

noncomputable section
open P2HistoricQ80DefectLookup
open P2DirectedLogRounding

def ceilDiv (n d : ℤ) : ℤ := -((-n) / d)
def positiveMul (x y : I80) : I80 :=
  ⟨x.lo*y.lo/(Q : ℤ), ceilDiv (x.hi*y.hi) (Q : ℤ)⟩

def divNat (x : I80) (n : ℕ) : I80 := ⟨x.lo/(n : ℤ), ceilDiv x.hi (n : ℤ)⟩

structure OddState where
  power : I80
  total : I80

def oddSquare (ul uh : ℤ) : I80 :=
  ⟨ul*ul/(Q : ℤ), ceilDiv (uh*uh) (Q : ℤ)⟩

def oddStart (ul uh : ℤ) : OddState := ⟨⟨ul,uh⟩, I80.raw 0⟩

def oddStep (square : I80) (j : ℕ) (s : OddState) : OddState :=
  ⟨positiveMul s.power square, s.total.add (divNat s.power (2*j+1))⟩

def oddLoop (square : I80) (ul uh : ℤ) : ℕ → OddState :=
  Nat.rec (motive := fun _ => OddState) (oddStart ul uh)
    (fun n s => oddStep square n s)

theorem oddLoop_zero_eq (square : I80) (ul uh : ℤ) :
    oddLoop square ul uh 0 = oddStart ul uh := rfl

theorem oddLoop_succ_eq (square : I80) (ul uh : ℤ) (n : ℕ) :
    oddLoop square ul uh (n + 1) = oddStep square n (oddLoop square ul uh n) := rfl

def atanhBounds (ul uh : ℤ) : I80 :=
  let square := oddSquare ul uh
  let state := oddLoop square ul uh 32
  let tail := ceilDiv (2*state.power.hi*(Q : ℤ)) (65*((Q : ℤ)-square.hi))
  ⟨2*state.total.lo, 2*state.total.hi+tail⟩

def logTwoBounds : I80 := atanhBounds ((Q : ℤ)/3) (ceilDiv (Q : ℤ) 3)

def reducedParameter (rl rh : ℤ) : I80 :=
  ⟨(rl-(Q : ℤ))*(Q : ℤ)/(rh+(Q : ℤ)),
    ceilDiv ((rh-(Q : ℤ))*(Q : ℤ)) (rl+(Q : ℤ))⟩

def reducedLogBounds (rl rh : ℤ) : I80 :=
  let p := reducedParameter rl rh
  atanhBounds p.lo p.hi

def integerScale (x : I80) (k : ℤ) : I80 :=
  if 0 ≤ k then ⟨k*x.lo,k*x.hi⟩ else ⟨k*x.hi,k*x.lo⟩

def logPointFromReduction (k rl rh : ℤ) : I80 :=
  (reducedLogBounds rl rh).add (integerScale logTwoBounds k)

def logPoint (q : ℤ) : I80 :=
  if q = (Q : ℤ) then I80.raw 0 else
    logPointFromReduction
      (P2HistoricLogRangeReduction.sourceShift q)
      (P2HistoricLogRangeReduction.sourceRL q)
      (P2HistoricLogRangeReduction.sourceRH q)

def logI (q : ℚ) : I80 :=
  let x := I80.point q
  ⟨(logPoint x.lo).lo,(logPoint x.hi).hi⟩

end

end ImbalancedChen.Certificates.P2HistoricLogPointInterpreter
