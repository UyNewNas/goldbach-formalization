import Lean
import ImbalancedChen.P2OriginalSaving19Archive
import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.P5OldFifthFirstFConcavity
import ImbalancedChen.CurrentUpperEighteenBudget

/-! The original two-chart, 8 × 8 × 32 per-chart G6 witness.
The data loader embeds the original text. The total parser and the
4096 rational checks interpret the original fields in Lean. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackArchive
open Lean Elab Term
open scoped BigOperators
open P2OriginalSaving19Archive (SourceJson parseInteger jsonRational)

elab "originalThirdFallbackText%" : term => do
  let source := System.FilePath.mk (← getFileName)
  let raw ← liftIO <| IO.FS.readFile (source.withFileName "G6_ORIGINAL_WITNESS.json")
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

def originalText : String := originalThirdFallbackText%

abbrev Cell := Bool × Fin 8 × Fin 8 × Fin 32
def branch (b : Bool) : ℤ := if b then 1 else -3
def pos (c : Cell) : ℕ :=
  (((if c.1 then 8 else 0) + c.2.1.val)*8 + c.2.2.1.val)*32 + c.2.2.2.val

structure Record where
  k : ℤ
  i : ℕ
  j : ℕ
  l : ℕ
  t : ℚ
  floor : ℤ
  deriving Inhabited, DecidableEq

def decodeRecord (x : SourceJson) : Except String Record := do
  let .arr [.number k,i,j,l,t,f] := x | throw "expected six original G6 fields"
  return ⟨← parseInteger k, ← SourceJson.Decode.read i, ← SourceJson.Decode.read j,
    ← SourceJson.Decode.read l, ← jsonRational t, ← parseInteger (← f.getStr?)⟩

def decode (x : SourceJson) : Except String (Array Record) := do
  let shape ← x.getObjValAs? (Array Nat) "grid"
  let b ← x.getObjValAs? Nat "rounding_bits"
  let terms ← x.getObjValAs? Nat "log_terms"
  let w ← x.getObjValAs? String "w_min"
  let cols ← x.getObjValAs? (Array String) "columns"
  unless shape == #[8,8,32] && b == 96 && terms == 16 && w == "5/9" &&
    cols == #["chart_k","u_index","v_index","w_index","new_argument_upper","floor_Q"] do
    throw "original G6 grid or fields differ"
  (← (← x.getObjVal? "rows").getArr?).mapM decodeRecord

def parsed := SourceJson.parse originalText >>= decode
def records : Array Record := parsed.toOption.getD #[]
def record (c : Cell) := records.getD (pos c) default

def h : ℚ := 1/384
def mu : ℚ := 25/128
def peak : ℚ := 153/256
def ua (c : Cell) : ℚ := (c.2.1.val : ℚ)/8
def ub (c : Cell) : ℚ := ((c.2.1.val : ℚ)+1)/8
def va (c : Cell) : ℚ := (c.2.2.1.val : ℚ)/8
def vb (c : Cell) : ℚ := ((c.2.2.1.val : ℚ)+1)/8
def wa (c : Cell) : ℚ := 5/9 + (4/9)*(c.2.2.2.val : ℚ)/32
def wb (c : Cell) : ℚ := 5/9 + (4/9)*((c.2.2.2.val : ℚ)+1)/32
def xQ (u : ℚ) : ℚ := mu+h*u
def sQ (b : Bool) (u v : ℚ) : ℚ := mu+(branch b : ℚ)*h*u*v
def oldQ (u : ℚ) : ℚ := peak-(3/2)*h*u
def newQ (u v : ℚ) : ℚ := peak-(3/2)*h*u*v
def edge (a b : ℚ) (i : Bool) := if i then b else a
def upperRatio (c : Cell) (i j : Bool) : ℚ :=
  let u := edge (ua c) (ub c) i
  let v := edge (va c) (vb c) j
  2*(newQ u v-xQ u-sQ c.1 u v)/(sQ c.1 u v*wa c)
def cornerMax (f : Bool → Bool → ℚ) : ℚ :=
  max (max (f false false) (f false true)) (max (f true false) (f true true))
def sMax (c : Cell) : ℚ := cornerMax (fun i j => sQ c.1 (edge (ua c) (ub c) i) (edge (va c) (vb c) j))
def den (c : Cell) : ℚ := xQ (ub c)*(sMax c)^3*(1-wb c/2)*(wb c)^3
def mass (c : Cell) : ℚ :=
  ((ub c)^3-(ua c)^3)/3 * ((vb c-va c)-((vb c)^2-(va c)^2)/2) * (wb c-wa c)
def logUp (q : ℚ) : ℚ :=
  let z := (q-1)/(q+1)
  2*(∑ i ∈ Finset.range 16, z^(2*i+1)/((2*i+1 : ℕ) : ℚ)) + 2*z^33/(33*(1-z^2))
def slope (c : Cell) : ℚ :=
  let t := (record c).t
  (t/(t-1)-logUp (t-1))/t^2
def rationalContribution (c : Cell) : ℚ :=
  24*|(branch c.1 : ℚ)|*h^3*mass c*slope c/den c

def Checked (c : Cell) : Prop :=
  let r := record c
  r.k = branch c.1 ∧ r.i = c.2.1.val ∧ r.j = c.2.2.1.val ∧ r.l = c.2.2.2.val ∧
  r.t = cornerMax (upperRatio c) ∧ 2 ≤ r.t ∧ r.t ≤ 4 ∧
  0 < den c ∧ 0 < mass c ∧ 0 < slope c ∧
  0 ≤ r.floor ∧ r.floor = ⌊(2:ℚ)^96*rationalContribution c⌋ ∧
  ∀ i j : Bool,
    let u := edge (ua c) (ub c) i
    let v := edge (va c) (vb c) j
    0 < sQ c.1 u v ∧ sQ c.1 u v ≤ sMax c ∧
      2*(oldQ u-xQ u-sQ c.1 u v) ≥ 2*sQ c.1 u v*wb c ∧
      2*(newQ u v-xQ u-sQ c.1 u v) ≤ r.t*sQ c.1 u v*wa c

instance (c : Cell) : Decidable (Checked c) := by unfold Checked; infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem original_parse_success : parsed.toOption.isSome = true ∧ records.size = 4096 := by decide

def Slice (b : Bool) (i : Fin 8) : Prop := ∀ j : Fin 8, ∀ l : Fin 32, Checked (b,i,j,l)
instance (b : Bool) (i : Fin 8) : Decidable (Slice b i) := by unfold Slice; infer_instance
theorem sliceLeft0 : Slice false 0 := by decide
theorem sliceLeft1 : Slice false 1 := by decide
theorem sliceLeft2 : Slice false 2 := by decide
theorem sliceLeft3 : Slice false 3 := by decide
theorem sliceLeft4 : Slice false 4 := by decide
theorem sliceLeft5 : Slice false 5 := by decide
theorem sliceLeft6 : Slice false 6 := by decide
theorem sliceLeft7 : Slice false 7 := by decide
theorem sliceRight0 : Slice true 0 := by decide
theorem sliceRight1 : Slice true 1 := by decide
theorem sliceRight2 : Slice true 2 := by decide
theorem sliceRight3 : Slice true 3 := by decide
theorem sliceRight4 : Slice true 4 := by decide
theorem sliceRight5 : Slice true 5 := by decide
theorem sliceRight6 : Slice true 6 := by decide
theorem sliceRight7 : Slice true 7 := by decide

theorem original_rows (c : Cell) : Checked c := by
  rcases c with ⟨b,i,j,l⟩
  cases b <;> fin_cases i
  · exact sliceLeft0 j l
  · exact sliceLeft1 j l
  · exact sliceLeft2 j l
  · exact sliceLeft3 j l
  · exact sliceLeft4 j l
  · exact sliceLeft5 j l
  · exact sliceLeft6 j l
  · exact sliceLeft7 j l
  · exact sliceRight0 j l
  · exact sliceRight1 j l
  · exact sliceRight2 j l
  · exact sliceRight3 j l
  · exact sliceRight4 j l
  · exact sliceRight5 j l
  · exact sliceRight6 j l
  · exact sliceRight7 j l

theorem chart_floors (b : Bool) :
    (∑ i : Fin 8, ∑ j : Fin 8, ∑ l : Fin 32, (record (b,i,j,l)).floor) =
      if b then (823252131740202516613350 : ℤ) else 2273760546844112511182079 := by
  cases b <;> decide

theorem original_Q96 :
    (∑ c : Cell, (record c).floor) = (3097012678584315027795429 : ℤ) := by
  simp only [Fintype.sum_prod_type]
  simp only [chart_floors]
  decide

theorem row_floor_le_contribution (c : Cell) : ((record c).floor : ℝ)/2^96 ≤ (rationalContribution c : ℝ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hfloor,_⟩ := original_rows c
  have h := Int.floor_le ((2 : ℚ)^96 * rationalContribution c)
  rw [← hfloor] at h
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^96)).mpr
  exact_mod_cast (by simpa only [mul_comm] using h :
    ((record c).floor : ℚ) ≤ rationalContribution c * 2^96)

theorem original_slot_le_contributions :
    currentUpperEighteenGains 5 ≤ ∑ c : Cell, (rationalContribution c : ℝ) := by
  have hs : (∑ c : Cell, ((record c).floor : ℝ)) = 3097012678584315027795429 := by
    exact_mod_cast original_Q96
  calc
    currentUpperEighteenGains 5 = 3097012678584315027795429 / (2 : ℝ)^96 := by
      norm_num [currentUpperEighteenGains]
    _ = ∑ c : Cell, ((record c).floor : ℝ)/2^96 := by rw [← Finset.sum_div,hs]
    _ ≤ _ := Finset.sum_le_sum fun c _ => row_floor_le_contribution c

end ImbalancedChen.P4AOriginalThirdFallbackArchive
