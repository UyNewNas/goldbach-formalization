import ImbalancedChen.Part5OriginalH430W2UpperQuadrature
import ImbalancedChen.Part5OriginalH430W2ArchivedSingletons

namespace ImbalancedChen.Part5OriginalH430W2UpperPolygons

open Set MeasureTheory
open scoped Interval
open Part5OriginalH430W2UpperKernel Part5OriginalH430W2UpperQuadrature
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def parameterQ : Fin 36 → Fin 5 → ℚ :=
  ![![11/5, 227/50, 353/100, 29/10, 61/25],
    ![11/5, 24/5, 353/100, 29/10, 47/20],
    ![21/10, 24/5, 353/100, 29/10, 117/50],
    ![101/50, 9707/2000, 89/25, 14663/5000, 11667/5000],
    ![51/25, 46871/10000, 18297/5000, 28913/10000, 11909/5000],
    ![103/50, 24/5, 7119/2000, 2931/1000, 4679/2000],
    ![52/25, 1863/400, 181/50, 7253/2500, 23819/10000],
    ![21/10, 46399/10000, 18099/5000, 1451/500, 23813/10000],
    ![21/10, 47873/10000, 89/25, 14623/5000, 23379/10000],
    ![53/25, 46681/10000, 35999/10000, 29037/10000, 2977/1250],
    ![107/50, 119/25, 17897/5000, 1822/625, 23317/10000],
    ![54/25, 46397/10000, 179/50, 29109/10000, 2977/1250],
    ![11/5, 23199/5000, 89/25, 14597/5000, 4763/2000],
    ![11/5, 47323/10000, 17799/5000, 7297/2500, 4659/2000],
    ![56/25, 45799/10000, 89/25, 1457/500, 2977/1250],
    ![56/25, 2911/625, 17899/5000, 233/80, 5843/2500],
    ![57/25, 45393/10000, 179/50, 3641/1250, 2977/1250],
    ![23/10, 5599/1250, 179/50, 729/250, 11907/5000],
    ![58/25, 5573/1250, 18/5, 29101/10000, 2977/1250],
    ![58/25, 45569/10000, 18099/5000, 29057/10000, 11619/5000],
    ![59/25, 2209/500, 18/5, 2907/1000, 2977/1250],
    ![12/5, 42999/10000, 18/5, 29131/10000, 24077/10000],
    ![61/25, 20797/5000, 181/50, 29193/10000, 3053/1250],
    ![61/25, 8319/2000, 18/5, 7289/2500, 24471/10000],
    ![62/25, 4079/1000, 179/50, 29231/10000, 12433/5000],
    ![5/2, 203/50, 7119/2000, 5837/2000, 25063/10000],
    ![63/25, 40587/10000, 177/50, 2921/1000, 1263/500],
    ![64/25, 191/50, 17699/5000, 5873/2000, 25619/10000],
    ![64/25, 20297/5000, 34999/10000, 14601/5000, 12827/5000],
    ![13/5, 81/20, 17293/5000, 5843/2000, 1628/625],
    ![66/25, 40501/10000, 33999/10000, 29213/10000, 13221/5000],
    ![67/25, 179/50, 86/25, 29529/10000, 13407/5000],
    ![67/25, 10127/2500, 84/25, 14649/5000, 26837/10000],
    ![68/25, 81/20, 33/10, 29343/10000, 1702/625],
    ![69/25, 81/20, 163/50, 29343/10000, 13813/5000],
    ![14/5, 81/20, 161/50, 5883/2000, 28021/10000]]

abbrev Parameters := Fin 5 → ℚ

noncomputable def physical (p : Parameters) : W2Parameters :=
  ⟨(p 0 : ℝ),(p 1 : ℝ),(p 2 : ℝ),(p 3 : ℝ),(p 4 : ℝ)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem original_parameters (j : Fin 36) : physical (parameterQ j) = originalW2At j := by
  fin_cases j
  · change (⟨((11/5 : ℚ) : ℝ),((227/50 : ℚ) : ℝ),((353/100 : ℚ) : ℝ),((29/10 : ℚ) : ℝ),((61/25 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨11/5,227/50,353/100,29/10,61/25⟩
    norm_num
  · change (⟨((11/5 : ℚ) : ℝ),((24/5 : ℚ) : ℝ),((353/100 : ℚ) : ℝ),((29/10 : ℚ) : ℝ),((47/20 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨11/5,24/5,353/100,29/10,47/20⟩
    norm_num
  · change (⟨((21/10 : ℚ) : ℝ),((24/5 : ℚ) : ℝ),((353/100 : ℚ) : ℝ),((29/10 : ℚ) : ℝ),((117/50 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨21/10,24/5,353/100,29/10,117/50⟩
    norm_num
  · change (⟨((101/50 : ℚ) : ℝ),((9707/2000 : ℚ) : ℝ),((89/25 : ℚ) : ℝ),((14663/5000 : ℚ) : ℝ),((11667/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨101/50,9707/2000,89/25,14663/5000,11667/5000⟩
    norm_num
  · change (⟨((51/25 : ℚ) : ℝ),((46871/10000 : ℚ) : ℝ),((18297/5000 : ℚ) : ℝ),((28913/10000 : ℚ) : ℝ),((11909/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨51/25,46871/10000,18297/5000,28913/10000,11909/5000⟩
    norm_num
  · change (⟨((103/50 : ℚ) : ℝ),((24/5 : ℚ) : ℝ),((7119/2000 : ℚ) : ℝ),((2931/1000 : ℚ) : ℝ),((4679/2000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨103/50,24/5,7119/2000,2931/1000,4679/2000⟩
    norm_num
  · change (⟨((52/25 : ℚ) : ℝ),((1863/400 : ℚ) : ℝ),((181/50 : ℚ) : ℝ),((7253/2500 : ℚ) : ℝ),((23819/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨52/25,1863/400,181/50,7253/2500,23819/10000⟩
    norm_num
  · change (⟨((21/10 : ℚ) : ℝ),((46399/10000 : ℚ) : ℝ),((18099/5000 : ℚ) : ℝ),((1451/500 : ℚ) : ℝ),((23813/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨21/10,46399/10000,18099/5000,1451/500,23813/10000⟩
    norm_num
  · change (⟨((21/10 : ℚ) : ℝ),((47873/10000 : ℚ) : ℝ),((89/25 : ℚ) : ℝ),((14623/5000 : ℚ) : ℝ),((23379/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨21/10,47873/10000,89/25,14623/5000,23379/10000⟩
    norm_num
  · change (⟨((53/25 : ℚ) : ℝ),((46681/10000 : ℚ) : ℝ),((35999/10000 : ℚ) : ℝ),((29037/10000 : ℚ) : ℝ),((2977/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨53/25,46681/10000,35999/10000,29037/10000,2977/1250⟩
    norm_num
  · change (⟨((107/50 : ℚ) : ℝ),((119/25 : ℚ) : ℝ),((17897/5000 : ℚ) : ℝ),((1822/625 : ℚ) : ℝ),((23317/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨107/50,119/25,17897/5000,1822/625,23317/10000⟩
    norm_num
  · change (⟨((54/25 : ℚ) : ℝ),((46397/10000 : ℚ) : ℝ),((179/50 : ℚ) : ℝ),((29109/10000 : ℚ) : ℝ),((2977/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨54/25,46397/10000,179/50,29109/10000,2977/1250⟩
    norm_num
  · change (⟨((11/5 : ℚ) : ℝ),((23199/5000 : ℚ) : ℝ),((89/25 : ℚ) : ℝ),((14597/5000 : ℚ) : ℝ),((4763/2000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨11/5,23199/5000,89/25,14597/5000,4763/2000⟩
    norm_num
  · change (⟨((11/5 : ℚ) : ℝ),((47323/10000 : ℚ) : ℝ),((17799/5000 : ℚ) : ℝ),((7297/2500 : ℚ) : ℝ),((4659/2000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨11/5,47323/10000,17799/5000,7297/2500,4659/2000⟩
    norm_num
  · change (⟨((56/25 : ℚ) : ℝ),((45799/10000 : ℚ) : ℝ),((89/25 : ℚ) : ℝ),((1457/500 : ℚ) : ℝ),((2977/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨56/25,45799/10000,89/25,1457/500,2977/1250⟩
    norm_num
  · change (⟨((56/25 : ℚ) : ℝ),((2911/625 : ℚ) : ℝ),((17899/5000 : ℚ) : ℝ),((233/80 : ℚ) : ℝ),((5843/2500 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨56/25,2911/625,17899/5000,233/80,5843/2500⟩
    norm_num
  · change (⟨((57/25 : ℚ) : ℝ),((45393/10000 : ℚ) : ℝ),((179/50 : ℚ) : ℝ),((3641/1250 : ℚ) : ℝ),((2977/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨57/25,45393/10000,179/50,3641/1250,2977/1250⟩
    norm_num
  · change (⟨((23/10 : ℚ) : ℝ),((5599/1250 : ℚ) : ℝ),((179/50 : ℚ) : ℝ),((729/250 : ℚ) : ℝ),((11907/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨23/10,5599/1250,179/50,729/250,11907/5000⟩
    norm_num
  · change (⟨((58/25 : ℚ) : ℝ),((5573/1250 : ℚ) : ℝ),((18/5 : ℚ) : ℝ),((29101/10000 : ℚ) : ℝ),((2977/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨58/25,5573/1250,18/5,29101/10000,2977/1250⟩
    norm_num
  · change (⟨((58/25 : ℚ) : ℝ),((45569/10000 : ℚ) : ℝ),((18099/5000 : ℚ) : ℝ),((29057/10000 : ℚ) : ℝ),((11619/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨58/25,45569/10000,18099/5000,29057/10000,11619/5000⟩
    norm_num
  · change (⟨((59/25 : ℚ) : ℝ),((2209/500 : ℚ) : ℝ),((18/5 : ℚ) : ℝ),((2907/1000 : ℚ) : ℝ),((2977/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨59/25,2209/500,18/5,2907/1000,2977/1250⟩
    norm_num
  · change (⟨((12/5 : ℚ) : ℝ),((42999/10000 : ℚ) : ℝ),((18/5 : ℚ) : ℝ),((29131/10000 : ℚ) : ℝ),((24077/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨12/5,42999/10000,18/5,29131/10000,24077/10000⟩
    norm_num
  · change (⟨((61/25 : ℚ) : ℝ),((20797/5000 : ℚ) : ℝ),((181/50 : ℚ) : ℝ),((29193/10000 : ℚ) : ℝ),((3053/1250 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨61/25,20797/5000,181/50,29193/10000,3053/1250⟩
    norm_num
  · change (⟨((61/25 : ℚ) : ℝ),((8319/2000 : ℚ) : ℝ),((18/5 : ℚ) : ℝ),((7289/2500 : ℚ) : ℝ),((24471/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨61/25,8319/2000,18/5,7289/2500,24471/10000⟩
    norm_num
  · change (⟨((62/25 : ℚ) : ℝ),((4079/1000 : ℚ) : ℝ),((179/50 : ℚ) : ℝ),((29231/10000 : ℚ) : ℝ),((12433/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨62/25,4079/1000,179/50,29231/10000,12433/5000⟩
    norm_num
  · change (⟨((5/2 : ℚ) : ℝ),((203/50 : ℚ) : ℝ),((7119/2000 : ℚ) : ℝ),((5837/2000 : ℚ) : ℝ),((25063/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨5/2,203/50,7119/2000,5837/2000,25063/10000⟩
    norm_num
  · change (⟨((63/25 : ℚ) : ℝ),((40587/10000 : ℚ) : ℝ),((177/50 : ℚ) : ℝ),((2921/1000 : ℚ) : ℝ),((1263/500 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨63/25,40587/10000,177/50,2921/1000,1263/500⟩
    norm_num
  · change (⟨((64/25 : ℚ) : ℝ),((191/50 : ℚ) : ℝ),((17699/5000 : ℚ) : ℝ),((5873/2000 : ℚ) : ℝ),((25619/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨64/25,191/50,17699/5000,5873/2000,25619/10000⟩
    norm_num
  · change (⟨((64/25 : ℚ) : ℝ),((20297/5000 : ℚ) : ℝ),((34999/10000 : ℚ) : ℝ),((14601/5000 : ℚ) : ℝ),((12827/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨64/25,20297/5000,34999/10000,14601/5000,12827/5000⟩
    norm_num
  · change (⟨((13/5 : ℚ) : ℝ),((81/20 : ℚ) : ℝ),((17293/5000 : ℚ) : ℝ),((5843/2000 : ℚ) : ℝ),((1628/625 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨13/5,81/20,17293/5000,5843/2000,1628/625⟩
    norm_num
  · change (⟨((66/25 : ℚ) : ℝ),((40501/10000 : ℚ) : ℝ),((33999/10000 : ℚ) : ℝ),((29213/10000 : ℚ) : ℝ),((13221/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨66/25,40501/10000,33999/10000,29213/10000,13221/5000⟩
    norm_num
  · change (⟨((67/25 : ℚ) : ℝ),((179/50 : ℚ) : ℝ),((86/25 : ℚ) : ℝ),((29529/10000 : ℚ) : ℝ),((13407/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨67/25,179/50,86/25,29529/10000,13407/5000⟩
    norm_num
  · change (⟨((67/25 : ℚ) : ℝ),((10127/2500 : ℚ) : ℝ),((84/25 : ℚ) : ℝ),((14649/5000 : ℚ) : ℝ),((26837/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨67/25,10127/2500,84/25,14649/5000,26837/10000⟩
    norm_num
  · change (⟨((68/25 : ℚ) : ℝ),((81/20 : ℚ) : ℝ),((33/10 : ℚ) : ℝ),((29343/10000 : ℚ) : ℝ),((1702/625 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨68/25,81/20,33/10,29343/10000,1702/625⟩
    norm_num
  · change (⟨((69/25 : ℚ) : ℝ),((81/20 : ℚ) : ℝ),((163/50 : ℚ) : ℝ),((29343/10000 : ℚ) : ℝ),((13813/5000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨69/25,81/20,163/50,29343/10000,13813/5000⟩
    norm_num
  · change (⟨((14/5 : ℚ) : ℝ),((81/20 : ℚ) : ℝ),((161/50 : ℚ) : ℝ),((5883/2000 : ℚ) : ℝ),((28021/10000 : ℚ) : ℝ)⟩ : W2Parameters) =
        ⟨14/5,81/20,161/50,5883/2000,28021/10000⟩
    norm_num

def grid (i : ℕ) : ℚ := 1+(i : ℚ)/50
def z : Line := ⟨0,0⟩
def idLine : Line := ⟨0,1⟩
def constant (q : ℚ) : Line := ⟨q,0⟩
def roof : Line := ⟨1,-1⟩
def good5 : Line := ⟨1,-2⟩
def lowX (p : Parameters) := 1/p 1
def highX (p : Parameters) (k : Fin 4) : ℚ := if k=0 then 1/3 else 1/p 2
def bot (p : Parameters) : Fin 4 → Line :=
  ![idLine,constant (1/p 3),idLine,constant (1/p 2)]
def top (p : Parameters) : Fin 4 → Line :=
  ![constant (1/p 3),constant (1/p 4),constant (1/p 2),constant (1/p 3)]
def extra (p : Parameters) (k : Fin 4) : Line := if k=0 then good5 else top p k
def cellLow (p : Parameters) (k : Fin 4) (i : ℕ) : Line :=
  if k.val<2 then ⟨1-grid (i+1)/p 1,-1⟩ else ⟨1,-(1+grid (i+1))⟩
def cellHigh (p : Parameters) (k : Fin 4) (i : ℕ) : Line :=
  if k.val<2 then ⟨1-grid i/p 1,-1⟩ else ⟨1,-(1+grid i)⟩

/-- All original affine candidates, with the old D5 good region split at its original corner. -/
def parts (p : Parameters) (k : Fin 4) : List Strip :=
  let a := lowX p
  let h := highX p k
  let c := (1-1/p 3)/2
  if k=0 then [⟨a,c,idLine,top p k⟩,⟨c,h,idLine,good5⟩]
  else [⟨a,h,bot p k,top p k⟩]

def cross (base : Strip) (a b : Line) : List ℚ :=
  let x := (b.c-a.c)/(a.m-b.m)
  if a.m≠b.m ∧ base.l<x ∧ x<base.r then [x] else []

def clipped (base : Strip) (low high : Line) : List Strip :=
  let lines := [base.low,low,base.high,high]
  let allCuts := [base.l,base.r] ++ lines.flatMap (fun a => lines.flatMap (cross base a))
  let xs := allCuts.eraseDups.mergeSort (fun a b => decide (a≤b))
  (xs.zip xs.tail).filterMap fun lr =>
    let m := (lr.1+lr.2)/2
    let a := if low.atQ m ≤ base.low.atQ m then base.low else low
    let b := if base.high.atQ m ≤ high.atQ m then base.high else high
    if a.atQ m < b.atQ m then some ⟨lr.1,lr.2,a,b⟩ else none

def pieces (p : Parameters) (k : Fin 4) (i : ℕ) : List Strip :=
  if grid i < 3 then (parts p k).flatMap (fun w => clipped w (cellLow p k i) (cellHigh p k i))
  else []

def OrderAtEnds (s : Strip) (a b : Line) : Prop :=
  a.atQ s.l ≤ b.atQ s.l ∧ a.atQ s.r ≤ b.atQ s.r
def StrictAtEnds (s : Strip) (a b : Line) : Prop :=
  a.atQ s.l < b.atQ s.l ∧ a.atQ s.r < b.atQ s.r

/-- Certificates use only rational endpoint inequalities and preserve every original wall. -/
def Fit (p : Parameters) (k : Fin 4) (i : ℕ) (s : Strip) : Prop :=
  s.l<s.r ∧ 0<s.l ∧ lowX p≤s.l ∧ s.r≤highX p k ∧ StrictAtEnds s z s.low ∧
  OrderAtEnds s s.low s.high ∧ StrictAtEnds s s.high roof ∧
  OrderAtEnds s (bot p k) s.low ∧ OrderAtEnds s s.high (top p k) ∧
  OrderAtEnds s s.high (extra p k) ∧
  OrderAtEnds s (cellLow p k i) s.low ∧ OrderAtEnds s s.high (cellHigh p k i)

instance (p : Parameters) (k : Fin 4) (i : ℕ) (s : Strip) : Decidable (Fit p k i s) := by
  unfold Fit StrictAtEnds OrderAtEnds
  infer_instance

@[simp] theorem cast_at (a : Line) (u : ℚ) : ((a.atQ u : ℚ) : ℝ) = a.atR u := by
  simp [Line.atQ,Line.atR]

theorem order_on {s : Strip} {a b : Line} (h : OrderAtEnds s a b) {x : ℝ}
    (hx : x ∈ Icc (s.l : ℝ) (s.r : ℝ)) : a.atR x ≤ b.atR x := by
  have hl : ((a.atQ s.l : ℚ) : ℝ) ≤ (b.atQ s.l : ℝ) := by exact_mod_cast h.1
  have hr : ((a.atQ s.r : ℚ) : ℝ) ≤ (b.atQ s.r : ℝ) := by exact_mod_cast h.2
  simp only [cast_at,Line.atR] at hl hr ⊢
  by_cases hm : (a.m : ℝ) ≤ b.m
  · nlinarith only [hl,mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hx.1)]
  · nlinarith only [hr,mul_nonneg (sub_nonneg.mpr (le_of_not_ge hm)) (sub_nonneg.mpr hx.2)]

theorem strict_on {s : Strip} {a b : Line} (h : StrictAtEnds s a b) {x : ℝ}
    (hx : x ∈ Icc (s.l : ℝ) (s.r : ℝ)) : a.atR x < b.atR x := by
  have hl : ((a.atQ s.l : ℚ) : ℝ) < (b.atQ s.l : ℝ) := by exact_mod_cast h.1
  have hr : ((a.atQ s.r : ℚ) : ℝ) < (b.atQ s.r : ℝ) := by exact_mod_cast h.2
  simp only [cast_at,Line.atR] at hl hr ⊢
  by_cases hm : (a.m : ℝ) ≤ b.m
  · nlinarith only [hl,mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hx.1)]
  · nlinarith only [hr,mul_nonneg (sub_nonneg.mpr (le_of_not_ge hm)) (sub_nonneg.mpr hx.2)]

theorem fit_safe {p : Parameters} {k : Fin 4} {i : ℕ} {s : Strip} (hf : Fit p k i s)
    {u : ℝ} (hu : u∈Icc (s.l : ℝ) (s.r : ℝ)) : Safe s u := by
  rcases hf with ⟨_,hl,_,_,h0,hh,hz,_⟩
  refine ⟨lt_of_lt_of_le (by exact_mod_cast hl) hu.1,?_,order_on hh hu,?_⟩
  · simpa [z,Line.atR] using strict_on h0 hu
  · simpa [roof,Line.atR,sub_eq_add_neg] using strict_on hz hu

def carrier (s : Strip) : Set Point :=
  {x | x 0 ∈ Ioo (s.l : ℝ) (s.r : ℝ) ∧ x 1 ∈ Ioo (s.low.atR (x 0)) (s.high.atR (x 0))}

theorem carrier_measurable (s : Strip) : MeasurableSet (carrier s) := by
  change MeasurableSet (((fun x : Point => x 0) ⁻¹' Ioo (s.l : ℝ) (s.r : ℝ)) ∩ ({x : Point | s.low.atR (x 0) < x 1} ∩
    {x : Point | x 1 < s.high.atR (x 0)}))
  exact (measurable_pi_apply 0 measurableSet_Ioo).inter
    ((measurableSet_lt (by unfold Line.atR; fun_prop) (measurable_pi_apply 1)).inter
      (measurableSet_lt (measurable_pi_apply 1) (by unfold Line.atR; fun_prop)))

private theorem fixed_query {s l r u v : ℝ} (hs : 0<s)
    (hl : 1-r/s-u<v) (hr : v<1-l/s-u) : l<s*(1-u-v) ∧ s*(1-u-v)<r := by
  have h1 : l/s < 1-u-v := by linarith
  have h2 : 1-u-v < r/s := by linarith
  simpa only [mul_comm s] using And.intro ((div_lt_iff₀ hs).mp h1) ((lt_div_iff₀ hs).mp h2)

private theorem moving_query {l r u v : ℝ} (hu : 0<u)
    (hl : 1-(1+r)*u<v) (hr : v<1-(1+l)*u) : l<(1-u-v)/u ∧ (1-u-v)/u<r := by
  constructor
  · apply (lt_div_iff₀ hu).2
    linarith
  · apply (div_lt_iff₀ hu).2
    linarith

theorem carrier_native {p : Parameters} {k : Fin 4} {i : Fin 200} {s : Strip}
    (hp : W2Geometry (physical p)) (hf : Fit p k i.val s) :
    carrier s ⊆ W2PairDomain (physical p) k ∩ tablePullback false (pairProfile (physical p) k) (.inl i) := by
  intro x hx
  rcases hx with ⟨hu,hv⟩
  have hc : x 0 ∈ Icc (s.l : ℝ) (s.r : ℝ) := ⟨hu.1.le,hu.2.le⟩
  have safe := fit_safe hf hc
  rcases hf with ⟨_,_,hxl,hxr,_,_,_,hl,hr,hex,hL,hR⟩
  have hxl' : (lowX p : ℝ)<x 0 := lt_of_le_of_lt (by exact_mod_cast hxl) hu.1
  have hxr' : x 0 < (highX p k : ℝ) := lt_of_lt_of_le hu.2 (by exact_mod_cast hxr)
  have l := lt_of_le_of_lt (order_on hl hc) hv.1
  have r := lt_of_lt_of_le hv.2 (order_on hr hc)
  have e := lt_of_lt_of_le hv.2 (order_on hex hc)
  have L := lt_of_le_of_lt (order_on hL hc) hv.1
  have R := lt_of_lt_of_le hv.2 (order_on hR hc)
  constructor
  · fin_cases k <;>
      simp [W2PairDomain,W2Pair5,W2Pair6,W2Pair7,W2Pair8,physical,a0,a1,a2,a3,
        lowX,highX,bot,top,extra,good5,idLine,constant,Line.atR] at l r e hxl' hxr' ⊢ <;>
      repeat' constructor <;> linarith
  · have hs : (0 : ℝ)<p 1 := W2_anchor_positive hp
    have hq : floorGrid i.val < pairProfile (physical p) k x ∧
        pairProfile (physical p) k x < floorGrid (i.val+1) := by
      by_cases hk : k.val<2
      · have H := fixed_query (u := x 0) (v := x 1) (l := (grid i.val : ℝ))
            (r := (grid (i.val+1) : ℝ)) hs
        have h := H (by simpa [cellLow,hk,Line.atR,sub_eq_add_neg] using L)
          (by simpa [cellHigh,hk,Line.atR,sub_eq_add_neg] using R)
        simpa [pairProfile,hk,fixedPairProfile,physical,grid,floorGrid] using h
      · have H := moving_query (u := x 0) (v := x 1) (l := (grid i.val : ℝ))
            (r := (grid (i.val+1) : ℝ)) safe.u
        have h := H (by simpa [cellLow,hk,Line.atR,sub_eq_add_neg] using L)
          (by simpa [cellHigh,hk,Line.atR,sub_eq_add_neg] using R)
        simpa [pairProfile,hk,movingPairProfile,physical,grid,floorGrid] using h
    change (pairProfile (physical p) k x ∈ Icc 1 5) ∧ _
    have bounds : 1≤floorGrid i.val ∧ floorGrid (i.val+1)≤5 := by
      have hi : (i.val : ℝ) < 200 := by exact_mod_cast i.isLt
      unfold floorGrid
      push_cast
      constructor <;> linarith [Nat.cast_nonneg (R := ℝ) i.val]
    exact ⟨⟨bounds.1.trans hq.1.le,hq.2.le.trans bounds.2⟩,hq⟩

end ImbalancedChen.Part5OriginalH430W2UpperPolygons
