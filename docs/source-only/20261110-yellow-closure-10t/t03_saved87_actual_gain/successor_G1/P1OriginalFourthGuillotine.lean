import ImbalancedChen.P1OriginalFourthRowGap

/-! Midpoint separation of the complete actual 17-byte row list.
The enclosing 16-bit cube has depth 16 in each coordinate. Its
planes down to length 1024 include the archived 1/200 root planes.
The lower-dimensional boundary convention is the physical half-open
logPrimeBox. There are no certificates of disjointness from callers. -/
namespace ImbalancedChen.P1OriginalFourthGuillotine
open P1OriginalPrefixRowDecodeSoundness P1OriginalFourthPackedTable
open P1OriginalFourthRowGap P5OriginalFourthFifthSourceInputs
open Set

abbrev Endpoints := Fin 4 → ℕ
def mid (a b : Endpoints) (i : Fin 4) : ℕ := (a i+b i)/2
def onLeft (i : Fin 4) (m : ℕ) (r : FourthWireRow) : Bool := decide (r.hi i ≤ m)
def good (a b : Endpoints) (xs : List FourthWireRow) (i : Fin 4) : Bool :=
  decide (1 < b i-a i) && xs.all (fun r => decide (r.hi i ≤ mid a b i ∨ mid a b i ≤ r.lo i))
def chooseCut (a b : Endpoints) (xs : List FourthWireRow) :
    Option {i : Fin 4 // good a b xs i = true} :=
  if h : good a b xs 0 = true then some ⟨0,h⟩
  else if h : good a b xs 1 = true then some ⟨1,h⟩
  else if h : good a b xs 2 = true then some ⟨2,h⟩
  else if h : good a b xs 3 = true then some ⟨3,h⟩ else none

def check : ℕ → Endpoints → Endpoints → List FourthWireRow → Bool
  | _, _, _, [] => true
  | _, _, _, [_] => true
  | 0, _, _, _::_::_ => false
  | fuel+1, a, b, x::y::xs =>
      let rows := x::y::xs
      match chooseCut a b rows with
      | none => false
      | some d =>
        let i := d.val
        let m := mid a b i
        let p := onLeft i m
        check fuel a (Function.update b i m) (rows.filter p) &&
          check fuel (Function.update a i m) b (rows.filter (fun r => !(p r)))

def Sep (x y : FourthWireRow) : Prop := Disjoint (box x) (box y)

theorem cut_separates (i : Fin 4) (x y : FourthWireRow) (hxy : x.hi i ≤ y.lo i) : Sep x y := by
  apply Set.disjoint_left.mpr
  intro t hx hy
  have h1 := (mem_logPrimeBox.mp hx i).2
  have h2 := (mem_logPrimeBox.mp hy i).1
  have h3 : right x i ≤ left y i := by
    simp only [right,left,fourth_upper,fourth_lower,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hxy) (by norm_num)
  exact (not_lt_of_ge h2) (h1.trans_le h3)

private theorem join (p : FourthWireRow → Bool) (xs : List FourthWireRow)
    (hl : (xs.filter p).Pairwise Sep) (hr : (xs.filter (fun r => !(p r))).Pairwise Sep)
    (hc : ∀ x ∈ xs, ∀ y ∈ xs, p x = true → p y = false → Sep x y) : xs.Pairwise Sep := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have hc' (v : FourthWireRow) (hv : v ∈ xs) (w : FourthWireRow) (hw : w ∈ xs) :=
      hc v (List.mem_cons_of_mem _ hv) w (List.mem_cons_of_mem _ hw)
    cases hx : p x with
    | true =>
      have hL : (x::xs.filter p).Pairwise Sep := by simpa [hx] using hl
      have hR : (xs.filter (fun r => !(p r))).Pairwise Sep := by simpa [hx] using hr
      refine List.pairwise_cons.mpr ⟨?_,ih (List.pairwise_cons.mp hL).2 hR hc'⟩
      intro y hy
      cases hy' : p y with
      | false => exact hc x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hx hy'
      | true => exact (List.pairwise_cons.mp hL).1 y (List.mem_filter.mpr ⟨hy,hy'⟩)
    | false =>
      have hL : (xs.filter p).Pairwise Sep := by simpa [hx] using hl
      have hR : (x::xs.filter (fun r => !(p r))).Pairwise Sep := by simpa [hx] using hr
      refine List.pairwise_cons.mpr ⟨?_,ih hL (List.pairwise_cons.mp hR).2 hc'⟩
      intro y hy
      cases hy' : p y with
      | false => exact (List.pairwise_cons.mp hR).1 y (List.mem_filter.mpr ⟨hy,by simp [hy']⟩)
      | true => exact (hc y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hy' hx).symm

theorem check_sound (fuel : ℕ) (a b : Endpoints) (xs : List FourthWireRow)
    (h : check fuel a b xs = true) : xs.Pairwise Sep := by
  induction fuel generalizing a b xs with
  | zero =>
    cases xs with
    | nil => simp
    | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys => simp [check] at h
  | succ fuel ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys =>
        cases he : chooseCut a b (x::y::ys) with
        | none => simp [check,he] at h
        | some d =>
          let xs := x::y::ys
          let m := mid a b d.val
          let p := onLeft d.val m
          have hh : check fuel a (Function.update b d.val m) (xs.filter p) = true ∧
              check fuel (Function.update a d.val m) b (xs.filter (fun r => !(p r))) = true := by
            simpa only [check,he,Bool.and_eq_true,xs,m,p] using h
          apply join p xs (ih _ _ _ hh.1) (ih _ _ _ hh.2)
          intro u hu v hv hup hvp
          have hleft : u.hi d.val ≤ m := by simpa only [p,onLeft,decide_eq_true_eq] using hup
          have hn : ¬ v.hi d.val ≤ m := by simpa only [p,onLeft,decide_eq_false_iff_not] using hvp
          have hf := (Bool.and_eq_true.mp d.property).2
          have hsep : v.hi d.val ≤ m ∨ m ≤ v.lo d.val :=
            of_decide_eq_true (List.all_eq_true.mp hf v hv)
          exact cut_separates d.val u v (hleft.trans (hsep.resolve_left hn))

noncomputable section

def originalDisjointCheck : Bool :=
  match decodeWireRows originalFourthBytes with
  | none => false
  | some rs => check 64 (fun _ => 0) (fun _ => 65536) rs

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem original_disjoint_check : originalDisjointCheck = true := by decide

theorem original_half_open_disjoint : originalFourthWireRows.Pairwise Sep := by
  apply check_sound 64 (fun _ => 0) (fun _ => 65536)
  simpa only [originalDisjointCheck,originalFourth_parse] using original_disjoint_check

end
end ImbalancedChen.P1OriginalFourthGuillotine
