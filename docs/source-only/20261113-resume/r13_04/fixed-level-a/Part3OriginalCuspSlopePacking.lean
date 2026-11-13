import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Two slope coordinates count the actual short denominator lines. The endpoints
of the slope intervals are included. The high strip itself will be half-open. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalCuspSlopePacking20261112
open Finset Set

def wedge (v w : ℝ×ℝ) : ℝ := v.1*w.2-w.1*v.2

private def axis (v : ℝ×ℝ) : Bool := decide (|v.2|≤|v.1|)
private def main (v : ℝ×ℝ) : ℝ := if axis v then v.1 else v.2
private def other (v : ℝ×ℝ) : ℝ := if axis v then v.2 else v.1
private def slope (v : ℝ×ℝ) : ℝ := other v/main v

private theorem parts (v : ℝ×ℝ) (hv : 0<v.1^2+v.2^2) :
    main v≠0 ∧ |other v|≤|main v| ∧ |slope v|≤1 := by
  have h : |other v|≤|main v| := by
    by_cases he : |v.2|≤|v.1|
    · simpa [main,other,axis,he] using he
    · simpa [main,other,axis,he] using (le_of_not_ge he : |v.1|≤|v.2|)
  have h0 : main v≠0 := by
    intro z
    have z' : other v=0 := abs_nonpos_iff.mp (by simpa [z] using h)
    by_cases he : |v.2|≤|v.1| <;>simp [main,other,axis,he] at z z' <;>simp [z,z'] at hv
  exact ⟨h0,h,by rw [slope,abs_div,div_le_one (abs_pos.mpr h0)];exact h⟩

private theorem separation (z Y : ℝ) (hY : 0<Y) (v w : ℝ×ℝ)
    (hv0 : 0<v.1^2+v.2^2) (hw0 : 0<w.1^2+w.2^2)
    (hv : v.1^2+v.2^2≤1/Y) (hw : w.1^2+w.2^2≤1/Y)
    (same : axis v=axis w) (gap : z≤|wedge v w|) :
    z*Y≤|slope w-slope v| := by
  have H (u : ℝ×ℝ) : (main u)^2≤u.1^2+u.2^2 := by
    unfold main;split <;>nlinarith [sq_nonneg u.1,sq_nonneg u.2]
  have p : |main v*main w|≤1/Y := by
    rw [abs_mul]
    nlinarith [sq_abs (main v),sq_abs (main w),sq_nonneg (|main v|-|main w|),H v,H w]
  have e : |wedge v w|=|main v*main w|*|slope w-slope v| := by
    rw [←abs_mul]
    have V := (parts v hv0).1
    have W := (parts w hw0).1
    cases h : axis v
    · have h' : axis w=false := same.symm.trans h
      simp only [slope,other,main,h,h',Bool.false_eq_true,if_false] at V W ⊢
      rw [show v.2*w.2*(w.1/w.2-v.1/v.2)= -(wedge v w) by
        unfold wedge; field_simp [V,W] <;>ring,abs_neg]
    · have h' : axis w=true := same.symm.trans h
      simp only [slope,other,main,h,h',if_true] at V W ⊢
      rw [show v.1*w.1*(w.2/w.1-v.2/v.1)=wedge v w by
        unfold wedge;field_simp [V,W] <;>ring]
  have A := (gap.trans_eq e).trans (mul_le_mul_of_nonneg_right p (abs_nonneg _))
  calc
    z*Y ≤ (1/Y*|slope w-slope v|)*Y := mul_le_mul_of_nonneg_right A hY.le
    _ = _ := by field_simp [hY.ne']

theorem count_lines {ι : Type*} (s : Finset ι) (v : ι→ℝ×ℝ) {z Y : ℝ}
    (hz : 0<z) (hY : 0<Y)
    (short : ∀ i∈s,0<(v i).1^2+(v i).2^2 ∧ (v i).1^2+(v i).2^2≤1/Y)
    (det : ∀ i∈s,∀ j∈s,i≠j→z≤|wedge (v i) (v j)|) :
    (s.card:ℝ)≤2+4/(z*Y) := by
  classical
  let A := z*Y
  have ap : 0<A := mul_pos hz hY
  let k := ⌊2/A⌋₊+1
  let t := fun i => (slope (v i)+1)/A
  have bd (i) (hi : i∈s) : 0≤t i ∧ t i≤2/A := by
    have h := abs_le.mp (parts (v i) (short i hi).1).2.2
    exact ⟨div_nonneg (by linarith [h.1]) ap.le,div_le_div_of_nonneg_right (by linarith [h.2]) ap.le⟩
  let f := fun i : s => (axis (v i), (⟨⌊t i⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (bd i i.2).2)⟩ : Fin k))
  have inj : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    by_contra ne
    have ax := congrArg Prod.fst h
    have fl : ⌊t i⌋₊=⌊t j⌋₊ := congrArg (fun b : Bool×Fin k => b.2.val) h
    have sep := separation z Y hY (v i) (v j) (short _ i.2).1 (short _ j.2).1
      (short _ i.2).2 (short _ j.2).2 ax (det _ i.2 _ j.2 ne)
    have floorN (u : s) := Nat.floor_le (bd u u.2).1
    have ij : t j<t i+1 := (Nat.lt_floor_add_one (t j)).trans_le (by rw [←fl];linarith [floorN i])
    have ji : t i<t j+1 := (Nat.lt_floor_add_one (t i)).trans_le (by rw [fl];linarith [floorN j])
    have a : |slope (v j)-slope (v i)|<A := by
      apply abs_lt.mpr
      have ea := (div_lt_iff₀ ap).mp (show (slope (v i)+1)/A<t j+1 from ji)
      have eb := (div_lt_iff₀ ap).mp (show (slope (v j)+1)/A<t i+1 from ij)
      dsimp only [t] at ea eb
      rw [add_mul,div_mul_cancel₀ _ ap.ne',one_mul] at ea eb
      constructor <;> linarith
    exact (not_lt_of_ge sep) a
  have cards := Fintype.card_le_of_injective f inj
  have c : s.card≤2*k := by simpa using cards
  have floor_le := Nat.floor_le (show (0:ℝ)≤2/A by positivity)
  have cr : (s.card:ℝ)≤2*((⌊2/A⌋₊:ℕ):ℝ)+2 := by
    have cr' : (s.card:ℝ)≤(2:ℝ)*(k:ℝ) := by exact_mod_cast c
    dsimp [k] at cr';push_cast at cr';linarith
  calc
    _ ≤ 2*((⌊2/A⌋₊:ℕ):ℝ)+2 := cr
    _ ≤ 2*(2/A)+2 := add_le_add_right (mul_le_mul_of_nonneg_left floor_le (by norm_num)) 2
    _ = _ := by dsimp only [A]; ring

end ImbalancedChen.Part3.OriginalCuspSlopePacking20261112
end
