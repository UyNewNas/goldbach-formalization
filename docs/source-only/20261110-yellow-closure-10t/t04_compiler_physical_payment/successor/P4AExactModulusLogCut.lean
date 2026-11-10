import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! An exact finite lower cut in sums of logarithms. The arbitrary real
threshold is never rounded. Distinct *attained* rational products have an
elementary separation bound. Each integer digit reads one modulus slot. -/
namespace ImbalancedChen.P4AExactModulusLogCut
noncomputable section
open scoped Classical BigOperators
open Classical

theorem integer_log_gap {a b h : ℕ} (ha : 0 < a) (hab : a < b) (hbh : b ≤ h) :
    (1 : ℝ) / h ≤ Real.log b - Real.log a := by
  have hb : 0 < b := ha.trans hab
  have har : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb
  have hstep : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
  have hsmall := Real.one_sub_inv_le_log_of_pos (div_pos hbr har)
  rw [Real.log_div hbr.ne' har.ne',inv_div] at hsmall
  calc
    (1:ℝ)/h ≤ 1/b := one_div_le_one_div_of_le hbr (by exact_mod_cast hbh)
    _ ≤ 1-(a:ℝ)/b := by
      rw [le_sub_iff_add_le,← add_div,div_le_iff₀ hbr]
      linarith
    _ ≤ _ := hsmall

theorem ratio_log_gap {a b c d H : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (hcH : c≤H) (hbH : b≤H)
    (hlt : Real.log a-Real.log b < Real.log c-Real.log d) :
    (1:ℝ)/(H*H) ≤ (Real.log c-Real.log d)-(Real.log a-Real.log b) := by
  have hat : (0:ℝ)<a := by exact_mod_cast ha
  have hbt : (0:ℝ)<b := by exact_mod_cast hb
  have hct : (0:ℝ)<c := by exact_mod_cast hc
  have hdt : (0:ℝ)<d := by exact_mod_cast hd
  have hl : Real.log ((a*d:ℕ):ℝ) < Real.log ((c*b:ℕ):ℝ) := by
    rw [Nat.cast_mul,Nat.cast_mul,Real.log_mul hat.ne' hdt.ne',Real.log_mul hct.ne' hbt.ne']
    linarith
  have hcross : a*d<c*b := by
    exact_mod_cast (Real.log_lt_log_iff (by positivity) (by positivity)).mp hl
  have hg := integer_log_gap (Nat.mul_pos ha hd) hcross (Nat.mul_le_mul hcH hbH)
  push_cast at hg
  rw [Real.log_mul hct.ne' hbt.ne',Real.log_mul hat.ne' hdt.ne'] at hg
  linarith

def slot (u v : ℕ) : ℝ := Real.log u - Real.log v
def digit (L u v : ℕ) : ℕ := ⌊(L:ℝ)*slot u v⌋₊

section
variable {k : ℕ} (u v : Fin k → ℕ → ℕ)

def score (p : Fin k → ℕ) : ℝ := ∑ i, slot (u i (p i)) (v i (p i))
def code (L : ℕ) (p : Fin k → ℕ) : ℕ := ∑ i, digit L (u i (p i)) (v i (p i))
def bounded (H : ℕ) (p : Fin k → ℕ) : Prop :=
  (∀ i, 0<v i (p i) ∧ v i (p i) ≤ u i (p i)) ∧ (∏ i, u i (p i)) ≤ H

theorem score_logs {H : ℕ} {p : Fin k → ℕ} (hp : bounded u v H p) :
    score u v p = Real.log ((∏ i, u i (p i) : ℕ) : ℝ) -
      Real.log ((∏ i, v i (p i) : ℕ) : ℝ) := by
  have hu (i : Fin k) : (u i (p i):ℝ) ≠ 0 := by exact_mod_cast ((hp.1 i).1.trans_le (hp.1 i).2).ne'
  have hv (i : Fin k) : (v i (p i):ℝ) ≠ 0 := by exact_mod_cast (hp.1 i).1.ne'
  simp only [score,slot,Nat.cast_prod,Real.log_prod (fun i _ => hu i),
    Real.log_prod (fun i _ => hv i),Finset.sum_sub_distrib]

private theorem product_info {H : ℕ} {p : Fin k → ℕ} (hp : bounded u v H p) :
    0 < ∏ i, v i (p i) ∧ (∏ i, v i (p i)) ≤ ∏ i, u i (p i) := by
  exact ⟨Finset.prod_pos fun i _ => (hp.1 i).1,
    Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => (hp.1 i).2)⟩

theorem code_bounds (L : ℕ) {H : ℕ} {p : Fin k → ℕ} (hp : bounded u v H p) :
    (code u v L p:ℝ) ≤ L*score u v p ∧
      L*score u v p ≤ (code u v L p:ℝ)+k := by
  have nonneg (i : Fin k) : 0 ≤ slot (u i (p i)) (v i (p i)) := by
    apply sub_nonneg.mpr
    apply Real.log_le_log (by exact_mod_cast (hp.1 i).1)
    exact_mod_cast (hp.1 i).2
  have lo := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg L) (nonneg i)))
  have hi := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i ∈ (Finset.univ:Finset (Fin k))) =>
    (Nat.lt_floor_add_one ((L:ℝ)*slot (u i (p i)) (v i (p i)))).le)
  simpa [code,score,digit,Finset.mul_sum,Finset.sum_add_distrib] using And.intro lo hi

def scale (k H : ℕ) := (k+2)*(H*H)
def period (k H : ℕ) := scale k H * H + 3

instance period_neZero (k H : ℕ) : NeZero (period k H) :=
  ⟨by unfold period; omega⟩

theorem code_strict {H : ℕ} {p q : Fin k → ℕ} (hp : bounded u v H p)
    (hq : bounded u v H q) (hlt : score u v p < score u v q) :
    code u v (scale k H) p < code u v (scale k H) q := by
  obtain ⟨hpv,hpvu⟩ := product_info u v hp
  obtain ⟨hqv,hqvu⟩ := product_info u v hq
  have hH : 0<H := hpv.trans_le (hpvu.trans hp.2)
  have hg := ratio_log_gap (hpv.trans_le hpvu) hpv (hqv.trans_le hqvu) hqv
    hq.2 (hpvu.trans hp.2) (by simpa only [← score_logs u v hp,← score_logs u v hq] using hlt)
  rw [← score_logs u v hq,← score_logs u v hp] at hg
  have hsH : (0:ℝ)<H := by exact_mod_cast hH
  have hg' := (div_le_iff₀ (mul_pos hsH hsH)).mp hg
  have hm := mul_le_mul_of_nonneg_left hg' (by positivity : 0≤(k:ℝ)+2)
  have hlo := (code_bounds u v (scale k H) hp).1
  have hhi := (code_bounds u v (scale k H) hq).2
  simp only [scale,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at hlo hhi
  exact_mod_cast (show (code u v (scale k H) p : ℝ)<(code u v (scale k H) q:ℝ) by nlinarith)

theorem code_le {H : ℕ} {p : Fin k → ℕ} (hp : bounded u v H p) :
    code u v (scale k H) p ≤ scale k H * H := by
  obtain ⟨hpv,hpvu⟩ := product_info u v hp
  have hpvr : (1:ℝ) ≤ ((∏ i, v i (p i):ℕ):ℝ) := by exact_mod_cast hpv
  have hpu : 0 < ((∏ i, u i (p i):ℕ):ℝ) := by exact_mod_cast hpv.trans_le hpvu
  have hH : ((∏ i, u i (p i):ℕ):ℝ) ≤ H := by exact_mod_cast hp.2
  have hs : score u v p ≤ H := by
    rw [score_logs u v hp]
    linarith [Real.log_le_sub_one_of_pos hpu,Real.log_nonneg hpvr]
  have h := (code_bounds u v (scale k H) hp).1.trans
    (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  exact_mod_cast h

/-- True and false may be separated at an arbitrary real threshold,
including a tie. The cutoff is constructed from the true tuples. -/
theorem exists_cut (H : ℕ) (T : Finset (Fin k → ℕ))
    (hT : ∀ p ∈ T, bounded u v H p) (good : (Fin k → ℕ) → Prop)
    (hord : ∀ p ∈ T, ∀ q ∈ T, good p → ¬ good q → score u v p < score u v q) :
    ∃ b < period k H, ∀ p ∈ T, good p ↔ code u v (scale k H) p < b := by
  classical
  let A := T.filter good
  let f := code u v (scale k H)
  by_cases hA : A.Nonempty
  · obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup A hA f
    have ha' := Finset.mem_filter.mp (show a ∈ T.filter good from ha)
    have hbound := code_le u v (hT a ha'.1)
    refine ⟨A.sup f+1,?_,?_⟩
    · rw [he]; change f a+1 < scale k H*H+3
      dsimp [f]; omega
    · intro p hp
      constructor
      · intro hg
        exact Nat.lt_succ_of_le (Finset.le_sup (s:=A) (f:=f) (Finset.mem_filter.mpr ⟨hp,hg⟩))
      · intro hl
        by_contra hn
        have hlt := code_strict u v (hT a ha'.1) (hT p hp) (hord a ha'.1 p hp ha'.2 hn)
        rw [he] at hl
        change f a < f p at hlt
        change f p < f a+1 at hl
        omega
  · refine ⟨0,by simp [period],?_⟩
    intro p hp
    have hn : ¬good p := fun h => hA ⟨p,Finset.mem_filter.mpr ⟨hp,h⟩⟩
    simp [hn]

end
end
end ImbalancedChen.P4AExactModulusLogCut
