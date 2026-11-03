import ImbalancedChen.P2GammaJointSameRhoBlockSource
import Mathlib.Data.Nat.Log

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Exact binary prefix decomposition of the original integer head intervals.
At each scale a prefix selects at most one LEFT half of a binary cell.
The left halves are disjoint at that scale, even for arbitrarily many
original endpoints. Clipping preserves this disjointness. No interval
count or overlap bound for the old family is assumed.
-/

namespace ImbalancedChen.P2GammaDyadicHeadIntervals
noncomputable section
open scoped Classical BigOperators

/-- The lower multiple of 2^d below n. -/
def cut (d n : ℕ) : ℕ := n / 2^d * 2^d

def prefixKey (d n : ℕ) : ℕ := n / 2^(d+1)

def Active (d n : ℕ) : Prop := (n / 2^d) % 2 = 1

/-- LEFT half of the binary parent indexed by b. All endpoints are exact. -/
def cell (d b : ℕ) : Finset ℕ :=
  Finset.Ioc ((2*b)*2^d) ((2*b+1)*2^d)

/-- The common original head window is imposed geometrically, not as an
arithmetic condition on the coefficient. -/
def clippedCell (L P d b : ℕ) : Finset ℕ :=
  (cell d b).filter (fun p => L < p ∧ p ≤ P)

def prefix (n : ℕ) (F : ℕ → ℂ) : ℂ := ∑ p ∈ Finset.Ioc 0 n,F p

def piece (d n : ℕ) (F : ℕ → ℂ) : ℂ :=
  if Active d n then ∑ p ∈ cell d (prefixKey d n),F p else 0

def clippedPiece (L P d n : ℕ) (F : ℕ → ℂ) : ℂ :=
  if Active d n then ∑ p ∈ clippedCell L P d (prefixKey d n),F p else 0

/-- Finite prefix addition, including a=b=0 and every endpoint. -/
theorem prefix_split {a b : ℕ} (hab : a ≤ b) (F : ℕ → ℂ) :
    prefix b F = prefix a F + ∑ p ∈ Finset.Ioc a b,F p := by
  have hu : Finset.Ioc 0 b = Finset.Ioc 0 a ∪ Finset.Ioc a b := by
    ext p
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a b) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := Finset.mem_Ioc.mp hp
    have hq' := Finset.mem_Ioc.mp hq
    omega
  unfold prefix
  rw [hu,Finset.sum_union hd]

/-- The quotient parity is the exact binary digit; no numerical guard. -/
theorem cut_step (d n : ℕ) :
    cut d n = cut (d+1) n + ((n / 2^d) % 2)*2^d := by
  have hdiv : n / 2^(d+1) = (n / 2^d)/2 := by
    rw [Nat.div_div_eq_div_mul,pow_succ]
  have hmod := Nat.mod_add_div (n / 2^d) 2
  calc
    cut d n = ((n / 2^d)%2 + 2*((n / 2^d)/2))*2^d := by
      rw [hmod]; rfl
    _ = cut (d+1) n + ((n / 2^d)%2)*2^d := by
      simp only [cut,hdiv,pow_succ]
      ring

theorem cut_next_eq_start (d n : ℕ) :
    cut (d+1) n = (2*prefixKey d n)*2^d := by
  unfold cut prefixKey
  rw [pow_succ]
  ring

theorem prefix_step (d n : ℕ) (F : ℕ → ℂ) :
    prefix (cut d n) F = prefix (cut (d+1) n) F + piece d n F := by
  have hm := Nat.mod_lt (n / 2^d) (by omega : 0 < 2)
  by_cases ha : Active d n
  · have hd : (n / 2^d)%2 = 1 := ha
    have hc : cut d n = (2*prefixKey d n+1)*2^d := by
      rw [cut_step,cut_next_eq_start,hd]
      ring
    rw [piece,if_pos ha,hc,cut_next_eq_start]
    exact prefix_split (by nlinarith [Nat.zero_le (2^d)]) F
  · have hd : (n / 2^d)%2 = 0 := by unfold Active at ha; omega
    rw [piece,if_neg ha,cut_step,hd,zero_mul,add_zero,add_zero]

/-- Telescoping is proved before choosing a cap. -/
theorem prefix_telescope (D n : ℕ) (F : ℕ → ℂ) :
    prefix n F = prefix (cut D n) F + ∑ d ∈ Finset.range D,piece d n F := by
  induction D with
  | zero => simp [cut]
  | succ D ih =>
      calc
        _ = prefix (cut D n) F + ∑ d ∈ Finset.range D,piece d n F := ih
        _ = _ := by rw [prefix_step,Finset.sum_range_succ]; abel

theorem prefix_expansion {D n : ℕ} (hn : n < 2^D) (F : ℕ → ℂ) :
    prefix n F = ∑ d ∈ Finset.range D,piece d n F := by
  have h := prefix_telescope D n F
  simpa only [cut,Nat.div_eq_of_lt hn,zero_mul,prefix,Finset.Ioc_self,
    Finset.sum_empty,zero_add] using h

def depth (P : ℕ) : ℕ := Nat.log 2 P + 1

theorem below_depth {n P : ℕ} (hn : n ≤ P) : n < 2^(depth P) :=
  hn.trans_lt (Nat.lt_pow_succ_log_self (by omega : 1 < 2) P)

/-- Two prefixes recover a literal open-left/closed-right interval. -/
theorem interval_expansion {a b P : ℕ} (hab : a ≤ b) (hb : b ≤ P)
    (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc a b,F p) =
      ∑ d ∈ Finset.range (depth P),(piece d b F-piece d a F) := by
  calc
    _ = prefix b F-prefix a F := by rw [prefix_split hab F]; abel
    _ = _ := by
      rw [prefix_expansion (below_depth hb),prefix_expansion (below_depth (hab.trans hb)),
        Finset.sum_sub_distrib]

/-- A common clip may be applied to every cell before the arithmetic test.
No below-window values of the test or profile are required to vanish. -/
theorem clipped_interval_expansion {L a b P : ℕ}
    (hLa : L ≤ a) (hab : a ≤ b) (hb : b ≤ P) (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc a b,F p) =
      ∑ d ∈ Finset.range (depth P),
        (clippedPiece L P d b F-clippedPiece L P d a F) := by
  let G := fun p => if L < p ∧ p ≤ P then F p else 0
  have hF : (∑ p ∈ Finset.Ioc a b,F p) = ∑ p ∈ Finset.Ioc a b,G p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_Ioc.mp hp
    simp only [G,if_pos (show L < p ∧ p ≤ P by omega)]
  rw [hF,interval_expansion hab hb G]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [piece,clippedPiece,clippedCell,Finset.sum_filter,G]

/-- Strict separation of left-half cells at the same scale. -/
theorem cell_disjoint (d : ℕ) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (cell d a) (cell d b) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨hpa,hpa'⟩ := Finset.mem_Ioc.mp hp
  obtain ⟨hpb,hpb'⟩ := Finset.mem_Ioc.mp hq
  have hs : 0 < 2^d := by positivity
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hsep : (2*a+1)*2^d ≤ (2*b)*2^d :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have hsep : (2*b+1)*2^d ≤ (2*a)*2^d :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem clippedCell_subset (L P d b : ℕ) :
    clippedCell L P d b ⊆ Finset.Icc 1 P := by
  intro p hp
  obtain ⟨_,hLp,hpP⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_Icc.mpr ⟨by omega,hpP⟩

theorem clippedCell_disjoint (L P d : ℕ) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (clippedCell L P d a) (clippedCell L P d b) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (cell_disjoint d hab)
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1

/-- At most one head copy per point at a fixed scale; no old head-key
multiplicity occurs, even when K contains every possible binary cell. -/
theorem sum_clipped_cells_le (L P d : ℕ) (K : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p,0 ≤ f p) :
    (∑ b ∈ K,∑ p ∈ clippedCell L P d b,f p) ≤
      ∑ p ∈ Finset.Icc 1 P,f p := by
  have hd : (↑K : Set ℕ).PairwiseDisjoint (clippedCell L P d) := by
    intro a ha b hb hab
    exact clippedCell_disjoint L P d hab
  rw [← Finset.sum_biUnion hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨b,hb,hp⟩ := Finset.mem_biUnion.mp hp
    exact clippedCell_subset L P d b hp
  · intro p hp hnot
    exact hf p

/-- Exact geometric interval form, including an empty or reversed clip. -/
theorem clippedCell_eq_Ioc (L P d b : ℕ) :
    clippedCell L P d b =
      Finset.Ioc (max L ((2*b)*2^d)) (min P ((2*b+1)*2^d)) := by
  ext p
  simp only [clippedCell,cell,Finset.mem_filter,Finset.mem_Ioc,
    max_lt_iff,le_min_iff]
  tauto

/-- Reuse the already supplied logarithmic bound for this exact depth. -/
theorem depth_le_logGauge (P : ℕ) :
    (depth P : ℝ) ≤ P2GammaConductorScaleThreshold.dyadicCountCoefficient *
      P2GammaConductorScaleThreshold.logGauge P :=
  P2GammaConductorScaleThreshold.dyadicCount_le_logGauge P

end
end ImbalancedChen.P2GammaDyadicHeadIntervals
