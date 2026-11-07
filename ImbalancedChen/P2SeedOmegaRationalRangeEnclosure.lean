import ImbalancedChen.P2SeedOmegaRationalCellArea
import ImbalancedChen.P2BuchstabRationalSemantics

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
TRUE Buchstab enclosures on arbitrary rational argument ranges. Both
node indices and their whole-range membership are PRODUCED by rational
floors. Weighted monotonicity transports the causal recurrence endpoints;
no pointwise omega enclosure or desired integral gain is a premise.
The finite recurrence array must still be supplied/checked by Dots.
-/

namespace ImbalancedChen.P2SeedOmegaRationalRangeEnclosure
noncomputable section
open Set
open Certificates.P2BuchstabRationalSemantics

def queryIndex (m : ℕ) (r : ℚ) : ℕ := ⌊(r-1)*(m:ℚ)⌋₊
def lowerOmega (m : ℕ) (cs : List NodeEnclosure) (lo hi : ℚ) : ℚ :=
  max 0 (entry cs (queryIndex m lo)).lower/hi
def upperOmega (m : ℕ) (cs : List NodeEnclosure) (lo hi : ℚ) : ℚ :=
  max 0 (entry cs (queryIndex m hi+1)).upper/lo

theorem queryIndex_mono {m : ℕ} {a b : ℚ} (hab : a≤b) :
    queryIndex m a≤queryIndex m b :=
  Nat.floor_mono (mul_le_mul_of_nonneg_right (sub_le_sub_right hab 1) (Nat.cast_nonneg m))

/-- Exact internally generated left and right grid ownership. The
right index is floor+1, including a rational query exactly on a grid node. -/
theorem query_grid_bounds {m : ℕ} (hm : 0<m) {r : ℚ} (hr : 1≤r) :
    grid m (queryIndex m r)≤r ∧ r<grid m (queryIndex m r+1) := by
  have hmQ : (0:ℚ)<m := by exact_mod_cast hm
  have hf : (queryIndex m r:ℚ)≤(r-1)*(m:ℚ) :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hr) hmQ.le)
  have hn : (r-1)*(m:ℚ)<(queryIndex m r:ℚ)+1 := Nat.lt_floor_add_one _
  have hleft : (queryIndex m r:ℚ)/(m:ℚ)≤r-1 :=
    (div_le_iff₀ hmQ).mpr (by nlinarith only [hf])
  have hright : r-1<((queryIndex m r:ℚ)+1)/(m:ℚ) :=
    (lt_div_iff₀ hmQ).mpr hn
  constructor
  · dsimp [grid]
    linarith only [hleft]
  · simp only [grid,Nat.cast_add,Nat.cast_one]
    linarith only [hright]

theorem grid_ge_one {m : ℕ} (hm : 0<m) (k : ℕ) : (1:ℚ)≤grid m k := by
  have hmQ : (0:ℚ)<m := by exact_mod_cast hm
  have h := div_nonneg (Nat.cast_nonneg k : (0:ℚ)≤k) hmQ.le
  dsimp [grid]
  linarith only [h]

/-- Causal recurrence semantics supplies an enclosure on the ENTIRE
rational query range. Only index coverage and the recurrence checker are
finite inputs; neither omega nor an integral occurs in those inputs. -/
theorem actual_buchstab_range_enclosure {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs=true) {lo hi : ℚ} (hlo : 1≤lo) (horder : lo≤hi)
    (hcover : queryIndex m hi+1<cs.length) {r : ℝ}
    (hr : r ∈ Icc (lo:ℝ) (hi:ℝ)) :
    (lowerOmega m cs lo hi:ℝ)≤LiLiuPrereqBuchstab.buchstab r ∧
      LiLiuPrereqBuchstab.buchstab r≤(upperOmega m cs lo hi:ℝ) := by
  have hm := (of_decide_eq_true hc : Valid m cs).1
  have hi1 : (1:ℚ)≤hi := hlo.trans horder
  have hL := query_grid_bounds hm hlo
  have hR := query_grid_bounds hm hi1
  have hkL : queryIndex m lo<cs.length :=
    (lt_of_le_of_lt (queryIndex_mono horder) (Nat.lt_succ_self _)).trans hcover
  have hLN := check_sound hc (k:=queryIndex m lo) hkL
  have hRN := check_sound hc (k:=queryIndex m hi+1) hcover
  have hgrid1 : (1:ℝ)≤(grid m (queryIndex m lo):ℝ) := by
    exact_mod_cast grid_ge_one hm (queryIndex m lo)
  have hgridLo : (grid m (queryIndex m lo):ℝ)≤r := by
    have h : (grid m (queryIndex m lo):ℝ)≤(lo:ℝ) := by exact_mod_cast hL.1
    exact h.trans hr.1
  have hgridHi : r≤(grid m (queryIndex m hi+1):ℝ) := by
    have h : (hi:ℝ)<(grid m (queryIndex m hi+1):ℝ) := by exact_mod_cast hR.2
    exact hr.2.trans h.le
  have hr1 : 1≤r := by
    have h : (1:ℝ)≤(lo:ℝ) := by exact_mod_cast hlo
    exact h.trans hr.1
  have hr0 : 0<r := zero_lt_one.trans_le hr1
  have hlo0 : (0:ℝ)<(lo:ℝ) := by exact_mod_cast zero_lt_one.trans_le hlo
  have hhi0 : (0:ℝ)<(hi:ℝ) := by exact_mod_cast zero_lt_one.trans_le hi1
  have hW0 : 0≤weighted r :=
    (mul_pos hr0 (buchstab_positive r)).le
  have hlow : (max 0 (entry cs (queryIndex m lo)).lower:ℝ)≤weighted r := by
    simp only [Rat.cast_max,Rat.cast_zero]
    exact max_le hW0 (hLN.1.trans (weighted_mono hgrid1 hgridLo))
  have hhigh : weighted r≤(max 0 (entry cs (queryIndex m hi+1)).upper:ℝ) := by
    have h := (weighted_mono hr1 hgridHi).trans hRN.2
    exact h.trans (by simp only [Rat.cast_max,Rat.cast_zero]; exact le_max_right _ _)
  have hlow0 : (0:ℝ)≤(max 0 (entry cs (queryIndex m lo)).lower:ℝ) := by positivity
  have hhigh0 : (0:ℝ)≤(max 0 (entry cs (queryIndex m hi+1)).upper:ℝ) := by positivity
  constructor
  · have hdiv : (max 0 (entry cs (queryIndex m lo)).lower:ℝ)/r≤
        LiLiuPrereqBuchstab.buchstab r := by
      apply (div_le_iff₀ hr0).mpr
      simpa only [weighted,mul_comm] using hlow
    have h := (div_le_div_of_nonneg_left hlow0 hr0 hr.2).trans hdiv
    simpa only [lowerOmega,Rat.cast_div] using h
  · have hdiv : LiLiuPrereqBuchstab.buchstab r≤
        (max 0 (entry cs (queryIndex m hi+1)).upper:ℝ)/r := by
      apply (le_div_iff₀ hr0).mpr
      simpa only [weighted,mul_comm] using hhigh
    have h := hdiv.trans (div_le_div_of_nonneg_left hhigh0 hlo0 hr.1)
    simpa only [upperOmega,Rat.cast_div] using h

end
end ImbalancedChen.P2SeedOmegaRationalRangeEnclosure
