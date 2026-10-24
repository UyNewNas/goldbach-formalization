import ImbalancedChen.ActualThirdOriginalRoundedNewOperations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
Literal positive-series unit_log and the no-range-reduction branch of ln from
numerical-w2-affine-series-independent-20261010.py. The integer interval and
P160=2^160 are imported. No checked-log certificate, new safety rounding, or
logarithm enclosure hypothesis is used. -/
namespace ImbalancedChen.OriginalThirdPositiveLogSourceOnly
noncomputable section
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open Finset

def add (v w : IV) : IV := ⟨v.lo+w.lo,v.hi+w.hi⟩

/-- Positive rational integer division, NOT division by an interval. -/
def divNat (v : IV) (k : ℕ) : IV := ⟨v.lo/(k:ℤ),up v.hi (k:ℤ)⟩

def logPartial (z : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, z^(i+1)/((i:ℝ)+1)

/-- State is (power,total), initially (z,V(0)); total uses the old power. -/
def loop (z : ℝ) : ℕ → IV × IV :=
  Nat.rec (motive := fun _ => IV × IV) (ofReal z,ofReal 0)
    (fun n s => (mul s.1 (ofReal z),add s.2 (divNat s.1 (n+1))))

def unitLog (x : ℝ) (n : ℕ) : IV :=
  let z := 1-1/x
  let s := loop z n
  let remainder := value s.1.hi / (((n:ℝ)+1)*(1-value (ofReal z).hi))
  ⟨s.2.lo,s.2.hi+(ofReal remainder).hi⟩

/-- Literal ln branch when 1≤x≤2, including the final + k*unit_log(2), k=0. -/
def originalLnUnit (x : ℝ) : IV :=
  add (unitLog x 256) (mul (unitLog 2 256) (ofReal 0))

theorem add_sound {v w : IV} {x y : ℝ}
    (hv : Encloses v x) (hw : Encloses w y) : Encloses (add v w) (x+y) := by
  exact ⟨by simpa [add] using add_le_add hv.1 hw.1,
    by simpa [add] using add_le_add hv.2 hw.2⟩

private theorem floor_div_nat (i : ℤ) (k : ℕ) (hk : 0<k) :
    ⌊(i:ℝ)/(k:ℝ)⌋=i/(k:ℤ) := by
  have hkz : (0:ℤ)≤(k:ℤ) := by positivity
  simpa using Int.floor_div_cast_of_nonneg (k:=ℝ) hkz (i:ℝ)

private theorem rounded_div_lower (i : ℤ) (k : ℕ) (hk : 0<k) :
    value (i/(k:ℤ)) ≤ value i/(k:ℝ) := by
  have h := Int.floor_le ((i:ℝ)/(k:ℝ))
  rw [floor_div_nat i k hk] at h
  calc
    value (i/(k:ℤ)) ≤ ((i:ℝ)/(k:ℝ))/(P160:ℝ) :=
      (div_le_div_iff_of_pos_right P160_real_pos).2 h
    _ = value i/(k:ℝ) := by simp only [value,div_eq_mul_inv]; ring

private theorem rounded_div_upper (i : ℤ) (k : ℕ) (hk : 0<k) :
    value i/(k:ℝ) ≤ value (up i (k:ℤ)) := by
  have h := neg_le_neg (rounded_div_lower (-i) k hk)
  simpa only [up,value,Int.cast_neg,neg_div,neg_neg] using h

theorem divNat_sound {v : IV} {x : ℝ} {k : ℕ}
    (hv : Encloses v x) (hk : 0<k) : Encloses (divNat v k) (x/(k:ℝ)) := by
  have hkr : (0:ℝ)<(k:ℝ) := by exact_mod_cast hk
  exact ⟨(rounded_div_lower v.lo k hk).trans
      ((div_le_div_iff_of_pos_right hkr).2 hv.1),
    ((div_le_div_iff_of_pos_right hkr).2 hv.2).trans
      (rounded_div_upper v.hi k hk)⟩

theorem loop_sound (z : ℝ) (n : ℕ) :
    Encloses (loop z n).1 (z^(n+1)) ∧
    Encloses (loop z n).2 (logPartial z n) := by
  induction n with
  | zero => simpa [loop,logPartial] using And.intro (ofReal_sound z) (ofReal_sound 0)
  | succ n ih =>
    constructor
    · simpa only [loop,pow_succ] using mul_sound ih.1 (ofReal_sound z)
    · have h := add_sound ih.2 (divNat_sound ih.1 (Nat.succ_pos n))
      simpa [loop,logPartial,Finset.sum_range_succ,Nat.cast_add,Nat.cast_one] using h

/-- Exact positive-series remainder, retaining the original factor 1/(n+1).
The pre-existing absolute-remainder lemma alone is too coarse for this. -/
theorem positive_series_bounds {z : ℝ} (hz : 0≤z) (hz1 : z<1) (n : ℕ) :
    logPartial z n ≤ -Real.log (1-z) ∧
    -Real.log (1-z) ≤ logPartial z n + z^(n+1)/(((n:ℝ)+1)*(1-z)) := by
  have habs : |z|<1 := by simpa [abs_of_nonneg hz] using hz1
  have hf := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have ht : HasSum (fun i : ℕ => z^(i+n+1)/(((i+n:ℕ):ℝ)+1))
      (-Real.log (1-z)-logPartial z n) := by
    simpa [logPartial] using (hasSum_nat_add_iff' n).2 hf
  have hg := (hasSum_geometric_of_lt_one hz hz1).mul_left
    (z^(n+1)/((n:ℝ)+1))
  have hpoint (i : ℕ) :
      z^(i+n+1)/(((i+n:ℕ):ℝ)+1) ≤ (z^(n+1)/((n:ℝ)+1))*z^i := by
    calc
      _ ≤ z^(i+n+1)/((n:ℝ)+1) :=
        div_le_div_of_nonneg_left (pow_nonneg hz _) (by positivity)
          (by push_cast; have hi : (0:ℝ)≤(i:ℝ) := Nat.cast_nonneg i; linarith)
      _ = _ := by
        rw [show i+n+1=(n+1)+i by omega,pow_add]
        ring
  have htail := hasSum_le hpoint ht hg
  have halg : (z^(n+1)/((n:ℝ)+1))*(1-z)⁻¹ =
      z^(n+1)/(((n:ℝ)+1)*(1-z)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [halg] at htail
  constructor
  · exact sum_le_hasSum (range n) (fun i _ => div_nonneg (pow_nonneg hz _) (by positivity)) hf
  · linarith

theorem ofReal_hi_mono {x y : ℝ} (h : x≤y) : (ofReal x).hi≤(ofReal y).hi := by
  exact neg_le_neg (Int.floor_mono
    (mul_le_mul_of_nonneg_right (neg_le_neg h) P160_real_pos.le))

/-- The original denominator is positive even after rounding z upward. -/
theorem rounded_z_upper {x : ℝ} (hx1 : 1≤x) (hx2 : x≤2) :
    0≤1-1/x ∧ value (ofReal (1-1/x)).hi≤(1:ℝ)/2 ∧
    (ofReal (1-1/x)).hi<P160 := by
  have hx : 0<x := lt_of_lt_of_le (by norm_num) hx1
  have hinv1 : 1/x≤1 := (div_le_iff₀ hx).2 (by linarith)
  have hinv2 : (1:ℝ)/2≤1/x := (le_div_iff₀ hx).2 (by nlinarith)
  have hhalf : value (ofReal ((1:ℝ)/2)).hi=(1:ℝ)/2 := by
    norm_num [ofReal,value,P160]
  have hu : value (ofReal (1-1/x)).hi≤(1:ℝ)/2 := by
    calc
      _ ≤ value (ofReal ((1:ℝ)/2)).hi := value_mono (ofReal_hi_mono (by linarith))
      _ = _ := hhalf
  refine ⟨by linarith,hu,?_⟩
  have hv : value (ofReal (1-1/x)).hi<value P160 := by rw [value_P160]; linarith
  by_contra h
  exact (not_le_of_gt hv) (value_mono (le_of_not_gt h))

theorem unitLog_sound {x : ℝ} (hx1 : 1≤x) (hx2 : x≤2) (n : ℕ) :
    Encloses (unitLog x n) (Real.log x) := by
  let z := 1-1/x
  let s := loop z n
  let Z := value (ofReal z).hi
  let A := value s.1.hi
  let R := A/(((n:ℝ)+1)*(1-Z))
  have hx : 0<x := lt_of_lt_of_le (by norm_num) hx1
  have hz0 : 0≤z := (rounded_z_upper hx1 hx2).1
  have hZ : Z≤(1:ℝ)/2 := (rounded_z_upper hx1 hx2).2.1
  have hzZ : z≤Z := (ofReal_sound z).2
  have hz1 : z<1 := by linarith
  have hZ1 : Z<1 := by linarith
  have hpow : z^(n+1)≤A := (loop_sound z n).1.2
  have hA : 0≤A := (pow_nonneg hz0 _).trans hpow
  have hn : 0<(n:ℝ)+1 := by positivity
  have hden : 0<((n:ℝ)+1)*(1-Z) := mul_pos hn (by linarith)
  have htail : z^(n+1)/(((n:ℝ)+1)*(1-z))≤R := by
    calc
      _ ≤ A/(((n:ℝ)+1)*(1-z)) :=
        (div_le_div_iff_of_pos_right (mul_pos hn (by linarith))).2 hpow
      _ ≤ A/(((n:ℝ)+1)*(1-Z)) :=
        div_le_div_of_nonneg_left hA hden
          (mul_le_mul_of_nonneg_left (by linarith) hn.le)
  have hlog : -Real.log (1-z)=Real.log x := by
    have heq : 1-z=x⁻¹ := by dsimp [z]; ring
    rw [heq,Real.log_inv,neg_neg]
  have hb := positive_series_bounds hz0 hz1 n
  rw [hlog] at hb
  have htotal : Encloses s.2 (logPartial z n) := (loop_sound z n).2
  have hround : R≤value (ofReal R).hi := (ofReal_sound R).2
  constructor
  · exact htotal.1.trans hb.1
  · change Real.log x ≤ value (s.2.hi+(ofReal R).hi)
    rw [value_add]
    exact hb.2.trans (add_le_add htotal.2 (htail.trans hround))

/-- The final zero multiple in ln is retained and is exactly zero, with no
extra endpoint slack. This equality does not require interval validity. -/
theorem originalLnUnit_eq (x : ℝ) : originalLnUnit x=unitLog x 256 := by
  cases h : unitLog x 256
  simp [originalLnUnit,h,add,mul,fourLo,fourHi,ofReal,up]

theorem original_positive256_ln_sound {x : ℝ} (hx1 : 1≤x) (hx2 : x≤2) :
    Encloses (originalLnUnit x) (Real.log x) := by
  rw [originalLnUnit_eq]
  exact unitLog_sound hx1 hx2 256

/-- The original above-mu symmetric NEW branch supplies these three bounds
from width_xy, mu≤a and upper_rho. Hence its literal Python ln uses this
unit branch: no x<1 recursion and no x>2 range-reduction iteration. -/
theorem original_above_mu_log_sound {a b : ℝ}
    (hab : a<b) (ha : (25:ℝ)/128≤a) (hb : b≤(19:ℝ)/96) :
    Encloses (originalLnUnit (b/a)) (Real.log (b/a)) := by
  have ha0 : 0<a := by linarith
  apply original_positive256_ln_sound
  · exact (le_div_iff₀ ha0).2 (by linarith)
  · exact (div_le_iff₀ ha0).2 (by linarith)

end
end ImbalancedChen.OriginalThirdPositiveLogSourceOnly
