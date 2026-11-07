import ImbalancedChen.P2HistoricQ80DefectLookup

/-!
SOURCE_WRITTEN_UNCOMPILED / code only, 2026-10-24.

Source: certify_conservative_chen.py, SHA256
67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e,
in ../tmp/publication-20261010/verification-renewal-v2/data/.
That hash equals the directly named dependency of the adopted paired-v2
certificate. `I.__truediv__` computes four signed integer floor quotients
and four signed integer ceiling quotients, and asserts other.lo > 0.

Here the integer operation itself is defined literally. Its equality to
the sibling's rational enclosure operation is proved before reusing that
operation's soundness. Thus changing the arithmetic implementation is not
an unproved assumption. The numerator may be negative or cross zero.
-/

namespace ImbalancedChen.Certificates.P2HistoricI80DivisionSoundness

open P2HistoricQ80DefectLookup P2DirectedLogRounding

def ceilDiv (n d : ℤ) : ℤ := -((-n)/d)

def historicalDiv (x y : I80) : I80 :=
  ⟨min (min ((x.lo*(Q:ℤ))/y.lo) ((x.lo*(Q:ℤ))/y.hi))
      (min ((x.hi*(Q:ℤ))/y.lo) ((x.hi*(Q:ℤ))/y.hi)),
   max (max (ceilDiv (x.lo*(Q:ℤ)) y.lo) (ceilDiv (x.lo*(Q:ℤ)) y.hi))
      (max (ceilDiv (x.hi*(Q:ℤ)) y.lo) (ceilDiv (x.hi*(Q:ℤ)) y.hi))⟩

theorem floor_int_div_of_pos (n d : ℤ) (hd : 0 < d) :
    ⌊((n:ℚ)/(d:ℚ))⌋ = n/d := by
  have he : (d.toNat:ℤ) = d := Int.toNat_of_nonneg hd.le
  have heQ : (d.toNat:ℚ) = (d:ℚ) := by exact_mod_cast he
  have h := Rat.floor_intCast_div_natCast n d.toNat
  rw [heQ,he] at h
  exact h

theorem ceil_int_div_of_pos (n d : ℤ) (hd : 0 < d) :
    ⌈((n:ℚ)/(d:ℚ))⌉ = ceilDiv n d := by
  have he : (d.toNat:ℤ) = d := Int.toNat_of_nonneg hd.le
  have heQ : (d.toNat:ℚ) = (d:ℚ) := by exact_mod_cast he
  have h := Rat.ceil_intCast_div_natCast n d.toNat
  rw [heQ,he] at h
  exact h

theorem ceil_max_rat (v w : ℚ) : ⌈max v w⌉ = max ⌈v⌉ ⌈w⌉ := by
  rcases le_total v w with h | h
  · simp only [max_eq_right h, max_eq_right (Int.ceil_mono h)]
  · simp only [max_eq_left h, max_eq_left (Int.ceil_mono h)]

theorem signed_quotient_scaled (n d : ℤ) (hd : d ≠ 0) :
    ((n:ℚ)/Q * (1/((d:ℚ)/Q)))*Q = (((n*(Q:ℤ):ℤ):ℚ)/(d:ℚ)) := by
  have hdQ : (d:ℚ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp [Q_ne_zero,hdQ] <;> ring

/-- Exact historical integer output identity. This is stronger than an
enclosure comparison and retains each intermediate signed floor/ceiling. -/
theorem historicalDiv_eq_I80_div (x y : I80)
    (hpos : 0 < y.lo) (horder : y.lo ≤ y.hi) : historicalDiv x y = x.div y := by
  have hhi : 0 < y.hi := hpos.trans_le horder
  ext
  · simp only [historicalDiv, I80.div, I80.ofEnclosure, I80.enclosure,
      I80.decodeLo, I80.decodeHi, Enclosure.divisionBounds, Enclosure.mul,
      Enclosure.reciprocalBounds, min_mul_of_nonneg _ _ Q_pos.le, floor_min_rat,
      signed_quotient_scaled _ _ (ne_of_gt hpos),
      signed_quotient_scaled _ _ (ne_of_gt hhi),
      floor_int_div_of_pos _ _ hpos, floor_int_div_of_pos _ _ hhi]
    simp only [min_comm]
  · simp only [historicalDiv, I80.div, I80.ofEnclosure, I80.enclosure,
      I80.decodeLo, I80.decodeHi, Enclosure.divisionBounds, Enclosure.mul,
      Enclosure.reciprocalBounds, max_mul_of_nonneg _ _ Q_pos.le, ceil_max_rat,
      signed_quotient_scaled _ _ (ne_of_gt hpos),
      signed_quotient_scaled _ _ (ne_of_gt hhi),
      ceil_int_div_of_pos _ _ hpos, ceil_int_div_of_pos _ _ hhi]
    simp only [max_comm]

/-- The complete signed-numerator propagation theorem. Contains itself
supplies endpoint order; no sign restriction is imposed on v or x.lo. -/
theorem historicalDiv_contains {x y : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w) (hpos : 0 < y.lo) :
    (historicalDiv x y).Contains (v/w) := by
  have horder : y.lo ≤ y.hi := by
    have hq : y.decodeLo ≤ y.decodeHi := by exact_mod_cast (hy.1.trans hy.2)
    have hh := (div_le_div_iff_of_pos_right Q_pos).mp hq
    exact_mod_cast hh
  rw [historicalDiv_eq_I80_div x y hpos horder]
  exact I80.div_contains hx hy hpos

def denominatorCheck (y : I80) : Bool := decide (0 < y.lo)

def checkedHistoricalDiv (x y : I80) : Option I80 :=
  if denominatorCheck y then some (historicalDiv x y) else none

theorem checkedHistoricalDiv_none (x y : I80) (hy : y.lo ≤ 0) :
    checkedHistoricalDiv x y = none := by
  simp [checkedHistoricalDiv,denominatorCheck,not_lt_of_ge hy]

theorem checkedHistoricalDiv_sound {x y z : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w)
    (hresult : checkedHistoricalDiv x y = some z) : z.Contains (v/w) := by
  have hp : 0 < y.lo := by
    by_contra hn
    simp [checkedHistoricalDiv,denominatorCheck,hn] at hresult
  have he : historicalDiv x y = z := by
    simpa [checkedHistoricalDiv,denominatorCheck,hp] using hresult
  rw [←he]
  exact historicalDiv_contains hx hy hp

/-- Exact one-ulp errors relative to the four-corner rational quotient
interval. The analytic interval width is distinct from rounding error. -/
theorem historicalDiv_lower_error (x y : I80)
    (hp : 0 < y.lo) (ho : y.lo ≤ y.hi) :
    0 ≤ (x.enclosure.divisionBounds y.enclosure).lower - (historicalDiv x y).decodeLo ∧
      (x.enclosure.divisionBounds y.enclosure).lower - (historicalDiv x y).decodeLo <
        1/(Q:ℚ) := by
  rw [historicalDiv_eq_I80_div x y hp ho]
  exact I80.lower_rounding _

theorem historicalDiv_upper_error (x y : I80)
    (hp : 0 < y.lo) (ho : y.lo ≤ y.hi) :
    0 ≤ (historicalDiv x y).decodeHi - (x.enclosure.divisionBounds y.enclosure).upper ∧
      (historicalDiv x y).decodeHi - (x.enclosure.divisionBounds y.enclosure).upper <
        1/(Q:ℚ) := by
  rw [historicalDiv_eq_I80_div x y hp ho]
  exact I80.upper_rounding _

def unit : I80 := I80.raw (Q:ℤ)

theorem unit_contains : unit.Contains (1:ℝ) := by
  have h := I80.raw_contains (Q:ℤ)
  simpa [Q_ne_zero] using h

/-- The specialised inverse has the two literal integer endpoint formulas. -/
def historicalReciprocal (y : I80) : I80 :=
  ⟨((Q:ℤ)*(Q:ℤ))/y.hi, ceilDiv ((Q:ℤ)*(Q:ℤ)) y.lo⟩

theorem historicalReciprocal_eq_div (y : I80)
    (hp : 0 < y.lo) (ho : y.lo ≤ y.hi) : historicalReciprocal y = historicalDiv unit y := by
  have hhi : 0 < y.hi := hp.trans_le ho
  have hpQ : (0:ℚ) < (y.lo:ℚ) := by exact_mod_cast hp
  have hoQ : (y.lo:ℚ) ≤ (y.hi:ℚ) := by exact_mod_cast ho
  have hr : (((Q:ℤ)*(Q:ℤ):ℤ):ℚ)/(y.hi:ℚ) ≤
      (((Q:ℤ)*(Q:ℤ):ℤ):ℚ)/(y.lo:ℚ) := by
    apply div_le_div_of_nonneg_left (by positivity) hpQ hoQ
  have hl := Int.floor_mono hr
  have hu := Int.ceil_mono hr
  rw [floor_int_div_of_pos _ _ hhi, floor_int_div_of_pos _ _ hp] at hl
  rw [ceil_int_div_of_pos _ _ hhi, ceil_int_div_of_pos _ _ hp] at hu
  ext <;> simp [historicalReciprocal,historicalDiv,unit,I80.raw,
    min_eq_right hl,max_eq_left hu]

theorem historicalReciprocal_contains {y : I80} {w : ℝ}
    (hy : y.Contains w) (hp : 0 < y.lo) : (historicalReciprocal y).Contains (1/w) := by
  have ho : y.lo ≤ y.hi := by
    have hq : y.decodeLo ≤ y.decodeHi := by exact_mod_cast (hy.1.trans hy.2)
    have hh := (div_le_div_iff_of_pos_right Q_pos).mp hq
    exact_mod_cast hh
  rw [historicalReciprocal_eq_div y hp ho]
  exact historicalDiv_contains unit_contains hy hp

theorem historicalReciprocal_lower_error (y : I80)
    (hp : 0 < y.lo) (ho : y.lo ≤ y.hi) :
    0 ≤ 1/y.decodeHi - (historicalReciprocal y).decodeLo ∧
      1/y.decodeHi - (historicalReciprocal y).decodeLo < 1/(Q:ℚ) := by
  have hhi : 0 < y.hi := hp.trans_le ho
  have hne : (y.hi:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hhi)
  have he : 1/y.decodeHi * Q = (((Q:ℤ)*(Q:ℤ):ℤ):ℚ)/(y.hi:ℚ) := by
    simp only [I80.decodeHi,Int.cast_mul,Int.cast_natCast]
    field_simp [Q_ne_zero,hne] <;> ring
  have h := I80.lower_rounding (⟨1/y.decodeHi,0⟩:Enclosure)
  change 0 ≤ 1/y.decodeHi - (⌊1/y.decodeHi * Q⌋:ℚ)/Q ∧
    1/y.decodeHi - (⌊1/y.decodeHi * Q⌋:ℚ)/Q < 1/(Q:ℚ) at h
  rw [he,floor_int_div_of_pos _ _ hhi] at h
  simpa only [I80.decodeLo,historicalReciprocal] using h

theorem historicalReciprocal_upper_error (y : I80)
    (hp : 0 < y.lo) :
    0 ≤ (historicalReciprocal y).decodeHi - 1/y.decodeLo ∧
      (historicalReciprocal y).decodeHi - 1/y.decodeLo < 1/(Q:ℚ) := by
  have hne : (y.lo:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have he : 1/y.decodeLo * Q = (((Q:ℤ)*(Q:ℤ):ℤ):ℚ)/(y.lo:ℚ) := by
    simp only [I80.decodeLo,Int.cast_mul,Int.cast_natCast]
    field_simp [Q_ne_zero,hne] <;> ring
  have h := I80.upper_rounding (⟨0,1/y.decodeLo⟩:Enclosure)
  change 0 ≤ (⌈1/y.decodeLo * Q⌉:ℚ)/Q - 1/y.decodeLo ∧
    (⌈1/y.decodeLo * Q⌉:ℚ)/Q - 1/y.decodeLo < 1/(Q:ℚ) at h
  rw [he,ceil_int_div_of_pos _ _ hp] at h
  simpa only [I80.decodeHi,historicalReciprocal] using h

/-- Positive rational width is insufficient for a positive rounded lower
integer. The exact condition is at least one complete Q80 ulp. -/
theorem point_lo_pos_iff (q : ℚ) : 0 < (I80.point q).lo ↔ 1/(Q:ℚ) ≤ q := by
  change 0 < ⌊q*Q⌋ ↔ 1/(Q:ℚ) ≤ q
  constructor
  · intro h
    have hi : (1:ℤ) ≤ ⌊q*Q⌋ := by omega
    have hq : (1:ℚ) ≤ q*Q := by simpa using (Int.le_floor.mp hi)
    exact (div_le_iff₀ Q_pos).mpr hq
  · intro h
    have hq : (1:ℚ) ≤ q*Q := (div_le_iff₀ Q_pos).mp h
    have hi : (1:ℤ) ≤ ⌊q*Q⌋ := Int.le_floor.mpr (by simpa using hq)
    omega

theorem point_lo_pos_of_one_ulp_le (q : ℚ) (hq : 1/(Q:ℚ) ≤ q) :
    0 < (I80.point q).lo := (point_lo_pos_iff q).mpr hq

theorem chord_denominator_guard (pl ph : ℚ) (hwidth : 1/(Q:ℚ) ≤ ph-pl) :
    0 < (I80.point (ph-pl)).lo := point_lo_pos_of_one_ulp_le _ hwidth

/-- Exact affine width of an ordinary high-t pair512 parent. No saved
output or numerical producer is used to establish this denominator guard. -/
def ordinaryPair512Width : ℚ :=
  (5/2)*((59/250-25/128)/512) + ((19/125-417/5000)/512)

theorem ordinaryPair512Width_guard : 0 < (I80.point ordinaryPair512Width).lo := by
  apply point_lo_pos_of_one_ulp_le
  norm_num [ordinaryPair512Width,Q]

end ImbalancedChen.Certificates.P2HistoricI80DivisionSoundness
