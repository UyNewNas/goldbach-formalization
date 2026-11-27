import ImbalancedChen.ActualThirdOriginalRoundedNewOperations
import ImbalancedChen.P2GuardedReciprocalCore

/-!
# Direct division in the original P160 paired-cell producer

Lines 42–47 of `corpus-renewal-paired-certificate-v2-20261010.py`
(Git blob `ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce`) round each of
the four signed quotients at scale `2^160`. The denominator interval
has a strictly positive lower endpoint.
-/

namespace ImbalancedChen.Certificates.P2OriginalP160DirectDivision

open ImbalancedChen.OriginalThirdClippedChordSourceOnly
open ImbalancedChen.OriginalThirdRoundedNewSourceOnly
open P2DirectedLogRounding

/-- Decode both integers using the same P160 scale as the paired producer. -/
def toEnclosure (x : IV) : Enclosure :=
  ⟨(x.lo : ℚ) / (P160 : ℚ), (x.hi : ℚ) / (P160 : ℚ)⟩

/-- The source takes a minimum of four floors and a maximum of four ceilings.
`up n d` is the integer expression `-((-n) / d)`. -/
def directDiv (x y : IV) : IV :=
  ⟨min (min (x.lo * P160 / y.lo) (x.lo * P160 / y.hi))
       (min (x.hi * P160 / y.lo) (x.hi * P160 / y.hi)),
   max (max (up (x.lo * P160) y.lo) (up (x.lo * P160) y.hi))
       (max (up (x.hi * P160) y.lo) (up (x.hi * P160) y.hi))⟩

private theorem scale_pos : (0 : ℚ) < P160 := by exact_mod_cast P160_pos

private theorem scale_eq : dyadicScale 160 = (P160 : ℚ) :=
  (by norm_num : (2 : ℚ) ^ 160 = ((2 ^ 160 : ℤ) : ℚ))

private theorem scaled_corner (n d : ℤ) (hd : 0 < d) :
    ((n : ℚ) / (P160 : ℚ) * (1 / ((d : ℚ) / (P160 : ℚ)))) * (P160 : ℚ) =
      ((n * P160 : ℤ) : ℚ) / (d : ℚ) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp [scale_pos.ne', hdQ]

private theorem floor_corner (n d : ℤ) (hd : 0 < d) :
    ⌊(n : ℚ) / (d : ℚ)⌋ = n / d := by
  simpa using Int.floor_div_cast_of_nonneg (k := ℚ) hd.le (n : ℚ)

private theorem ceil_corner (n d : ℤ) (hd : 0 < d) :
    ⌈(n : ℚ) / (d : ℚ)⌉ = up n d := by
  have he : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  have heQ : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast he
  have h := Rat.ceil_intCast_div_natCast n d.toNat
  rw [heQ, he] at h
  exact h

private theorem floor_min (a b : ℚ) : ⌊min a b⌋ = min ⌊a⌋ ⌊b⌋ := by
  rcases le_total a b with h | h
  · simp only [min_eq_left h, min_eq_left (Int.floor_mono h)]
  · simp only [min_eq_right h, min_eq_right (Int.floor_mono h)]

private theorem ceil_max (a b : ℚ) : ⌈max a b⌉ = max ⌈a⌉ ⌈b⌉ := by
  rcases le_total a b with h | h
  · simp only [max_eq_right h, max_eq_right (Int.ceil_mono h)]
  · simp only [max_eq_left h, max_eq_left (Int.ceil_mono h)]

/-- Exact rational decoding of both returned integers. The rational division
uses an exact reciprocal and rounds only the completed quotient. -/
theorem directDiv_eq_round160 (x y : IV) (hp : 0 < y.lo) (ho : y.lo ≤ y.hi) :
    toEnclosure (directDiv x y) =
      ((toEnclosure x).divisionBounds (toEnclosure y)).round 160 := by
  have hh := hp.trans_le ho
  apply congrArg₂ Enclosure.mk
  · change ((directDiv x y).lo : ℚ) / (P160 : ℚ) =
      (⌊((toEnclosure x).divisionBounds (toEnclosure y)).lower * dyadicScale 160⌋ : ℚ) /
        dyadicScale 160
    simp only [directDiv, scale_eq, toEnclosure, Enclosure.divisionBounds,
      Enclosure.mul, Enclosure.reciprocalBounds, min_mul_of_nonneg _ _ scale_pos.le,
      floor_min, scaled_corner _ _ hp, scaled_corner _ _ hh,
      floor_corner _ _ hp, floor_corner _ _ hh]
    simp only [min_comm]
  · change ((directDiv x y).hi : ℚ) / (P160 : ℚ) =
      (⌈((toEnclosure x).divisionBounds (toEnclosure y)).upper * dyadicScale 160⌉ : ℚ) /
        dyadicScale 160
    simp only [directDiv, scale_eq, toEnclosure, Enclosure.divisionBounds,
      Enclosure.mul, Enclosure.reciprocalBounds, max_mul_of_nonneg _ _ scale_pos.le,
      ceil_max, scaled_corner _ _ hp, scaled_corner _ _ hh,
      ceil_corner _ _ hp, ceil_corner _ _ hh]
    simp only [max_comm]

private theorem contains_iff (b : IV) (v : ℝ) :
    (toEnclosure b).Contains v ↔ Encloses b v := by
  change (toEnclosure b).Contains v ↔ value b.lo ≤ v ∧ v ≤ value b.hi
  simp only [toEnclosure, Enclosure.Contains, value, Rat.cast_div, Rat.cast_intCast]

/-- A signed numerator and a positive denominator interval suffice for every
real quotient enclosed by these two inputs. -/
theorem directDiv_contains {x y : IV} {v w : ℝ}
    (hx : Encloses x v) (hy : Encloses y w) (hp : 0 < y.lo) :
    Encloses (directDiv x y) (v / w) := by
  have ho : y.lo ≤ y.hi := value_le_iff.mp (hy.1.trans hy.2)
  have valid : (toEnclosure y).ReciprocalValid :=
    ⟨div_le_div_of_nonneg_right (by exact_mod_cast ho) scale_pos.le,
     Or.inl (div_pos (by exact_mod_cast hp) scale_pos)⟩
  have check : (toEnclosure y).reciprocalCheck = true := by
    simpa only [Enclosure.reciprocalCheck, decide_eq_true_eq] using valid
  apply (contains_iff _ _).mp
  rw [directDiv_eq_round160 _ _ hp ho]
  exact Enclosure.round_contains
    (Enclosure.divisionBounds_contains ((contains_iff _ _).mpr hx)
      ((contains_iff _ _).mpr hy) check) 160

end ImbalancedChen.Certificates.P2OriginalP160DirectDivision
