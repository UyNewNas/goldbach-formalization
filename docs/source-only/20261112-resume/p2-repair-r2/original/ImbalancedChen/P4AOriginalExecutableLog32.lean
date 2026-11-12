import ImbalancedChen.ActualThirdOriginalPositive256LogRange32
import Mathlib.Data.Rat.Cast.Order

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Executable rational/integer ABI for the original P160 positive-series ln.
The 256 terms, old-power update, four-corner rounded multiplication,
positive-series remainder, and five range-reduction branches are unchanged.
This is independent of the Q80 atanh32 and paired P160/W224 log96 backends.

The identities are total for every rational argument, including zero and
negative arguments: they identify operation trees, without asserting that
such arguments satisfy the analytic logarithm-enclosure hypotheses.
-/
namespace ImbalancedChen.P4AOriginalExecutableLog32SourceOnly

open OriginalThirdRoundedNewSourceOnly OriginalThirdClippedChordSourceOnly

/-- Computational copy of the original integer scale. -/
def scale : ℤ := 2 ^ 160

def upInt (a b : ℤ) : ℤ := -((-a) / b)

/-- Literal V(F(num,den)): denominator is the positive canonical Rat.den. -/
def ofRat (q : ℚ) : IV :=
  ⟨q.num * scale / (q.den : ℤ), upInt (q.num * scale) (q.den : ℤ)⟩

theorem ofRat_eq_original (q : ℚ) :
    ofRat q = OriginalThirdRoundedNewSourceOnly.ofReal (q : ℝ) := by
  have hcast : (q : ℝ) = (q.num : ℝ) / ((q.den : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using (Rat.cast_def q :
      (q : ℝ) = (q.num : ℝ) / (q.den : ℝ))
  rw [hcast, ofReal_int_div_source q.num (q.den : ℤ)
    (by exact_mod_cast q.den_pos)]
  rfl

def addIV (v w : IV) : IV := ⟨v.lo + w.lo, v.hi + w.hi⟩

def mulIV (v w : IV) : IV :=
  ⟨min (min (v.lo * w.lo) (v.lo * w.hi))
      (min (v.hi * w.lo) (v.hi * w.hi)) / scale,
    upInt (max (max (v.lo * w.lo) (v.lo * w.hi))
      (max (v.hi * w.lo) (v.hi * w.hi))) scale⟩

def divNatIV (v : IV) (n : ℕ) : IV :=
  ⟨v.lo / (n : ℤ), upInt v.hi (n : ℤ)⟩

theorem addIV_eq_original (v w : IV) :
    addIV v w = OriginalThirdPositiveLogSourceOnly.add v w := by rfl

theorem mulIV_eq_original (v w : IV) :
    mulIV v w = OriginalThirdRoundedNewSourceOnly.mul v w := by rfl

theorem divNatIV_eq_original (v : IV) (n : ℕ) :
    divNatIV v n = OriginalThirdPositiveLogSourceOnly.divNat v n := by rfl

/-- The state is (power,total); the sum uses the preceding power. -/
def loop (z : ℚ) : ℕ → IV × IV :=
  Nat.rec (motive := fun _ => IV × IV) (ofRat z, ofRat 0)
    (fun n s => (mulIV s.1 (ofRat z), addIV s.2 (divNatIV s.1 (n + 1))))

theorem loop_eq_original (z : ℚ) (n : ℕ) :
    loop z n = OriginalThirdPositiveLogSourceOnly.loop (z : ℝ) n := by
  induction n with
  | zero =>
    change (ofRat z, ofRat 0) =
      (OriginalThirdRoundedNewSourceOnly.ofReal (z : ℝ),
        OriginalThirdRoundedNewSourceOnly.ofReal 0)
    simp only [ofRat_eq_original, Rat.cast_zero]
  | succ n ih =>
    change (mulIV (loop z n).1 (ofRat z),
      addIV (loop z n).2 (divNatIV (loop z n).1 (n + 1))) =
      (OriginalThirdRoundedNewSourceOnly.mul
        (OriginalThirdPositiveLogSourceOnly.loop (z : ℝ) n).1
        (OriginalThirdRoundedNewSourceOnly.ofReal (z : ℝ)),
      OriginalThirdPositiveLogSourceOnly.add
        (OriginalThirdPositiveLogSourceOnly.loop (z : ℝ) n).2
        (OriginalThirdPositiveLogSourceOnly.divNat
          (OriginalThirdPositiveLogSourceOnly.loop (z : ℝ) n).1 (n + 1)))
    rw [ih, mulIV_eq_original, addIV_eq_original, divNatIV_eq_original,
      ofRat_eq_original]

def decode (z : ℤ) : ℚ := (z : ℚ) / (scale : ℚ)

theorem decode_cast (z : ℤ) : (decode z : ℝ) = value z := by
  simp only [decode, Rat.cast_div, Rat.cast_intCast]
  rfl

/-- Exact rational version of the producer's remainder before V conversion. -/
def remainder (z : ℚ) (s : IV × IV) (n : ℕ) : ℚ :=
  decode s.1.hi / (((n : ℚ) + 1) * (1 - decode (ofRat z).hi))

theorem remainder_cast (z : ℚ) (s : IV × IV) (n : ℕ) :
    (remainder z s n : ℝ) =
      value s.1.hi / (((n : ℝ) + 1) *
        (1 - value (OriginalThirdRoundedNewSourceOnly.ofReal (z : ℝ)).hi)) := by
  simp only [remainder, Rat.cast_div, Rat.cast_mul, Rat.cast_add,
    Rat.cast_sub, Rat.cast_natCast, Rat.cast_one, decode_cast, ofRat_eq_original]

def unitLog (q : ℚ) (n : ℕ) : IV :=
  let z := 1 - 1 / q
  let s := loop z n
  ⟨s.2.lo, s.2.hi + (ofRat (remainder z s n)).hi⟩

theorem unitLog_eq_original (q : ℚ) (n : ℕ) :
    unitLog q n = OriginalThirdPositiveLogSourceOnly.unitLog (q : ℝ) n := by
  simp only [unitLog, OriginalThirdPositiveLogSourceOnly.unitLog,
    ofRat_eq_original, remainder_cast, loop_eq_original,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one]

def logBranch (reduced : ℚ) (k : ℕ) : IV :=
  addIV (unitLog reduced 256) (mulIV (unitLog 2 256) (ofRat (k : ℚ)))

theorem logBranch_eq_original (reduced : ℚ) (k : ℕ) :
    logBranch reduced k =
      OriginalThirdPositiveLogSourceOnly.originalLogBranch (reduced : ℝ) k := by
  simp only [logBranch, OriginalThirdPositiveLogSourceOnly.originalLogBranch,
    addIV_eq_original, mulIV_eq_original, unitLog_eq_original,
    ofRat_eq_original, Rat.cast_natCast, Rat.cast_ofNat]

/-- Original <=2 exit convention, including the final k*unit_log(2). -/
def ln32 (q : ℚ) : IV :=
  if q ≤ 2 then logBranch q 0
  else if q / 2 ≤ 2 then logBranch (q / 2) 1
  else if q / (2 : ℚ) ^ 2 ≤ 2 then logBranch (q / (2 : ℚ) ^ 2) 2
  else if q / (2 : ℚ) ^ 3 ≤ 2 then logBranch (q / (2 : ℚ) ^ 3) 3
  else logBranch (q / (2 : ℚ) ^ 4) 4

theorem ln32_eq_original (q : ℚ) :
    ln32 q = OriginalThirdPositiveLogSourceOnly.originalLn32 (q : ℝ) := by
  have hle (a : ℚ) : ((a : ℝ) ≤ 2) ↔ a ≤ 2 := by
    simpa only [Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ) (p := a) (q := (2 : ℚ)))
  have h1 : ((q : ℝ) / 2 ≤ 2) ↔ q / 2 ≤ 2 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hle (q / 2)
  have h2 : ((q : ℝ) / (2 : ℝ) ^ 2 ≤ 2) ↔ q / (2 : ℚ) ^ 2 ≤ 2 := by
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hle (q / (2 : ℚ) ^ 2)
  have h3 : ((q : ℝ) / (2 : ℝ) ^ 3 ≤ 2) ↔ q / (2 : ℚ) ^ 3 ≤ 2 := by
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hle (q / (2 : ℚ) ^ 3)
  simp only [ln32, OriginalThirdPositiveLogSourceOnly.originalLn32,
    hle q, h1, h2, h3, logBranch_eq_original,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]

end ImbalancedChen.P4AOriginalExecutableLog32SourceOnly
