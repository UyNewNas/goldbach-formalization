import ImbalancedChen.P2GuardedReciprocalRounding
import Mathlib.Data.Rat.Floor

/-!
SOURCE_WRITTEN_UNCOMPILED, 2026-10-24. No evaluator was run.

Literal sources recovered in the sibling publication cache, with SHA256
equal to the bindings in the adopted paired-v2 JSON:
* certify_sharp_184_baseline.py a4ebffaf2b13123cf8d7510fed18482f85ec1a79f1bcddb220bd3d3ec8197639
* certify_conservative_chen.py 67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e
* certify_combined_chen_functional.py 2d33559abaeb08d076a0185952ef7a1697ed1ca0b5beade129aa443a9ac4876b
* certify_extended_prefix.py 1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29

This file transcribes the Q80 interval primitives and the ordinary,
non-enhanced, non-diagonal pair-cell expression used by the saved rows.
The two engine inputs `sf` and `logI` remain explicit: the SieveTable
recurrence and log_point algorithm are NOT silently replaced by true real
functions or by an assumed lower-bound theorem. Integer lookup guards and
the closed-cell indexing convention are proved below. No historical saved
row equality, positive table licence, gain, or count theorem is asserted.
-/

namespace ImbalancedChen.Certificates.P2HistoricQ80DefectLookup

open P2DirectedLogRounding

def Q : ℕ := 2 ^ 80

theorem Q_pos : (0 : ℚ) < Q := by norm_num [Q]
theorem Q_ne_zero : (Q : ℚ) ≠ 0 := ne_of_gt Q_pos

structure I80 where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def I80.decodeLo (x : I80) : ℚ := (x.lo : ℚ) / Q
def I80.decodeHi (x : I80) : ℚ := (x.hi : ℚ) / Q
def I80.enclosure (x : I80) : Enclosure := ⟨x.decodeLo, x.decodeHi⟩
def I80.Contains (x : I80) (v : ℝ) : Prop := x.enclosure.Contains v

/-- Convert exact rational endpoints with precisely one directed Q80 round. -/
def I80.ofEnclosure (x : Enclosure) : I80 :=
  ⟨⌊x.lower * Q⌋, ⌈x.upper * Q⌉⟩

def I80.point (q : ℚ) : I80 := I80.ofEnclosure (Enclosure.point q)
def I80.raw (n : ℤ) : I80 := ⟨n, n⟩
def I80.add (x y : I80) : I80 := ⟨x.lo + y.lo, x.hi + y.hi⟩
def I80.neg (x : I80) : I80 := ⟨-x.hi, -x.lo⟩
def I80.sub (x y : I80) : I80 := x.add y.neg
def I80.mul (x y : I80) : I80 := I80.ofEnclosure (x.enclosure.mul y.enclosure)

/-- The literal producer asserts `0 < y.lo` before this operation.
The formula itself remains total; soundness retains that guard. -/
def I80.div (x y : I80) : I80 :=
  I80.ofEnclosure (x.enclosure.divisionBounds y.enclosure)

theorem I80.enclosure_ofEnclosure (x : Enclosure) :
    (I80.ofEnclosure x).enclosure = x.round 80 := by
  ext <;> simp [I80.ofEnclosure, I80.enclosure, I80.decodeLo, I80.decodeHi,
    Enclosure.round, roundDown, roundUp, dyadicScale, Q]

theorem I80.ofEnclosure_contains {x : Enclosure} {v : ℝ}
    (hx : x.Contains v) : (I80.ofEnclosure x).Contains v := by
  change (I80.ofEnclosure x).enclosure.Contains v
  rw [I80.enclosure_ofEnclosure]
  exact Enclosure.round_contains hx 80

theorem I80.point_contains (q : ℚ) : (I80.point q).Contains q := by
  exact I80.ofEnclosure_contains (Enclosure.point_contains q)

theorem I80.raw_contains (n : ℤ) :
    (I80.raw n).Contains (((n : ℚ) / Q : ℚ) : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem I80.enclosure_add (x y : I80) :
    (x.add y).enclosure = x.enclosure.add y.enclosure := by
  ext <;> simp [I80.enclosure, I80.add, I80.decodeLo, I80.decodeHi,
    Enclosure.add, add_div]

theorem I80.enclosure_neg (x : I80) :
    x.neg.enclosure = x.enclosure.neg := by
  ext <;> simp [I80.enclosure, I80.neg, I80.decodeLo, I80.decodeHi,
    Enclosure.neg]

theorem I80.add_contains {x y : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w) : (x.add y).Contains (v + w) := by
  change (x.add y).enclosure.Contains (v + w)
  rw [I80.enclosure_add]
  exact Enclosure.add_contains hx hy

theorem I80.neg_contains {x : I80} {v : ℝ}
    (hx : x.Contains v) : x.neg.Contains (-v) := by
  change x.neg.enclosure.Contains (-v)
  rw [I80.enclosure_neg]
  exact Enclosure.neg_contains hx

theorem I80.sub_contains {x y : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w) : (x.sub y).Contains (v - w) := by
  simpa only [I80.sub, sub_eq_add_neg] using I80.add_contains hx (I80.neg_contains hy)

theorem I80.mul_contains {x y : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w) : (x.mul y).Contains (v * w) := by
  exact I80.ofEnclosure_contains (Enclosure.mul_contains hx hy)

theorem I80.div_contains {x y : I80} {v w : ℝ}
    (hx : x.Contains v) (hy : y.Contains w) (hpos : 0 < y.lo) :
    (x.div y).Contains (v / w) := by
  have hp : 0 < y.decodeLo := div_pos (by exact_mod_cast hpos) Q_pos
  have hord : y.decodeLo ≤ y.decodeHi := by
    exact_mod_cast (hy.1.trans hy.2)
  have hc : y.enclosure.reciprocalCheck = true := by
    simp [Enclosure.reciprocalCheck, Enclosure.ReciprocalValid,
      I80.enclosure, hord, hp]
  exact I80.ofEnclosure_contains (Enclosure.divisionBounds_contains hx hy hc)

/-- Rational endpoint rounding equals Python's signed integer `//`.
The denominator is positive, so Lean's integer Euclidean division has the
same floor convention for negative numerators too. -/
theorem floor_div_Q (n : ℤ) : ⌊((n : ℚ) / Q)⌋ = n / (Q : ℤ) := by
  exact Rat.floor_intCast_div_natCast n Q

theorem ceil_div_Q (n : ℤ) : ⌈((n : ℚ) / Q)⌉ = -((-n) / (Q : ℤ)) := by
  exact Rat.ceil_intCast_div_natCast n Q

theorem floor_min_rat (v w : ℚ) : ⌊min v w⌋ = min ⌊v⌋ ⌊w⌋ := by
  rcases le_total v w with h | h
  · simp only [min_eq_left h, min_eq_left (Int.floor_mono h)]
  · simp only [min_eq_right h, min_eq_right (Int.floor_mono h)]

/-- Exactly the producer's four signed corner products, followed by
integer `// Q`. This proves an operational identity, not just enclosure. -/
theorem I80.mul_lo_integer (x y : I80) :
    (x.mul y).lo =
      min (min ((x.lo*y.lo)/(Q:ℤ)) ((x.lo*y.hi)/(Q:ℤ)))
        (min ((x.hi*y.lo)/(Q:ℤ)) ((x.hi*y.hi)/(Q:ℤ))) := by
  have he (m n : ℤ) :
      ((m:ℚ)/Q * ((n:ℚ)/Q))*Q = (((m*n:ℤ):ℚ)/Q) := by
    push_cast
    field_simp [Q_ne_zero] <;> ring
  simp only [I80.mul, I80.ofEnclosure, I80.enclosure, I80.decodeLo, I80.decodeHi,
    Enclosure.mul, min_mul_of_nonneg _ _ Q_pos.le, floor_min_rat]
  simp only [he, floor_div_Q]

theorem I80.lower_rounding (x : Enclosure) :
    0 ≤ x.lower - (I80.ofEnclosure x).decodeLo ∧
      x.lower - (I80.ofEnclosure x).decodeLo < 1 / (Q : ℚ) := by
  simpa [I80.ofEnclosure, I80.decodeLo, roundDown, dyadicScale, Q] using
    roundDown_error 80 x.lower

theorem I80.upper_rounding (x : Enclosure) :
    0 ≤ (I80.ofEnclosure x).decodeHi - x.upper ∧
      (I80.ofEnclosure x).decodeHi - x.upper < 1 / (Q : ℚ) := by
  simpa [I80.ofEnclosure, I80.decodeHi, roundUp, dyadicScale, Q] using
    roundUp_error 80 x.upper

def a : ℚ := 417 / 5000

structure Plane where
  c : ℚ
  b : ℚ
  d : ℚ
  deriving DecidableEq, Repr

def Plane.eval (p : Plane) (t u : ℚ) : ℚ := p.c + p.b * t + p.d * u
def Plane.sub (p q : Plane) : Plane := ⟨p.c-q.c, p.b-q.b, p.d-q.d⟩

/-- Exact source `affine_range`, including signed slopes. -/
def affineRange (p : Plane) (tl tr ul ur : ℚ) : ℚ × ℚ :=
  (p.c + p.b * (if 0 ≤ p.b then tl else tr) + p.d * (if 0 ≤ p.d then ul else ur),
   p.c + p.b * (if 0 ≤ p.b then tr else tl) + p.d * (if 0 ≤ p.d then ur else ul))

def ordinaryPlane₀ : Plane := ⟨1/2, -1/2, -1⟩
def ordinaryPlane₁ : Plane := ⟨57/64, -5/2, -1⟩

/-- A source affine is used only when it is the smaller cap on the whole box. -/
def planeAccepted (p q : Plane) (tl tr ul ur : ℚ) : Prop :=
  (affineRange (p.sub q) tl tr ul ur).2 ≤ 0

instance (p q : Plane) (tl tr ul ur : ℚ) :
    Decidable (planeAccepted p q tl tr ul ur) := by
  unfold planeAccepted
  infer_instance

def ordinaryRanges (tl tr ul ur : ℚ) : ℚ × ℚ :=
  let r₀ := affineRange ordinaryPlane₀ tl tr ul ur
  let r₁ := affineRange ordinaryPlane₁ tl tr ul ur
  (min r₀.1 r₁.1, min r₀.2 r₁.2)

/-- Literal non-diagonal logarithmic mass and first moments. -/
def rectangleMass (logI : ℚ → I80) (tl tr ul ur : ℚ) : I80 :=
  (logI (tr/tl)).mul (logI (ur/ul))

def rectangleMomentT (logI : ℚ → I80) (tl tr ul ur : ℚ) : I80 :=
  (I80.point (tr-tl)).mul (logI (ur/ul))

def rectangleMomentU (logI : ℚ → I80) (tl tr ul ur : ℚ) : I80 :=
  (I80.point (ur-ul)).mul (logI (tr/tl))

def ordinaryRectangleBase (sf logI : ℚ → I80)
    (tl tr ul ur rl : ℚ) : I80 :=
  (((sf (rl/a)).mul (rectangleMass logI tl tr ul ur)).mul (I80.point 4)).div (I80.point a)

def ordinaryRectangleChord (sf logI : ℚ → I80)
    (tl tr ul ur : ℚ) (p : Plane) : I80 :=
  let mass := rectangleMass logI tl tr ul ur
  let mt := rectangleMomentT logI tl tr ul ur
  let mu1 := rectangleMomentU logI tl tr ul ur
  let pl := (affineRange p tl tr ul ur).1
  let ph := (affineRange p tl tr ul ur).2
  let mom := (((I80.point p.c).mul mass).add ((I80.point p.b).mul mt)).add
    ((I80.point p.d).mul mu1)
  let val := (((I80.raw (sf (pl/a)).lo).mul (((I80.point ph).mul mass).sub mom)).add
    ((I80.raw (sf (ph/a)).lo).mul (mom.sub ((I80.point pl).mul mass)))).div
    (I80.point (ph-pl))
  (val.mul (I80.point 4)).div (I80.point a)

theorem point_a_lo_pos : 0 < (I80.point a).lo := by
  change 0 < ⌊a * Q⌋
  have h : (1:ℚ) ≤ a * Q := by norm_num [a,Q]
  exact lt_of_lt_of_le (by norm_num) (Int.le_floor.mpr h)

noncomputable def rectangleMassValue (tl tr ul ur : ℚ) : ℝ :=
  Real.log ((tr/tl:ℚ):ℝ) * Real.log ((ur/ul:ℚ):ℝ)

noncomputable def rectangleMomentTValue (tl tr ul ur : ℚ) : ℝ :=
  ((tr-tl:ℚ):ℝ) * Real.log ((ur/ul:ℚ):ℝ)

noncomputable def rectangleMomentUValue (tl tr ul ur : ℚ) : ℝ :=
  ((ur-ul:ℚ):ℝ) * Real.log ((tr/tl:ℚ):ℝ)

theorem rectangleMass_contains (logI : ℚ → I80) (tl tr ul ur : ℚ)
    (ht : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hu : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ))) :
    (rectangleMass logI tl tr ul ur).Contains (rectangleMassValue tl tr ul ur) := by
  exact I80.mul_contains ht hu

theorem rectangleMomentT_contains (logI : ℚ → I80) (tl tr ul ur : ℚ)
    (hu : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ))) :
    (rectangleMomentT logI tl tr ul ur).Contains (rectangleMomentTValue tl tr ul ur) := by
  exact I80.mul_contains (I80.point_contains (tr-tl)) hu

theorem rectangleMomentU_contains (logI : ℚ → I80) (tl tr ul ur : ℚ)
    (ht : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ))) :
    (rectangleMomentU logI tl tr ul ur).Contains (rectangleMomentUValue tl tr ul ur) := by
  exact I80.mul_contains (I80.point_contains (ur-ul)) ht

/-- The backend licences are local query enclosures. No actual integral
bound, final count bound, or saved-output lower theorem occurs here. -/
theorem ordinaryRectangleBase_contains (sf logI : ℚ → I80)
    (tl tr ul ur rl : ℚ) (f : ℝ)
    (hf : (sf (rl/a)).Contains f)
    (ht : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hu : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ))) :
    (ordinaryRectangleBase sf logI tl tr ul ur rl).Contains
      ((f * rectangleMassValue tl tr ul ur * 4) / (a:ℝ)) := by
  simpa only [Rat.cast_ofNat] using I80.div_contains
    (I80.mul_contains (I80.mul_contains hf (rectangleMass_contains logI tl tr ul ur ht hu))
      (I80.point_contains 4))
    (I80.point_contains a) point_a_lo_pos

theorem ordinaryRectangleBase_decodeLo_le (sf logI : ℚ → I80)
    (tl tr ul ur rl : ℚ) (f : ℝ)
    (hf : (sf (rl/a)).Contains f)
    (ht : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hu : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ))) :
    ((ordinaryRectangleBase sf logI tl tr ul ur rl).decodeLo:ℝ) ≤
      (f * rectangleMassValue tl tr ul ur * 4) / (a:ℝ) := by
  exact (ordinaryRectangleBase_contains sf logI tl tr ul ur rl f hf ht hu).1

noncomputable def ordinaryRectangleChordValue (sf : ℚ → I80)
    (tl tr ul ur : ℚ) (p : Plane) : ℝ :=
  let mass := rectangleMassValue tl tr ul ur
  let mt := rectangleMomentTValue tl tr ul ur
  let mu1 := rectangleMomentUValue tl tr ul ur
  let pl := (affineRange p tl tr ul ur).1
  let ph := (affineRange p tl tr ul ur).2
  let mom := ((p.c:ℝ)*mass + (p.b:ℝ)*mt) + (p.d:ℝ)*mu1
  ((((sf (pl/a)).decodeLo:ℝ)*((ph:ℝ)*mass-mom) +
      ((sf (ph/a)).decodeLo:ℝ)*(mom-(pl:ℝ)*mass)) /
    ((ph-pl:ℚ):ℝ) * 4) / (a:ℝ)

/-- Raw endpoint lows are exact numbers here. Their analytic lower-factor
licence belongs to the separate ordinary-table theorem, not this adapter. -/
theorem ordinaryRectangleChord_contains (sf logI : ℚ → I80)
    (tl tr ul ur : ℚ) (p : Plane)
    (ht : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hu : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ)))
    (hden : 0 < (I80.point ((affineRange p tl tr ul ur).2 -
      (affineRange p tl tr ul ur).1)).lo) :
    (ordinaryRectangleChord sf logI tl tr ul ur p).Contains
      (ordinaryRectangleChordValue sf tl tr ul ur p) := by
  have hm := rectangleMass_contains logI tl tr ul ur ht hu
  have hmt := rectangleMomentT_contains logI tl tr ul ur hu
  have hmu := rectangleMomentU_contains logI tl tr ul ur ht
  have hmom := I80.add_contains
    (I80.add_contains (I80.mul_contains (I80.point_contains p.c) hm)
      (I80.mul_contains (I80.point_contains p.b) hmt))
    (I80.mul_contains (I80.point_contains p.d) hmu)
  have hlo := I80.mul_contains
    (I80.raw_contains (sf ((affineRange p tl tr ul ur).1/a)).lo)
    (I80.sub_contains (I80.mul_contains
      (I80.point_contains (affineRange p tl tr ul ur).2) hm) hmom)
  have hhi := I80.mul_contains
    (I80.raw_contains (sf ((affineRange p tl tr ul ur).2/a)).lo)
    (I80.sub_contains hmom (I80.mul_contains
      (I80.point_contains (affineRange p tl tr ul ur).1) hm))
  have hval := I80.div_contains (I80.add_contains hlo hhi)
    (I80.point_contains ((affineRange p tl tr ul ur).2 -
      (affineRange p tl tr ul ur).1)) hden
  simpa only [Rat.cast_ofNat] using I80.div_contains (I80.mul_contains hval (I80.point_contains 4))
    (I80.point_contains a) point_a_lo_pos

theorem ordinaryRectangleChord_decodeLo_le (sf logI : ℚ → I80)
    (tl tr ul ur : ℚ) (p : Plane)
    (ht : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hu : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ)))
    (hden : 0 < (I80.point ((affineRange p tl tr ul ur).2 -
      (affineRange p tl tr ul ur).1)).lo) :
    ((ordinaryRectangleChord sf logI tl tr ul ur p).decodeLo:ℝ) ≤
      ordinaryRectangleChordValue sf tl tr ul ur p := by
  exact (ordinaryRectangleChord_contains sf logI tl tr ul ur p ht hu hden).1

def chordEligible (p q : Plane) (tl tr ul ur : ℚ) : Prop :=
  planeAccepted p q tl tr ul ur ∧
    2*a ≤ (affineRange p tl tr ul ur).1 ∧
    (affineRange p tl tr ul ur).2 ≠ (affineRange p tl tr ul ur).1

instance (p q : Plane) (tl tr ul ur : ℚ) :
    Decidable (chordEligible p q tl tr ul ur) := by
  unfold chordEligible
  infer_instance

/-- Exact two-plane ordinary rectangle branch of source `pair_cell`.
The two sequential maxima commute, but no sum of chords is introduced. -/
def savedOrdinaryRectangle (sf logI : ℚ → I80) (tl tr ul ur : ℚ) : ℤ :=
  let rl := (ordinaryRanges tl tr ul ur).1
  let base := (ordinaryRectangleBase sf logI tl tr ul ur rl).lo
  let best₀ := if chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur then
      max base (ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₀).lo else base
  let best₁ := if chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur then
      max best₀ (ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₁).lo else best₀
  max 0 best₁

theorem savedOrdinaryRectangle_nonneg (sf logI : ℚ → I80) (tl tr ul ur : ℚ) :
    0 ≤ savedOrdinaryRectangle sf logI tl tr ul ur := by
  exact le_max_left _ _

/-! The defect lookup uses rounded integer endpoints, NOT the input real
endpoints. At a knot it includes both adjacent closed cells. -/

def lookupGuard (x : I80) (lower : Bool) : Prop :=
  x.lo < (Q : ℤ) ∨ 5*(Q : ℤ) < x.hi ∨ (lower = true ∧ x.lo < 2*(Q : ℤ))

instance (x : I80) (lower : Bool) : Decidable (lookupGuard x lower) := by
  unfold lookupGuard
  infer_instance

def scaledLo (g : ℕ) (x : I80) : ℚ := ((x.lo : ℚ) - Q) * g / Q
def scaledHi (g : ℕ) (x : I80) : ℚ := ((x.hi : ℚ) - Q) * g / Q
def lookupStart (g : ℕ) (x : I80) : ℤ := max 0 (⌈scaledLo g x⌉ - 1)
def lookupStop (g : ℕ) (x : I80) : ℤ := min (4*(g : ℤ)-1) ⌊scaledHi g x⌋

/-- Nonempty Python slice minimum, expressed without a partial minimum.
The first element is seeded and then repeated, which does not change min. -/
def closedSliceMin (table : ℤ → ℤ) (start stop : ℤ) : ℤ :=
  ((List.range (stop-start+1).toNat).map (fun n => table (start+n))).foldr min (table start)

def defectLookup (g : ℕ) (table : ℤ → ℤ) (x : I80) (lower : Bool) : I80 :=
  if lookupGuard x lower then I80.raw 0 else
    I80.raw (closedSliceMin table (lookupStart g x) (lookupStop g x))

theorem defectLookup_guard (g : ℕ) (table : ℤ → ℤ) (x : I80) (lower : Bool)
    (h : lookupGuard x lower) : defectLookup g table x lower = I80.raw 0 := by
  simp [defectLookup, h]

/-- The lower defect licence is refused when the rounded lower endpoint
is below s=2; an interval crossing that guard gets precisely integer zero. -/
theorem defectLookup_lower_crossing (g : ℕ) (table : ℤ → ℤ) (x : I80)
    (h : x.lo < 2*(Q : ℤ)) : defectLookup g table x true = I80.raw 0 := by
  apply defectLookup_guard
  exact Or.inr (Or.inr ⟨rfl,h⟩)

theorem lookupStart_integer_formula (g : ℕ) (x : I80) :
    lookupStart g x = max 0 (-(-((x.lo-(Q:ℤ))*(g:ℤ)) / (Q:ℤ))-1) := by
  unfold lookupStart scaledLo
  have he : ((x.lo : ℚ) - Q) * g / Q =
      ((((x.lo-(Q:ℤ))*(g:ℤ) : ℤ) : ℚ) / Q) := by push_cast; ring
  rw [he, ceil_div_Q]

theorem lookupStop_integer_formula (g : ℕ) (x : I80) :
    lookupStop g x = min (4*(g:ℤ)-1) (((x.hi-(Q:ℤ))*(g:ℤ)) / (Q:ℤ)) := by
  unfold lookupStop scaledHi
  have he : ((x.hi : ℚ) - Q) * g / Q =
      ((((x.hi-(Q:ℤ))*(g:ℤ) : ℤ) : ℚ) / Q) := by push_cast; ring
  rw [he, floor_div_Q]

/-- Exact closed-cell intersection semantics, including BOTH inequalities
at equality. A floor-only lookup would omit the preceding cell at knots. -/
theorem lookup_indices_iff (g : ℕ) (x : I80) (k : ℤ) :
    lookupStart g x ≤ k ∧ k ≤ lookupStop g x ↔
      0 ≤ k ∧ k ≤ 4*(g:ℤ)-1 ∧
        scaledLo g x ≤ (k:ℚ)+1 ∧ (k:ℚ) ≤ scaledHi g x := by
  rw [lookupStart, lookupStop, max_le_iff, le_min_iff]
  have hceil : ⌈scaledLo g x⌉ - 1 ≤ k ↔ scaledLo g x ≤ (k:ℚ)+1 := by
    rw [sub_le_iff_le_add, Int.ceil_le]
    norm_cast
  rw [hceil, Int.le_floor]
  tauto

/-- A passed guard on an ordered query really selects a nonempty slice.
In particular the `closedSliceMin` seed is an actual selected entry. -/
theorem lookupStart_le_stop (g : ℕ) (x : I80) (lower : Bool)
    (hg : 0 < g) (horder : x.lo ≤ x.hi) (hguard : ¬ lookupGuard x lower) :
    lookupStart g x ≤ lookupStop g x := by
  have hlo : (Q:ℤ) ≤ x.lo := by
    by_contra h
    exact hguard (Or.inl (lt_of_not_ge h))
  have hhi : x.hi ≤ 5*(Q:ℤ) := by
    by_contra h
    exact hguard (Or.inr (Or.inl (lt_of_not_ge h)))
  have hloR : (Q:ℚ) ≤ (x.lo:ℚ) := by exact_mod_cast hlo
  have hhiR : (x.hi:ℚ) ≤ 5*(Q:ℚ) := by exact_mod_cast hhi
  have hordR : (x.lo:ℚ) ≤ (x.hi:ℚ) := by exact_mod_cast horder
  have hgR : (0:ℚ) ≤ g := by positivity
  have hs0 : 0 ≤ scaledHi g x := by
    unfold scaledHi
    exact div_nonneg (mul_nonneg (by linarith) hgR) Q_pos.le
  have hmono : scaledLo g x ≤ scaledHi g x := by
    unfold scaledLo scaledHi
    apply (div_le_div_iff_of_pos_right Q_pos).mpr
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right hordR _) hgR
  have htop : scaledLo g x ≤ (4*g:ℚ) := by
    unfold scaledLo
    apply (div_le_iff₀ Q_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right (hordR.trans hhiR) hgR]
  have hc : ⌈scaledLo g x⌉ ≤ (4*(g:ℤ)) := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using htop
  have hf : (0:ℤ) ≤ ⌊scaledHi g x⌋ := Int.le_floor.mpr (by simpa using hs0)
  have hc' : ⌈scaledLo g x⌉ ≤ ⌊scaledLo g x⌋ + 1 :=
    Int.ceil_le_floor_add_one _
  have hf' : ⌊scaledLo g x⌋ ≤ ⌊scaledHi g x⌋ := Int.floor_mono hmono
  unfold lookupStart lookupStop
  rw [max_le_iff, le_min_iff, le_min_iff]
  constructor <;> constructor <;> omega

/-- On a singleton knot query both adjacent cells are selected. This is
the precise reason for the source's `ceil(...)-1` left endpoint. -/
theorem lookup_knot_both_cells (g : ℕ) (x : I80) (k : ℤ)
    (hk : 1 ≤ k) (hkg : k ≤ 4*(g:ℤ)-1)
    (hl : scaledLo g x = (k:ℚ)) (hu : scaledHi g x = (k:ℚ)) :
    (lookupStart g x ≤ k-1 ∧ k-1 ≤ lookupStop g x) ∧
      (lookupStart g x ≤ k ∧ k ≤ lookupStop g x) := by
  constructor
  · apply (lookup_indices_iff g x (k-1)).mpr
    rw [hl,hu]
    push_cast
    constructor
    · omega
    constructor
    · omega
    constructor <;> linarith
  · apply (lookup_indices_iff g x k).mpr
    rw [hl,hu]
    exact ⟨by omega,hkg,by linarith,le_rfl⟩

theorem foldr_min_le_of_mem (xs : List ℤ) (seed z : ℤ) (hz : z ∈ xs) :
    xs.foldr min seed ≤ z := by
  induction xs with
  | nil => simp at hz
  | cons v xs ih =>
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hz)

theorem le_foldr_min (xs : List ℤ) (seed z : ℤ)
    (hseed : z ≤ seed) (hz : ∀ v ∈ xs, z ≤ v) : z ≤ xs.foldr min seed := by
  induction xs with
  | nil => exact hseed
  | cons v xs ih =>
    exact le_min (hz v (by simp)) (ih (fun w hw => hz w (by simp [hw])))

/-- The finite minimum is below every stored numerator in the closed slice. -/
theorem closedSliceMin_le (table : ℤ → ℤ) (start stop k : ℤ)
    (hk : start ≤ k) (hstop : k ≤ stop) :
    closedSliceMin table start stop ≤ table k := by
  apply foldr_min_le_of_mem
  apply List.mem_map.mpr
  refine ⟨(k-start).toNat, ?_, ?_⟩
  · apply List.mem_range.mpr
    omega
  · congr 1
    omega

/-- Lower bounds for every actual table entry survive the slice minimum;
this is arithmetic only and supplies no analytic table licence. -/
theorem le_closedSliceMin (table : ℤ → ℤ) (start stop z : ℤ)
    (hstart : start ≤ stop) (hz : ∀ k, start ≤ k → k ≤ stop → z ≤ table k) :
    z ≤ closedSliceMin table start stop := by
  apply le_foldr_min
  · exact hz start le_rfl hstart
  · intro v hv
    rcases List.mem_map.mp hv with ⟨n, hn, rfl⟩
    have hn' := List.mem_range.mp hn
    apply hz (start+n) <;> omega

theorem defectLookup_le_closed_cell (g : ℕ) (table : ℤ → ℤ) (x : I80)
    (lower : Bool) (hguard : ¬ lookupGuard x lower) (k : ℤ)
    (hk : 0 ≤ k) (hbound : k ≤ 4*(g:ℤ)-1)
    (hl : scaledLo g x ≤ (k:ℚ)+1) (hu : (k:ℚ) ≤ scaledHi g x) :
    (defectLookup g table x lower).lo ≤ table k := by
  have hindices := (lookup_indices_iff g x k).mpr ⟨hk,hbound,hl,hu⟩
  simpa [defectLookup, hguard, I80.raw] using
    closedSliceMin_le table (lookupStart g x) (lookupStop g x) k hindices.1 hindices.2

/-- Exact saved-cell expression, with the source's separate positive-part
operations on the ordinary proof choice and on the defect contribution. -/
def savedRectangle (sf logI : ℚ → I80) (table : ℤ → ℤ)
    (tl tr ul ur : ℚ) : ℤ :=
  let rr := ordinaryRanges tl tr ul ur
  let hlow := defectLookup 50 table (I80.ofEnclosure ⟨rr.1/a, rr.2/a⟩) true
  let defect := ((((I80.point 4).mul hlow).mul (rectangleMass logI tl tr ul ur)).div
    (I80.point rr.2)).lo
  savedOrdinaryRectangle sf logI tl tr ul ur + max 0 defect

theorem savedRectangle_nonneg (sf logI : ℚ → I80) (table : ℤ → ℤ)
    (tl tr ul ur : ℚ) : 0 ≤ savedRectangle sf logI table tl tr ul ur := by
  apply add_nonneg (savedOrdinaryRectangle_nonneg sf logI tl tr ul ur)
  exact le_max_left _ _

/-- Literal lower-defect bank. The 200 decimal tokens are copied as text
from expanded-w2-midpoint-table248-v1.json, SHA256
 a91c371b8c69398619ebee8b17598c163fbf8b6267fa0470ed6930e2097a98ed.
This is source data, not a proof of the analytic defect-table licence. -/
def bankLowerNumerators : List ℤ := [
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  0, 0, 0, 0, 0,
  37335258798817765329518, 36615797237963045739675, 35910040543614674640701, 35217476338697998875754, 34537620453637509424061,
  33870014893098428913238, 33214225982692190529794, 32569842676863467148818, 31936475011424335597775, 31313752686146776112369,
  30701323764512994200562, 30098853479191678031413, 29506023133088907617859, 28922529086941667301101, 28348081825402301680911,
  27782405094422879317414, 27225235103505500261738, 26676319787051912459486, 26135418119635181575573, 25602299480537684854474,
  25076743063362035951682, 24558537326932146005723, 24047479484066910299681, 23543375025134529284241, 23046037273586032053606,
  22555286970926337659764, 22070951888813788059521, 21592866466187671574266, 21120871469510581020013, 20654813674380923242339,
  20194545566922624710345, 19739925063495910434743, 19290815247396595931174, 18847084121323054747829, 18408604374491168400723,
  17975253163369245068267, 17546911905088092983410, 17123466082657026447385, 16704805061185340515025, 16290821914371401946961,
  15881413260578580316373, 15476479107869328705545, 15075922707416303866007, 14679650414752924735838, 14287571558365593601003,
  13899598315166293135695, 13515645592417736259913, 13135630915713963489937, 12759474322647505152008, 12387098261820179183578,
  12018427496878482502016, 11653389015276538294081, 11291911941489848410693, 10934551841249163903677, 10580611507331804266413,
  10232106097306897024976, 9887693865593967204479, 9549005061993831249626, 9218674250607525864385, 8891360201086868995798,
  8573835988737450520278, 8259159565521782692281, 7955742706261334551100, 7654999158034275981281, 7361225384657490320932,
  7074388411725939674392, 6799689408218069939768, 6527328296913703459134, 6268144232517459130963, 6011129097846547880213,
  5768275717480225163637, 5527421153028410295836, 5301871613096711591929, 5078148405267729638893, 4859593481132235637253,
  4653360418054929598085, 4461285786068314778022, 4270717637289821312308, 4088672654990538344157, 3908033439475565662713,
  3757671334079368540607, 3608452677810103061546, 3463230519244341600382, 3319096177321034305444, 3176033476102797837699,
  3064648229480520238136, 2954078999317280503084, 2844313916124657953348, 2735341367519581089422, 2627149990851971037220,
  2540745919110972694845, 2454952481953311298942, 2369761108962781542839, 2285163408898573519013, 2201151164735299807483,
  2120686719541898561730, 2040771523988084560005, 1961398130534951496907, 1882559242101222098010, 1804247708037549865057,
  1728924955745074763995, 1656480581668694101568, 1586808606203382828331, 1519807261306583315830, 1455378790424128190462,
  1393429259874457722025, 1333868380906223305946, 1276609341707941444172, 1221568648705926078680, 1168665976538934993632,
  1117824026145391384970, 1068968390442188138319, 1022027427113393278445, 976932138063041791167, 933616055118967666631,
  892015131604607277357, 852067639423163417459, 813714071323700757387, 776897048041864023995, 741561230029162662512,
  707653233504322464037, 675121550578220070245, 643916473220528940971, 613990020851539782037, 585295871356786610726,
  557789295335212546152, 531427093403738164479, 506167536392332190601, 481970308274103910828, 458796451684606484586,
  436608315893521537193, 415369507100243639867, 395044840932649090874, 375600297035562830589, 357002975642172297521,
  339221056027915826243, 322223756752230744831, 305981297599014591509, 290464863131761066384, 275646567784107235000,
  261499422410994648505, 247997302229826960472, 235114916084920985649, 222827776972215972807, 211112173764644642893,
  199945144081795379039, 189304448250522686386, 179168544306006352398, 169516563985431262734, 160328289668971229199
]

theorem bankLowerNumerators_length : bankLowerNumerators.length = 200 := by
  norm_num [bankLowerNumerators]

def bankLowerTable (k : ℤ) : ℤ := (bankLowerNumerators[k.toNat]?).getD 0

def bankDefectLookup (x : I80) : I80 := defectLookup 50 bankLowerTable x true

/-- Unlike the `< 2` guard, this uses the actual literal bank and its
closed-cell convention: the preceding cell 49 has numerator zero. -/
theorem bankDefectLookup_exact_s2 :
    bankDefectLookup (I80.raw (2*(Q:ℤ))) = I80.raw 0 := by
  norm_num [bankDefectLookup, defectLookup, lookupGuard, I80.raw,
    lookupStart, lookupStop, scaledLo, scaledHi, closedSliceMin,
    bankLowerTable, bankLowerNumerators, Q]

def sourceSavedRectangle (sf logI : ℚ → I80) (tl tr ul ur : ℚ) : ℤ :=
  savedRectangle sf logI bankLowerTable tl tr ul ur

end ImbalancedChen.Certificates.P2HistoricQ80DefectLookup
