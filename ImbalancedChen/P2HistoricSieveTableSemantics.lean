import ImbalancedChen.P2HistoricQ80DefectLookup
import ImbalancedChen.P2ContinuousSieveRational
import ImbalancedChen.ActualThirdOriginalLiteralNodes

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

Literal source: certify_extended_prefix.py, SHA256
1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29.
Its Q80 nested-floor trapezoidal recurrence is DIFFERENT from the P112
weighted-chord originalNodeUpdate.  Ordinary(g) uses SieveTable(g,8),
although the imported class's default maximum is 12.  Neither array can
be substituted for the other merely because g=16384.

The integer recurrence, numerator interpolation, point and sf below are
literal total definitions. Signed endpoint divisions, both trapezoid
rounding layers, curvature ceilings, and the factor-division round are
proved conservative. A finite rational Taylor guard independently licenses
actual fbar queries on [2,4]; it has no semantic/table-soundness premise.

NOT A FULL sf LICENCE: full-table induction still needs actual-factor
trapezoid errors 1/(6*g^3),1/(12*g^3). Actual numerator interpolation
at the historical g=16384 is supplied below from proved source curvature.
Existing P112 weighted-chord induction
does not identify this distinct Q80 table. No sf.is_sound, historical
target loss, or target point enclosure is assumed here.
-/

namespace ImbalancedChen.P2HistoricSieveTableSemantics

noncomputable section
open Certificates.P2HistoricQ80DefectLookup
open P2ContinuousSieveRational
open OriginalU2CoupledRecurrenceSourceOnly

def scale : ℤ := 2 ^ 80
def ceilDiv (x d : ℤ) : ℤ := -((-x) / d)
def value (x : ℤ) : ℝ := (x : ℝ) / (scale : ℝ)

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
theorem scale_pos_int : (0 : ℤ) < scale := by norm_num [scale]

/-- The history initializes delayed H nodes down to s=1. Canonical upper
source series is only needed for s>1; the explicit first strip supplies
the continuous endpoint 1 required by the first trapezoid. -/
def endpointUpper (s : ℝ) : ℝ := if s ≤ 3 then 1 / s else upper s
def endpointH (s : ℝ) : ℝ := s * endpointUpper s

theorem endpointUpper_eq_upper {s : ℝ} (hs : 1 < s) : endpointUpper s = upper s := by
  by_cases hs3 : s ≤ 3
  · simp only [endpointUpper, if_pos hs3, upper_eq_inv hs hs3]
  · simp only [endpointUpper, if_neg hs3]

theorem endpointH_eq_H {s : ℝ} (hs : 1 < s) : endpointH s = H s := by
  rw [endpointH, endpointUpper_eq_upper hs]
  rfl

theorem endpointH_initial {s : ℝ} (hs : 1 ≤ s) (hs3 : s ≤ 3) : endpointH s = 1 := by
  have hn : s ≠ 0 := by linarith
  simp [endpointH, endpointUpper, hs3, hn]

structure HistoricNode where
  ll : ℤ
  lh : ℤ
  hl : ℤ
  hh : ℤ
  deriving DecidableEq, Repr

def initial : HistoricNode := ⟨0, 0, scale, scale⟩

def errL (g : ℕ) : ℤ := ceilDiv scale (6 * (g : ℤ) ^ 3)
def errH (g : ℕ) : ℤ := ceilDiv scale (12 * (g : ℤ) ^ 3)
def interpError (g : ℕ) : ℤ := ceilDiv scale (8 * (g : ℤ) ^ 2)

/-- The TWO nested floors, not one floor of the rational trapezoid. -/
def trapLo (g j : ℕ) (x y : ℤ) : ℤ :=
  (x * (g : ℤ) / ((j : ℤ) - 1) + y * (g : ℤ) / (j : ℤ)) / (2 * (g : ℤ))

/-- The TWO inner ceilings and the outer ceiling are all retained. -/
def trapHi (g j : ℕ) (x y : ℤ) : ℤ :=
  ceilDiv (ceilDiv (x * (g : ℤ)) ((j : ℤ) - 1) +
    ceilDiv (y * (g : ℤ)) (j : ℤ)) (2 * (g : ℤ))

def update (g i : ℕ) (old : ℕ → HistoricNode) : HistoricNode :=
  if i ≤ 2 * g then initial else
  let j := i - g
  let p := old (i - 1)
  let llo := trapLo g j (old (j - 1)).hl (old j).hl
  let lhi := trapHi g j (old (j - 1)).hh (old j).hh
  { ll := max p.ll (p.ll + llo - errL g)
    lh := p.lh + lhi
    hl := if i ≤ 3 * g then scale else
      p.hl + trapLo g j (old (j - 1)).ll (old j).ll
    hh := if i ≤ 3 * g then scale else
      p.hh + trapHi g j (old (j - 1)).lh (old j).lh + errH g }

def state (g : ℕ) : ℕ → (ℕ → HistoricNode) :=
  Nat.rec (motive := fun _ => ℕ → HistoricNode) (fun _ => initial)
    (fun k old i => if i = k + 1 then update g (k + 1) old else old i)

def table (g maximum : ℕ) : ℕ → HistoricNode := state g (maximum * g)

def queryIndex (g : ℕ) (a b : ℤ) : ℕ := ((a * (g : ℤ)) / b).toNat
def queryResidual (g : ℕ) (a b : ℤ) : ℤ := (a * (g : ℤ)) % b

def numerator (g : ℕ) (a b : ℤ) (lo hi : ℕ → ℤ) (convex : Bool := false) : I80 :=
  let q := queryIndex g a b
  let r := queryResidual g a b
  if r = 0 then ⟨lo q, hi q⟩ else
  let l := (lo q * (b - r) + lo (q + 1) * r) / b
  let h := ceilDiv (hi q * (b - r) + hi (q + 1) * r) b
  if convex then ⟨l - interpError g, h⟩ else ⟨l, h + interpError g⟩

/-- Exact source point interpreter, including the >maximum monotone tail. -/
def point (g maximum : ℕ) (a b : ℤ) : I80 :=
  if a ≤ 2 * b then ⟨0, 0⟩ else
  if a > (maximum : ℤ) * b then
    ⟨(table g maximum (maximum * g)).ll / (maximum : ℤ),
      ceilDiv (table g maximum (maximum * g)).hh (maximum : ℤ)⟩ else
  let p := numerator g a b (fun i => (table g maximum i).ll)
    (fun i => (table g maximum i).lh)
  ⟨p.lo * b / a, ceilDiv (p.hi * b) a⟩

/-- This is Ordinary.f's raw I80 result; paired-v2 supplies maximum=8. -/
def sf (g maximum : ℕ) (q : ℚ) : I80 := point g maximum q.num (q.den : ℤ)

theorem ordinary_sf (g : ℕ) (q : ℚ) : sf g 8 q = point g 8 q.num (q.den : ℤ) := rfl

theorem value_add (x y : ℤ) : value (x + y) = value x + value y := by
  unfold value
  push_cast
  <;> ring

theorem value_sub (x y : ℤ) : value (x - y) = value x - value y := by
  unfold value
  push_cast
  <;> ring

/-- Q80 scale agrees exactly with the historical interval carrier. -/
theorem I80_contains_iff (p : I80) (x : ℝ) : p.Contains x ↔
    value p.lo ≤ x ∧ x ≤ value p.hi := by
  simp [I80.Contains, I80.enclosure, I80.decodeLo, I80.decodeHi,
    Certificates.P2DirectedLogRounding.Enclosure.Contains, value, scale, Q]

private theorem floor_div_le (x d : ℤ) (hd : 0 < d) :
    ((x / d : ℤ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have he : ⌊(x : ℚ) / (d : ℚ)⌋ = x / d := by
    simpa using Int.floor_div_cast_of_nonneg (k := ℚ) hd.le (x : ℚ)
  have h := Int.floor_le ((x : ℚ) / (d : ℚ))
  rw [he] at h
  exact_mod_cast h

private theorem ceil_div_ge (x d : ℤ) (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) ≤ (ceilDiv x d : ℝ) := by
  simpa only [ceilDiv, Int.cast_neg, neg_div, neg_neg] using
    neg_le_neg (floor_div_le (-x) d hd)

/-- Each floor line is conservative for signed inputs. -/
theorem value_ediv_le (x d : ℤ) (hd : 0 < d) :
    value (x / d) ≤ value x / (d : ℝ) := by
  have h := div_le_div_of_nonneg_right (floor_div_le x d hd) scale_pos.le
  convert h using 1 <;> dsimp [value] <;> ring

/-- Each ceiling line is conservative for signed inputs. -/
theorem value_ceilDiv_ge (x d : ℤ) (hd : 0 < d) :
    value x / (d : ℝ) ≤ value (ceilDiv x d) := by
  have h := div_le_div_of_nonneg_right (ceil_div_ge x d hd) scale_pos.le
  convert h using 1 <;> dsimp [value] <;> ring

theorem value_mul_int (x n : ℤ) : value (x * n) = value x * (n : ℝ) := by
  unfold value
  push_cast
  <;> ring

def realTrap (g j : ℕ) (x y : ℝ) : ℝ :=
  (x * (g : ℝ) / ((j : ℝ) - 1) + y * (g : ℝ) / (j : ℝ)) / (2 * (g : ℝ))

/-- Actual endpoint numerator enclosures transport through every historical
endpoint quotient and both outer trapezoid divisions. No next node occurs. -/
theorem trap_roundline_transport (g j : ℕ) (hg : 0 < g) (hj : 1 < j)
    {ll lh rl rh : ℤ} {x y : ℝ}
    (hx : value ll ≤ x ∧ x ≤ value lh) (hy : value rl ≤ y ∧ y ≤ value rh) :
    value (trapLo g j ll rl) ≤ realTrap g j x y ∧
      realTrap g j x y ≤ value (trapHi g j lh rh) := by
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hjZ : (1 : ℤ) < j := by exact_mod_cast hj
  have hgR : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) ≤ (j : ℤ) - 1 by omega)
  have hj1 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have ho : (0 : ℝ) ≤ 2 * (g : ℝ) := by positivity
  have el0 := value_ediv_le (ll * (g : ℤ)) ((j : ℤ) - 1) (by omega)
  have el1 := value_ediv_le (rl * (g : ℤ)) (j : ℤ) (by omega)
  have eu0 := value_ceilDiv_ge (lh * (g : ℤ)) ((j : ℤ) - 1) (by omega)
  have eu1 := value_ceilDiv_ge (rh * (g : ℤ)) (j : ℤ) (by omega)
  simp only [value_mul_int, Int.cast_sub, Int.cast_one, Int.cast_natCast] at el0 el1 eu0 eu1
  have lx := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx.1 hgR) hj0
  have ly := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hy.1 hgR) hj1
  have ux := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx.2 hgR) hj0
  have uy := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hy.2 hgR) hj1
  constructor
  · have houter := value_ediv_le
      (ll * (g : ℤ) / ((j : ℤ) - 1) + rl * (g : ℤ) / (j : ℤ))
      (2 * (g : ℤ)) (by omega)
    simp only [value_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at houter
    exact houter.trans (div_le_div_of_nonneg_right
      (add_le_add (el0.trans lx) (el1.trans ly)) ho)
  · have houter := value_ceilDiv_ge
      (ceilDiv (lh * (g : ℤ)) ((j : ℤ) - 1) + ceilDiv (rh * (g : ℤ)) (j : ℤ))
      (2 * (g : ℤ)) (by omega)
    simp only [value_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at houter
    exact (div_le_div_of_nonneg_right
      (add_le_add (ux.trans eu0) (uy.trans eu1)) ho).trans houter

/-- The ceiling of Q/den, decoded in Q units, bounds exactly 1/den. -/
theorem reciprocal_error_rounds_up (den : ℤ) (hden : 0 < den) :
    1 / (den : ℝ) ≤ value (ceilDiv scale den) := by
  have h := value_ceilDiv_ge scale den hden
  have hv : value scale = 1 := by
    unfold value
    exact div_self (ne_of_gt scale_pos)
  simpa only [hv] using h

theorem original_error_constants (g : ℕ) (hg : 0 < g) :
    1 / (6 * (g : ℝ) ^ 3) ≤ value (errL g) ∧
    1 / (12 * (g : ℝ) ^ 3) ≤ value (errH g) ∧
    1 / (8 * (g : ℝ) ^ 2) ≤ value (interpError g) := by
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  refine ⟨?_, ?_, ?_⟩
  · simpa [errL] using reciprocal_error_rounds_up (6 * (g : ℤ) ^ 3) (by positivity)
  · simpa [errH] using reciprocal_error_rounds_up (12 * (g : ℤ) ^ 3) (by positivity)
  · simpa [interpError] using reciprocal_error_rounds_up (8 * (g : ℤ) ^ 2) (by positivity)

/-- The scaling relation is a conversion factor, not identity of tables. -/
theorem scale_dictionary : (scale : ℚ) = (originalWeightP : ℚ) / (2 : ℚ) ^ 32 := by
  norm_num [scale, originalWeightP]

/-- The source's global Q80 interpolation allowance is larger than the
actual local numerator curvature error. This reuses analytic geometry,
not P112 array values or the distinct originalNodeUpdate. -/
theorem actual_numerator_interpolation_allowance (i : ℕ) (hi : 32768 ≤ i)
    {s : ℝ} (hs : s ∈ Set.Icc (cellLeft i) (cellRight i)) :
    (0 ≤ L s - endpointChord L (cellLeft i) (cellRight i) s ∧
      L s - endpointChord L (cellLeft i) (cellRight i) s ≤ value (interpError 16384)) ∧
    (0 ≤ endpointChord H (cellLeft i) (cellRight i) s - H s ∧
      endpointChord H (cellLeft i) (cellRight i) s - H s ≤ value (interpError 16384)) := by
  have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hden : (8 * (16384 : ℝ) ^ 2) ≤ 8 * 16384 * ((i : ℝ) - 16384) := by
    nlinarith only [hiR]
  have hrecip := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8 * 16384 ^ 2) hden
  have herr := (original_error_constants 16384 (by norm_num)).2.2
  have hl := original_L_cell_chord i hi hs
  have hu := original_H_cell_chord i hi hs
  exact ⟨⟨hl.1, hl.2.1.trans (hl.2.2.trans (hrecip.trans herr))⟩,
    ⟨hu.1, hu.2.1.trans (hu.2.2.trans (hrecip.trans herr))⟩⟩

def interpolationLo (l0 l1 b r : ℤ) : ℤ := (l0 * (b - r) + l1 * r) / b
def interpolationHi (h0 h1 b r : ℤ) : ℤ := ceilDiv (h0 * (b - r) + h1 * r) b

/-- The numerator interpreter's signed integer residual interpolation
preserves actual endpoint enclosures before curvature is added. -/
theorem interpolation_roundline_transport (b r : ℤ) (hb : 0 < b)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) {l0 h0 l1 h1 : ℤ} {x y : ℝ}
    (hx : value l0 ≤ x ∧ x ≤ value h0) (hy : value l1 ≤ y ∧ y ≤ value h1) :
    value (interpolationLo l0 l1 b r) ≤
        ((b - r : ℤ) : ℝ) / (b : ℝ) * x + (r : ℝ) / (b : ℝ) * y ∧
      ((b - r : ℤ) : ℝ) / (b : ℝ) * x + (r : ℝ) / (b : ℝ) * y ≤
        value (interpolationHi h0 h1 b r) := by
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb.le
  have hrR : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hbrR : (0 : ℝ) ≤ ((b - r : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hrb
  have hl := value_ediv_le (l0 * (b - r) + l1 * r) b hb
  have hu := value_ceilDiv_ge (h0 * (b - r) + h1 * r) b hb
  rw [value_add, value_mul_int, value_mul_int] at hl hu
  have hlo := div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_right hx.1 hbrR)
      (mul_le_mul_of_nonneg_right hy.1 hrR)) hbR
  have hhi := div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_right hx.2 hbrR)
      (mul_le_mul_of_nonneg_right hy.2 hrR)) hbR
  constructor
  · have h := hl.trans hlo
    convert h using 1 <;> dsimp [interpolationLo] <;> ring
  · have h := hhi.trans hu
    convert h using 1 <;> dsimp [interpolationHi] <;> ring

/-- The final source point division by s=a/b is itself conservative,
separately from interpolation and from table-generation semantics. -/
theorem factor_division_rounds (p : I80) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    {v : ℝ} (hp : value p.lo ≤ v ∧ v ≤ value p.hi) :
    value (p.lo * b / a) ≤ v / ((a : ℝ) / (b : ℝ)) ∧
      v / ((a : ℝ) / (b : ℝ)) ≤ value (ceilDiv (p.hi * b) a) := by
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb.le
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
  have hfloor := value_ediv_le (p.lo * b) a ha
  have hceil := value_ceilDiv_ge (p.hi * b) a ha
  rw [value_mul_int] at hfloor hceil
  have hl := hfloor.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp.1 hbR) haR)
  have hu := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp.2 hbR) haR).trans
    hceil
  constructor
  · convert hl using 1 <;> field_simp [ne_of_gt (by exact_mod_cast ha : (0 : ℝ) < a),
      ne_of_gt (by exact_mod_cast hb : (0 : ℝ) < b)] <;> ring
  · convert hu using 1 <;> field_simp [ne_of_gt (by exact_mod_cast ha : (0 : ℝ) < a),
      ne_of_gt (by exact_mod_cast hb : (0 : ℝ) < b)] <;> ring

/-- The zero extension branch is completely licensed for every rational
q<=2, independently of every generated historical table entry. -/
theorem sf_contains_of_le_two (g maximum : ℕ) (q : ℚ) (hq : q ≤ 2) :
    (sf g maximum q).Contains (actualExtendedThirdLowerFactor (q : ℝ)) := by
  have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hqnum : (q.num : ℚ) ≤ 2 * (q.den : ℚ) := by
    apply (div_le_iff₀ hd).1
    simpa only [q.num_div_den] using hq
  have hnum : q.num ≤ 2 * (q.den : ℤ) := by exact_mod_cast hqnum
  have hqR : (q : ℝ) ≤ 2 := by exact_mod_cast hq
  rw [actualExtendedThirdLowerFactor_of_le_two hqR]
  rw [I80_contains_iff]
  simp only [sf, point, if_pos hnum]
  norm_num [value]

/-- Soundness of the source's >maximum tail branch from its TWO earlier
endpoint numerators. The upper endpoint is H, not L. This uses the true
factor monotonicity and true f<=F relation, without assuming a tail query. -/
theorem tail_query_transport (maximum : ℕ) (hmaximum : 2 ≤ maximum)
    {s : ℝ} (hs : (maximum : ℝ) ≤ s) {llo hhi : ℤ}
    (hlo : value llo ≤ L (maximum : ℝ))
    (hHupper : H (maximum : ℝ) ≤ value hhi) :
    (⟨llo / (maximum : ℤ), ceilDiv hhi (maximum : ℤ)⟩ : I80).Contains
      (actualExtendedThirdLowerFactor s) := by
  have hM2 : (2 : ℝ) ≤ (maximum : ℝ) := by exact_mod_cast hmaximum
  have hM0 : (0 : ℤ) < maximum := by exact_mod_cast (show 0 < maximum by omega)
  have hMpos : (0 : ℝ) < (maximum : ℝ) := by linarith
  have hs2 : 2 ≤ s := hM2.trans hs
  have hLdiv : L (maximum : ℝ) / (maximum : ℝ) = lower (maximum : ℝ) := by
    dsimp [L]
    field_simp [ne_of_gt hMpos]
  have hHdiv : H (maximum : ℝ) / (maximum : ℝ) = upper (maximum : ℝ) := by
    dsimp [H]
    field_simp [ne_of_gt hMpos]
  have hl := (value_ediv_le llo (maximum : ℤ) hM0).trans
    (div_le_div_of_nonneg_right hlo hMpos.le)
  have hu := (div_le_div_of_nonneg_right hHupper hMpos.le).trans
    (value_ceilDiv_ge hhi (maximum : ℤ) hM0)
  simp only [Int.cast_natCast, hLdiv, hHdiv] at hl hu
  rw [I80_contains_iff, ← lower_eq_actual hs2]
  exact ⟨hl.trans (lower_monotone hM2 hs2 hs),
    (lower_le_upper hs2).trans ((upper_antitone hM2 hs2 hs).trans hu)⟩

/-- A real-source analytic guard, computed entirely with rational Taylor
expressions and exact source sf integers. It is stronger than Contains,
and contains no actual function or integral. -/
def firstStripGuard (terms g maximum : ℕ) (q : ℚ) : Bool := decide
  ((sf g maximum q).decodeLo ≤ logLower terms q / q ∧
    logUpper terms q / q ≤ (sf g maximum q).decodeHi)

/-- A successful rational first-strip guard licenses the literal historical
sf output against actual normalized fbar, without assuming a sound table. -/
theorem sf_contains_of_firstStripGuard (terms g maximum : ℕ) (q : ℚ)
    (hq2 : 2 ≤ q) (hq4 : q ≤ 4)
    (hcheck : firstStripGuard terms g maximum q = true) :
    (sf g maximum q).Contains (actualExtendedThirdLowerFactor (q : ℝ)) := by
  have hg : (sf g maximum q).decodeLo ≤ logLower terms q / q ∧
      logUpper terms q / q ≤ (sf g maximum q).decodeHi := of_decide_eq_true hcheck
  obtain ⟨hl, hu⟩ := lower_rational_node_bounds terms q hq2 hq4
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have he := lower_eq_actual hq2R
  rw [he] at hl hu
  have hgl : ((sf g maximum q).decodeLo : ℝ) ≤ ((logLower terms q / q : ℚ) : ℝ) := by
    exact_mod_cast hg.1
  have hgu : ((logUpper terms q / q : ℚ) : ℝ) ≤ ((sf g maximum q).decodeHi : ℝ) := by
    exact_mod_cast hg.2
  exact ⟨hgl.trans hl, hu.trans hgu⟩

end

end ImbalancedChen.P2HistoricSieveTableSemantics
