import ImbalancedChen.Part5OriginalOmegaGridCoreModular
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
SOURCE ONLY / UNCOMPILED.  No Lean/lake/evaluator/numerical replay was run.

This supplies polynomial, rather than rectangle, method-of-steps semantics
for the actual pinned Buchstab function.  Exact rational antiderivatives are
interpreted by FTC; the analytic comparison uses the actual rebased Buchstab
integral equation.  Whole-cell slope inequalities are licensed by finite
rational/integer Bernstein checks, reusing the existing integer Bernstein
soundness theorem from `Part5OriginalOmegaGridCore`'s dependency.

The existing `OriginalOmegaGrid22034To22066` already proves its 32 cell caps.
No such cell, coefficient row, or coordinate datum is repeated here.  The new
object is a general polynomial propagation step and a small independent
`[2,3]` instance from the literal initial condition on `[1,2]`.

The prior envelope is required only on `[a-1,b-1]`, and the finite condition
`b <= a+1` proves that this entire delayed interval lies at or before `a`.
It never assumes an enclosure on the interior of its target cell.  Producing
sharp polynomial certificates for the remaining original grid is still open;
the generic semantic theorem is not a receipt for any unwritten table.
-/

namespace ImbalancedChen.Certificates.P2BuchstabPolynomialStep

open Set MeasureTheory LiLiuPrereqBuchstab
open SavedParent394700ActualBuchstabSourceOnly
open scoped Interval

/- All polynomial and certificate data before the real semantic section are
   ordinary executable Lists, rationals, integers, and finite arithmetic. -/

def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => (x + y) :: add p q

def scale (c : ℚ) (p : List ℚ) : List ℚ := p.map (fun x => c * x)

def sub (p q : List ℚ) : List ℚ := add p (scale (-1) q)

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: p, q => add (scale x q) (0 :: mul p q)

def delay : List ℚ → List ℚ
  | [] => []
  | x :: p => add [x] (mul [-1, 1] (delay p))

def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | x :: p, t => x + t * evalQ p t

def derivativeFrom : ℕ → List ℚ → List ℚ
  | _, [] => []
  | n, x :: p => ((n : ℚ) * x) :: derivativeFrom (n + 1) p

def derivative (p : List ℚ) : List ℚ := derivativeFrom 1 p.tail

def primitiveFrom : ℕ → List ℚ → List ℚ
  | _, [] => []
  | n, x :: p => (x / ((n : ℚ) + 1)) :: primitiveFrom (n + 1) p

def primitive (p : List ℚ) : List ℚ := 0 :: primitiveFrom 0 p

/-- The exact rational polynomial `h + integral_a^x p`. -/
def integrated (a h : ℚ) (p : List ℚ) : List ℚ :=
  add [h - evalQ (primitive p) a] (primitive p)

/-- An integer Bernstein proof of nonnegativity for a rational polynomial.
`Q` clears rational coefficients; `M` is the existing Bernstein multiplier. -/
structure NonnegativeCertificate where
  Q : ℤ
  coefficients : List ℤ
  degree : ℕ
  M : ℤ
  A : ℤ
  B : ℤ
  D : ℤ
  bernstein : List ℤ
  deriving DecidableEq, Repr

def NonnegativeCertificate.Valid (c : NonnegativeCertificate)
    (p : List ℚ) (lo hi : ℚ) : Prop :=
  0 < c.Q ∧ 0 < c.M ∧ 0 < c.D ∧ 0 < c.B ∧
    p = c.coefficients.map (fun z => (z : ℚ) / (c.Q : ℚ)) ∧
    positiveList c.bernstein = true ∧
    absSum (addList
      (scaleList c.M (homogeneousAffine c.A c.B c.D c.coefficients))
      (scaleList (-1) (bernsteinSumFrom c.degree 0 c.bernstein))) = 0 ∧
    (c.A : ℚ) / (c.D : ℚ) ≤ lo ∧ hi ≤ ((c.A : ℚ) + c.B) / (c.D : ℚ)

instance (c : NonnegativeCertificate) (p : List ℚ) (lo hi : ℚ) :
    Decidable (c.Valid p lo hi) := by
  unfold NonnegativeCertificate.Valid
  infer_instance

def NonnegativeCertificate.check (c : NonnegativeCertificate)
    (p : List ℚ) (lo hi : ℚ) : Bool := decide (c.Valid p lo hi)

structure Step where
  a : ℚ
  b : ℚ
  anchorLower : ℚ
  anchorUpper : ℚ
  priorLower : List ℚ
  priorUpper : List ℚ
  slopeLower : List ℚ
  slopeUpper : List ℚ
  lowerCertificate : NonnegativeCertificate
  upperCertificate : NonnegativeCertificate
  deriving DecidableEq, Repr

def Step.lowerResidual (c : Step) : List ℚ :=
  sub (delay c.priorLower) (mul [-1, 1] c.slopeLower)

def Step.upperResidual (c : Step) : List ℚ :=
  sub (mul [-1, 1] c.slopeUpper) (delay c.priorUpper)

def Step.lowerEnvelope (c : Step) : List ℚ :=
  integrated c.a c.anchorLower c.slopeLower

def Step.upperEnvelope (c : Step) : List ℚ :=
  integrated c.a c.anchorUpper c.slopeUpper

def Step.Valid (c : Step) : Prop :=
  2 ≤ c.a ∧ c.a < c.b ∧ c.b ≤ c.a + 1 ∧
    c.lowerCertificate.check c.lowerResidual c.a c.b = true ∧
    c.upperCertificate.check c.upperResidual c.a c.b = true

instance (c : Step) : Decidable c.Valid := by
  unfold Step.Valid
  infer_instance

def Step.check (c : Step) : Bool := decide c.Valid

noncomputable section

def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | x :: p, t => (x : ℝ) + t * eval p t

def H (s : ℝ) : ℝ := s * buchstab s

theorem eval_add (p q : List ℚ) (t : ℝ) :
    eval (add p q) t = eval p t + eval q t := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons x p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons y q => simp only [add, eval, ih, Rat.cast_add]; ring

theorem eval_scale (c : ℚ) (p : List ℚ) (t : ℝ) :
    eval (scale c p) t = (c : ℝ) * eval p t := by
  induction p with
  | nil => simp [scale, eval]
  | cons x p ih =>
      change (((c * x : ℚ) : ℝ) + t * eval (scale c p) t) =
        (c : ℝ) * ((x : ℝ) + t * eval p t)
      rw [ih, Rat.cast_mul]
      ring

theorem eval_sub (p q : List ℚ) (t : ℝ) :
    eval (sub p q) t = eval p t - eval q t := by
  rw [sub, eval_add, eval_scale]
  norm_num

theorem eval_mul (p q : List ℚ) (t : ℝ) :
    eval (mul p q) t = eval p t * eval q t := by
  induction p with
  | nil => simp [mul, eval]
  | cons x p ih =>
      rw [mul, eval_add, eval_scale]
      simp only [eval, Rat.cast_zero, zero_add, ih]
      ring

theorem eval_delay (p : List ℚ) (t : ℝ) : eval (delay p) t = eval p (t - 1) := by
  induction p with
  | nil => simp [delay, eval]
  | cons x p ih =>
      rw [delay, eval_add, eval_mul, ih]
      simp only [eval, Rat.cast_one, Rat.cast_neg, mul_zero, add_zero]
      ring

theorem eval_cast (p : List ℚ) (t : ℚ) : eval p t = (evalQ p t : ℝ) := by
  induction p with
  | nil => simp [eval, evalQ]
  | cons x p ih => simp only [eval, evalQ, Rat.cast_add, Rat.cast_mul, ih]

theorem eval_continuous (p : List ℚ) : Continuous (eval p) := by
  induction p with
  | nil => exact continuous_const
  | cons x p ih => exact continuous_const.add (continuous_id.mul ih)

private theorem eval_derivativeFrom (p : List ℚ) (t : ℝ) (n : ℕ) :
    eval (derivativeFrom n p) t =
      (n : ℝ) * eval p t + t * eval (derivative p) t := by
  induction p generalizing n with
  | nil => simp [derivativeFrom, derivative, eval]
  | cons x p ih =>
      change ((((n : ℚ) * x : ℚ) : ℝ) +
        t * eval (derivativeFrom (n + 1) p) t) =
          (n : ℝ) * ((x : ℝ) + t * eval p t) + t * eval (derivativeFrom 1 p) t
      rw [ih (n + 1), ih 1]
      push_cast
      ring

theorem hasDerivAt_eval (p : List ℚ) (t : ℝ) :
    HasDerivAt (eval p) (eval (derivative p) t) t := by
  induction p with
  | nil => simpa [eval, derivative, derivativeFrom] using hasDerivAt_const t (0 : ℝ)
  | cons x p ih =>
      have h := (hasDerivAt_const t (x : ℝ)).add ((hasDerivAt_id t).mul ih)
      change HasDerivAt (fun y : ℝ => (x : ℝ) + y * eval p y)
        (eval (derivativeFrom 1 p) t) t
      convert! h using 1
      simpa only [Nat.cast_one, zero_add, one_mul] using eval_derivativeFrom p t 1

private theorem derivativeFrom_primitiveFrom (p : List ℚ) (n : ℕ) :
    derivativeFrom (n + 1) (primitiveFrom n p) = p := by
  induction p generalizing n with
  | nil => rfl
  | cons x p ih =>
      have hn : (n : ℚ) + 1 ≠ 0 := by positivity
      simp only [primitiveFrom, derivativeFrom, ih, Nat.cast_add, Nat.cast_one]
      congr 1
      field_simp [hn] <;> ring

theorem derivative_primitive (p : List ℚ) : derivative (primitive p) = p := by
  simpa only [derivative, primitive, List.tail_cons] using derivativeFrom_primitiveFrom p 0

/-- Exact polynomial integration, proved with the actual real FTC. -/
theorem integral_eval (p : List ℚ) (a b : ℝ) :
    (∫ t in a..b, eval p t) = eval (primitive p) b - eval (primitive p) a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    simpa only [derivative_primitive] using hasDerivAt_eval (primitive p) t
  · exact (eval_continuous p).intervalIntegrable a b

theorem eval_integrated (a h : ℚ) (p : List ℚ) (s : ℝ) :
    eval (integrated a h p) s = (h : ℝ) + ∫ t in (a : ℝ)..s, eval p t := by
  rw [integrated, eval_add, integral_eval]
  simp only [eval, mul_zero, add_zero, Rat.cast_sub, ← eval_cast]
  ring

private theorem eval_integer_lift (zs : List ℤ) (Q : ℤ) (t : ℝ) :
    eval (zs.map (fun z => (z : ℚ) / (Q : ℚ))) t = evalList zs t / (Q : ℝ) := by
  induction zs with
  | nil => simp [eval, evalList]
  | cons z zs ih =>
      simp only [List.map_cons, eval, evalList, Rat.cast_div, Rat.cast_intCast, ih]
      ring

/-- Rational coefficient identities and integer Bernstein checks license
the whole closed real interval; no point sampling is involved. -/
theorem NonnegativeCertificate.check_sound (c : NonnegativeCertificate)
    (p : List ℚ) (lo hi : ℚ) (hc : c.check p lo hi = true)
    {t : ℝ} (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) : 0 ≤ eval p t := by
  have hv : c.Valid p lo hi := of_decide_eq_true hc
  rcases hv with ⟨hQ, hM, hD, hB, hp, hb, hid, hlo, hhi⟩
  have hloR : (c.A : ℝ) / (c.D : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (hi : ℝ) ≤ ((c.A : ℝ) + c.B) / (c.D : ℝ) := by exact_mod_cast hhi
  have h := integer_Bernstein_certificate_on_interval c.degree c.M c.A c.B c.D
    c.coefficients c.bernstein hM hD hB hb hid ⟨hloR.trans ht.1, ht.2.trans hhiR⟩
  rw [hp, eval_integer_lift]
  exact div_nonneg h (by exact_mod_cast hQ.le)

/-- The delayed interval cannot include a point in the current cell's
interior.  Its right endpoint is at or before the known anchor. -/
theorem Step.delay_owned (c : Step) (hc : c.check = true) {y : ℝ}
    (hy : y ∈ Icc ((c.a : ℝ) - 1) ((c.b : ℝ) - 1)) : y ≤ (c.a : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hc
  have hb : (c.b : ℝ) ≤ (c.a : ℝ) + 1 := by exact_mod_cast hv.2.2.1
  linarith [hy.2]

/-- Actual-function polynomial propagation.  The only analytic inputs
are the already owned delayed interval and the single known anchor. -/
theorem Step.check_sound (c : Step) (hc : c.check = true)
    (hanchor : (c.anchorLower : ℝ) ≤ H c.a ∧ H c.a ≤ (c.anchorUpper : ℝ))
    (hprior : ∀ y ∈ Icc ((c.a : ℝ) - 1) ((c.b : ℝ) - 1),
      eval c.priorLower y ≤ H y ∧ H y ≤ eval c.priorUpper y)
    {s : ℝ} (hs : s ∈ Icc (c.a : ℝ) (c.b : ℝ)) :
    eval c.lowerEnvelope s ≤ H s ∧ H s ≤ eval c.upperEnvelope s := by
  have hv : c.Valid := of_decide_eq_true hc
  rcases hv with ⟨ha, hab, hdelay, hlowcheck, hhighcheck⟩
  have haR : (2 : ℝ) ≤ (c.a : ℝ) := by exact_mod_cast ha
  have habR : (c.a : ℝ) ≤ s := hs.1
  have hpoint : ∀ t ∈ Icc (c.a : ℝ) s,
      eval c.slopeLower t ≤ buchstab (t - 1) ∧
        buchstab (t - 1) ≤ eval c.slopeUpper t := by
    intro t ht
    have htcell : t ∈ Icc (c.a : ℝ) (c.b : ℝ) := ⟨ht.1, ht.2.trans hs.2⟩
    have htdelay : t - 1 ∈ Icc ((c.a : ℝ) - 1) ((c.b : ℝ) - 1) := by
      constructor <;> linarith [htcell.1, htcell.2]
    have hp := hprior (t - 1) htdelay
    have hlo := c.lowerCertificate.check_sound c.lowerResidual c.a c.b hlowcheck htcell
    have hhi := c.upperCertificate.check_sound c.upperResidual c.a c.b hhighcheck htcell
    simp only [Step.lowerResidual, Step.upperResidual, eval_sub, eval_delay, eval_mul,
      eval, Rat.cast_neg, Rat.cast_one, mul_zero, add_zero] at hlo hhi
    have htpos : 0 < t - 1 := by linarith [ht.1]
    constructor
    · apply (mul_le_mul_iff_left₀ htpos).mp
      dsimp only [H] at hp
      nlinarith only [hlo, hp.1]
    · apply (mul_le_mul_iff_left₀ htpos).mp
      dsimp only [H] at hp
      nlinarith only [hhi, hp.2]
  have hbc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hloInt := intervalIntegral.integral_mono_on habR
    ((eval_continuous c.slopeLower).intervalIntegrable c.a s)
    (hbc.intervalIntegrable c.a s) (fun t ht => (hpoint t ht).1)
  have hhiInt := intervalIntegral.integral_mono_on habR
    (hbc.intervalIntegrable c.a s)
    ((eval_continuous c.slopeUpper).intervalIntegrable c.a s)
    (fun t ht => (hpoint t ht).2)
  have he := buchstab_weighted_sub_eq_integral (a := (c.a : ℝ)) haR habR
  rw [Step.lowerEnvelope, Step.upperEnvelope, eval_integrated, eval_integrated]
  dsimp only [H] at hanchor ⊢
  constructor <;> linarith only [hanchor.1, hanchor.2, hloInt, hhiInt, he]

/-- The endpoint output is an exact rational enclosure for the actual H.
It can be used as the next cell's known anchor. -/
theorem Step.endpoint_sound (c : Step) (hc : c.check = true)
    (hanchor : (c.anchorLower : ℝ) ≤ H c.a ∧ H c.a ≤ (c.anchorUpper : ℝ))
    (hprior : ∀ y ∈ Icc ((c.a : ℝ) - 1) ((c.b : ℝ) - 1),
      eval c.priorLower y ≤ H y ∧ H y ≤ eval c.priorUpper y) :
    (evalQ c.lowerEnvelope c.b : ℝ) ≤ H c.b ∧
      H c.b ≤ (evalQ c.upperEnvelope c.b : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hc
  have hab : (c.a : ℝ) ≤ (c.b : ℝ) := by exact_mod_cast hv.2.1.le
  simpa only [eval_cast] using c.check_sound hc hanchor hprior ⟨hab, le_rfl⟩

/-- A checked polynomial whole-cell barrier produces the same upper-bound
interface as the original omega grid, with its normalization explicit. -/
theorem Step.omega_cap_sound (c : Step) (hc : c.check = true)
    (hanchor : (c.anchorLower : ℝ) ≤ H c.a ∧ H c.a ≤ (c.anchorUpper : ℝ))
    (hprior : ∀ y ∈ Icc ((c.a : ℝ) - 1) ((c.b : ℝ) - 1),
      eval c.priorLower y ≤ H y ∧ H y ≤ eval c.priorUpper y)
    (S num : ℚ) (hS : 0 < S) (barrier : NonnegativeCertificate)
    (hbarrier : barrier.check (sub [0, num] (scale S c.upperEnvelope)) c.a c.b = true)
    {s : ℝ} (hs : s ∈ Icc (c.a : ℝ) (c.b : ℝ)) :
    buchstab s ≤ (num : ℝ) / (S : ℝ) := by
  have hu := (c.check_sound hc hanchor hprior hs).2
  have hb := barrier.check_sound (sub [0, num] (scale S c.upperEnvelope))
    c.a c.b hbarrier hs
  simp only [eval_sub, eval_scale, eval, Rat.cast_zero, mul_zero, add_zero] at hb
  have hv : c.Valid := of_decide_eq_true hc
  have ha : (2 : ℝ) ≤ (c.a : ℝ) := by exact_mod_cast hv.1
  have hs₀ : 0 < s := by linarith [hs.1]
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hmul := mul_le_mul_of_nonneg_left hu hSR.le
  apply (le_div_iff₀ hSR).mpr
  apply (mul_le_mul_iff_left₀ hs₀).mp
  dsimp only [H] at hmul
  nlinarith only [hmul, hb]

/-- Literal `2^80` normalization used by the original grid suppliers. -/
theorem Step.omega_cap_original_scale (c : Step) (hc : c.check = true)
    (hanchor : (c.anchorLower : ℝ) ≤ H c.a ∧ H c.a ≤ (c.anchorUpper : ℝ))
    (hprior : ∀ y ∈ Icc ((c.a : ℝ) - 1) ((c.b : ℝ) - 1),
      eval c.priorLower y ≤ H y ∧ H y ≤ eval c.priorUpper y)
    (num : ℤ) (barrier : NonnegativeCertificate)
    (hbarrier : barrier.check
      (sub [0, (num : ℚ)] (scale ((2 : ℚ) ^ 80) c.upperEnvelope)) c.a c.b = true)
    {s : ℝ} (hs : s ∈ Icc (c.a : ℝ) (c.b : ℝ)) :
    buchstab s ≤ (num : ℝ) / (2 : ℝ) ^ 80 := by
  have h := c.omega_cap_sound hc hanchor hprior ((2 : ℚ) ^ 80) (num : ℚ)
    (by positivity) barrier hbarrier hs
  simpa only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast] using h

end

/- A concrete first branch.  Both Bernstein residual checks are quadratic
   identities on [2,3].  Their lists concern no original P5 grid cell. -/

def firstLowerCertificate : NonnegativeCertificate where
  Q := 20
  coefficients := [44, -29, 5]
  degree := 2
  M := 2
  A := 2
  B := 1
  D := 1
  bernstein := [12, 3, 4]

def firstUpperCertificate : NonnegativeCertificate where
  Q := 20
  coefficients := [-61, 51, -10]
  degree := 2
  M := 2
  A := 2
  B := 1
  D := 1
  bernstein := [2, 13, 4]

def firstStep : Step where
  a := 2
  b := 3
  anchorLower := 1
  anchorUpper := 1
  priorLower := [1]
  priorUpper := [1]
  slopeLower := [6 / 5, -1 / 4]
  slopeUpper := [41 / 20, -1 / 2]
  lowerCertificate := firstLowerCertificate
  upperCertificate := firstUpperCertificate

theorem firstStep_checked : firstStep.check = true := by decide

noncomputable section

private theorem initial_H {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) : H s = 1 := by
  rw [H, buchstab_eq_one_div hs.1 hs.2]
  have hs₀ : s ≠ 0 := by linarith [hs.1]
  field_simp [hs₀]

/-- The first polynomial branch is supplied by the actual initial
condition; no prior numerical omega table occurs among its premises. -/
theorem firstStep_sound {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    eval firstStep.lowerEnvelope s ≤ H s ∧ H s ≤ eval firstStep.upperEnvelope s := by
  apply firstStep.check_sound firstStep_checked
  · have he := initial_H (s := 2) (by norm_num)
    norm_num [firstStep, he]
  · intro y hy
    have hy' : y ∈ Icc (1 : ℝ) 2 := by norm_num [firstStep] at hy ⊢; exact hy
    have he := initial_H hy'
    norm_num [firstStep, eval, he]
  · simpa only [firstStep, Rat.cast_ofNat] using hs

/-- Exact rational H endpoint obtained by integrating nonconstant
polynomials, ready to serve as an anchor for a following step. -/
theorem firstStep_endpoint : (63 : ℝ) / 40 ≤ H 3 ∧ H 3 ≤ (9 : ℝ) / 5 := by
  have h := firstStep_sound (s := 3) (by norm_num)
  norm_num [Step.lowerEnvelope, Step.upperEnvelope, firstStep, integrated,
    primitive, primitiveFrom, evalQ, add, eval] at h
  exact h

/-- The full original first branch, with explicit polynomial envelopes. -/
theorem firstStep_polynomial_envelopes {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    -(9 : ℝ) / 10 + (6 : ℝ) / 5 * s - s ^ 2 / 8 ≤ H s ∧
      H s ≤ -(21 : ℝ) / 10 + (41 : ℝ) / 20 * s - s ^ 2 / 4 := by
  have h := firstStep_sound hs
  norm_num [Step.lowerEnvelope, Step.upperEnvelope, firstStep, integrated,
    primitive, primitiveFrom, evalQ, add, eval] at h
  constructor <;> nlinarith only [h.1, h.2]

end

end ImbalancedChen.Certificates.P2BuchstabPolynomialStep
