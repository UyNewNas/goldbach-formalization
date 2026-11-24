import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. No producer, numerical replay, Lean, or lake run.

Exact Lebesgue moments for the canonical THREE-dimensional tetrahedron,
followed by genuine affine change of variables with absolute determinant.
The integer beta integral is proved by FTC and an elementary recurrence;
no source moment formula is assumed. Tetrahedron moments are then derived
from a proved Fubini identity on the actual closed tetrahedron.

This is a dimension-three prerequisite. Catalog #7 needs dimension6 and
#17/#19 need dimension8; those higher-dimensional simplex moment inductions
are not silently supplied by the present result. No numerical gain, simplex
cover, source floor sum, or log-Jensen conclusion is claimed here.
-/

namespace ImbalancedChen.Certificates.P2AffineSimplexMomentLaw

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval

/-- Polynomial beta integral; the endpoints are actual real endpoints. -/
def betaMonomial (a b : ℕ) (s : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..s, x ^ a * (s - x) ^ b

private theorem beta_continuous (a b : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ => x ^ a * (s - x) ^ b) := by fun_prop

/-- Integration of the derivative of x^(a+1)(s-x)^(b+1). -/
theorem beta_recurrence (a b : ℕ) (s : ℝ) :
    ((a : ℝ) + 1) * betaMonomial a (b + 1) s =
      ((b : ℝ) + 1) * betaMonomial (a + 1) b s := by
  let F : ℝ → ℝ := fun x => x ^ (a + 1) * (s - x) ^ (b + 1)
  let D : ℝ → ℝ := fun x =>
    ((a : ℝ) + 1) * (x ^ a * (s - x) ^ (b + 1)) -
      ((b : ℝ) + 1) * (x ^ (a + 1) * (s - x) ^ b)
  have hd (x : ℝ) : HasDerivAt F (D x) x := by
    have hx := hasDerivAt_pow (a + 1) x
    have hs := ((hasDerivAt_const x s).sub (hasDerivAt_id x)).pow (b + 1)
    convert hx.mul hs using 1 <;>
      simp [F, D, Nat.cast_add, Nat.cast_one] <;> ring
  have hD : Continuous D := by dsimp [D]; fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hD.intervalIntegrable 0 s)
  have hends : F s - F 0 = 0 := by simp [F]
  rw [hends] at he
  have h₁ := ((beta_continuous a (b + 1) s).intervalIntegrable 0 s).const_mul
    ((a : ℝ) + 1)
  have h₂ := ((beta_continuous (a + 1) b s).intervalIntegrable 0 s).const_mul
    ((b : ℝ) + 1)
  change (∫ x in (0 : ℝ)..s,
    ((a : ℝ) + 1) * (x ^ a * (s - x) ^ (b + 1)) -
      ((b : ℝ) + 1) * (x ^ (a + 1) * (s - x) ^ b)) = 0 at he
  rw [intervalIntegral.integral_sub h₁ h₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  exact sub_eq_zero.mp he

/-- The factorial beta law is a theorem about an actual real integral. -/
theorem betaMonomial_eq (a b : ℕ) (s : ℝ) :
    betaMonomial a b s =
      ((a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ)) *
        s ^ (a + b + 1) := by
  induction b generalizing a with
  | zero =>
      have ha : (a : ℝ) + 1 ≠ 0 := by positivity
      have hf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
      simp only [betaMonomial, pow_zero, mul_one, intervalIntegral.integral_pow,
        Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_pow (by omega : a + 1 ≠ 0),
        sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
      field_simp [ha, hf, Nat.cast_ne_zero, Nat.factorial_ne_zero] <;> ring
  | succ b ih =>
      have ha : (a : ℝ) + 1 ≠ 0 := by positivity
      have hf : ((a + (b + 1) + 1).factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (a + (b + 1) + 1)
      have he : a + 1 + b + 1 = a + (b + 1) + 1 := by omega
      have h := beta_recurrence a b s
      rw [ih (a + 1), he] at h
      apply (mul_left_cancel₀ ha)
      rw [h]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [ha, hf, Nat.cast_ne_zero, Nat.factorial_ne_zero] <;> ring

theorem beta_Icc_eq (a b : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x in Icc (0 : ℝ) s, x ^ a * (s - x) ^ b) =
      ((a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ)) *
        s ^ (a + b + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
  exact betaMonomial_eq a b s

abbrev Pair := ℝ × ℝ
abbrev Point := ℝ × Pair

def square (s : ℝ) : Set Pair := Icc 0 s ×ˢ Icc 0 s
def triangle (s : ℝ) : Set Pair := square s ∩ {p | p.1 + p.2 ≤ s}
def cube : Set Point := Icc (0 : ℝ) 1 ×ˢ square 1
def tetrahedron : Set Point := cube ∩ {p | p.1 + p.2.1 + p.2.2 ≤ 1}

theorem measurableSet_triangle (s : ℝ) : MeasurableSet (triangle s) := by
  exact (measurableSet_Icc.prod measurableSet_Icc).inter
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet

theorem measurableSet_tetrahedron : MeasurableSet tetrahedron := by
  exact (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)).inter
    (isClosed_le ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
      (continuous_snd.comp continuous_snd)) continuous_const).measurableSet

theorem isCompact_tetrahedron : IsCompact tetrahedron := by
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
  exact isClosed_le ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
    (continuous_snd.comp continuous_snd)) continuous_const

/-- Closed-triangle Fubini with the true slanted upper endpoint. -/
theorem integral_triangle_nested {s : ℝ} (hs : 0 ≤ s) (f : Pair → ℝ)
    (hf : Continuous f) :
    (∫ p in triangle s, f p) =
      ∫ x in Icc (0 : ℝ) s, ∫ y in Icc (0 : ℝ) (s - x), f (x, y) := by
  let O : Set Pair := {p | p.1 + p.2 ≤ s}
  have hO : MeasurableSet O :=
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet
  have hi : IntegrableOn f (square s) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc
    _ = ∫ p in square s, O.indicator f p := (setIntegral_indicator hO).symm
    _ = ∫ x in Icc (0 : ℝ) s, ∫ y in Icc (0 : ℝ) s, O.indicator f (x, y) := by
      rw [square, Measure.volume_eq_prod]
      exact setIntegral_prod _ (by
        simpa only [square, Measure.volume_eq_prod] using hi.indicator hO)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have he : (fun y => O.indicator f (x, y)) =
          (Iic (s - x)).indicator (fun y => f (x, y)) := by
        funext y
        by_cases h : y ≤ s - x
        · have h' : x + y ≤ s := by linarith
          simp [O, h, h']
        · have h' : ¬ x + y ≤ s := by linarith
          simp [O, h, h']
      rw [he, setIntegral_indicator measurableSet_Iic]
      have hset : Icc (0 : ℝ) s ∩ Iic (s - x) = Icc (0 : ℝ) (s - x) := by
        ext y
        constructor
        · intro hy; exact ⟨hy.1.1, hy.2⟩
        · intro hy
          exact ⟨⟨hy.1, by linarith [hx.1, hy.2]⟩, hy.2⟩
      rw [hset]

/-- Actual closed-tetrahedron Lebesgue integral as three nested integrals.
No iterated-integral definition is substituted for volume.restrict. -/
theorem integral_tetrahedron_nested (f : Point → ℝ) (hf : Continuous f) :
    (∫ p in tetrahedron, f p) = ∫ x in Icc (0 : ℝ) 1,
      ∫ y in Icc (0 : ℝ) (1 - x),
        ∫ z in Icc (0 : ℝ) (1 - x - y), f (x, y, z) := by
  let O : Set Point := {p | p.1 + p.2.1 + p.2.2 ≤ 1}
  have hO : MeasurableSet O :=
    (isClosed_le ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
      (continuous_snd.comp continuous_snd)) continuous_const).measurableSet
  have hi : IntegrableOn f cube :=
    hf.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  calc
    _ = ∫ p in cube, O.indicator f p := (setIntegral_indicator hO).symm
    _ = ∫ x in Icc (0 : ℝ) 1, ∫ yz in square 1, O.indicator f (x, yz) := by
      rw [cube, Measure.volume_eq_prod]
      exact setIntegral_prod _ (by
        simpa only [cube, Measure.volume_eq_prod] using hi.indicator hO)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have he : (fun yz => O.indicator f (x, yz)) =
          {yz : Pair | yz.1 + yz.2 ≤ 1 - x}.indicator (fun yz => f (x, yz)) := by
        funext yz
        by_cases h : yz.1 + yz.2 ≤ 1 - x
        · have h' : x + yz.1 + yz.2 ≤ 1 := by linarith
          simp [O, h, h']
        · have h' : ¬ x + yz.1 + yz.2 ≤ 1 := by linarith
          simp [O, h, h']
      have hclosed : MeasurableSet {yz : Pair | yz.1 + yz.2 ≤ 1 - x} :=
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet
      rw [he, setIntegral_indicator hclosed]
      have hset : square 1 ∩ {yz : Pair | yz.1 + yz.2 ≤ 1 - x} = triangle (1 - x) := by
        ext yz
        simp only [square, triangle, mem_inter_iff, mem_prod, mem_Icc, mem_setOf_eq]
        constructor
        · rintro ⟨⟨⟨hy0, hy1⟩, ⟨hz0, hz1⟩⟩, hsum⟩
          exact ⟨⟨⟨hy0, by linarith⟩, ⟨hz0, by linarith⟩⟩, hsum⟩
        · rintro ⟨⟨⟨hy0, hy1⟩, ⟨hz0, hz1⟩⟩, hsum⟩
          exact ⟨⟨⟨hy0, by linarith [hx.1]⟩, ⟨hz0, by linarith [hx.1]⟩⟩, hsum⟩
      rw [hset]
      simpa only [sub_sub] using integral_triangle_nested (by linarith [hx.2])
        (fun yz => f (x, yz)) (hf.comp (continuous_const.prod_mk continuous_id))

def monomial (a b c d : ℕ) (p : Point) : ℝ :=
  p.1 ^ a * p.2.1 ^ b * p.2.2 ^ c * (1 - p.1 - p.2.1 - p.2.2) ^ d

/-- All natural monomial moments, including the missing barycentric
coordinate. This is a real Lebesgue integral theorem, not an input law. -/
theorem integral_monomial (a b c d : ℕ) :
    (∫ p in tetrahedron, monomial a b c d p) =
      (a.factorial : ℝ) * b.factorial * c.factorial * d.factorial /
        ((a + b + c + d + 3).factorial : ℝ) := by
  rw [integral_tetrahedron_nested _ (by dsimp [monomial]; fun_prop)]
  have hinner (x y : ℝ) (hy : 0 ≤ 1 - x - y) :
      (∫ z in Icc (0 : ℝ) (1 - x - y), monomial a b c d (x, y, z)) =
        x ^ a * y ^ b *
          (((c.factorial : ℝ) * d.factorial / ((c + d + 1).factorial : ℝ)) *
            (1 - x - y) ^ (c + d + 1)) := by
    have he : (fun z => monomial a b c d (x, y, z)) =
        (fun z => (x ^ a * y ^ b) * (z ^ c * ((1 - x - y) - z) ^ d)) := by
      funext z
      dsimp [monomial]
      ring
    rw [he, integral_const_mul, beta_Icc_eq c d hy]
  have hmiddle (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (∫ y in Icc (0 : ℝ) (1 - x),
        ∫ z in Icc (0 : ℝ) (1 - x - y), monomial a b c d (x, y, z)) =
      ((c.factorial : ℝ) * d.factorial / ((c + d + 1).factorial : ℝ)) * x ^ a *
        (((b.factorial : ℝ) * (c + d + 1).factorial /
          ((b + (c + d + 1) + 1).factorial : ℝ)) *
            (1 - x) ^ (b + (c + d + 1) + 1)) := by
    have hfun : (∫ y in Icc (0 : ℝ) (1 - x),
        ∫ z in Icc (0 : ℝ) (1 - x - y), monomial a b c d (x, y, z)) =
        ∫ y in Icc (0 : ℝ) (1 - x),
          (((c.factorial : ℝ) * d.factorial / ((c + d + 1).factorial : ℝ)) * x ^ a) *
            (y ^ b * ((1 - x) - y) ^ (c + d + 1)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      rw [hinner x y (by linarith [hy.2])]
      ring
    rw [hfun, integral_const_mul, beta_Icc_eq b (c + d + 1) (by linarith [hx.2])]
  have hout : (∫ x in Icc (0 : ℝ) 1,
      ∫ y in Icc (0 : ℝ) (1 - x),
        ∫ z in Icc (0 : ℝ) (1 - x - y), monomial a b c d (x, y, z)) =
      (((c.factorial : ℝ) * d.factorial / ((c + d + 1).factorial : ℝ)) *
        ((b.factorial : ℝ) * (c + d + 1).factorial /
          ((b + (c + d + 1) + 1).factorial : ℝ))) *
        (((a.factorial : ℝ) * (b + (c + d + 1) + 1).factorial /
          ((a + (b + (c + d + 1) + 1) + 1).factorial : ℝ))) := by
    calc
      _ = ∫ x in Icc (0 : ℝ) 1,
          ((((c.factorial : ℝ) * d.factorial / ((c + d + 1).factorial : ℝ)) *
            ((b.factorial : ℝ) * (c + d + 1).factorial /
              ((b + (c + d + 1) + 1).factorial : ℝ)))) *
              (x ^ a * (1 - x) ^ (b + (c + d + 1) + 1)) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        rw [hmiddle x hx]
        ring
      _ = _ := by
        rw [integral_const_mul, beta_Icc_eq a (b + (c + d + 1) + 1) (by norm_num)]
        simp only [one_pow, mul_one]
  rw [hout]
  have he : a + (b + (c + d + 1) + 1) + 1 = a + b + c + d + 3 := by omega
  rw [he]
  have hf₁ : ((c + d + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (c + d + 1)
  have hf₂ : ((b + (c + d + 1) + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (b + (c + d + 1) + 1)
  have hf₃ : ((a + b + c + d + 3).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a + b + c + d + 3)
  field_simp [hf₁, hf₂, hf₃] <;> ring

def barycentric (i : Fin 4) (p : Point) : ℝ :=
  (![1 - p.1 - p.2.1 - p.2.2, p.1, p.2.1, p.2.2] : Fin 4 → ℝ) i

def affineVertex (v : Fin 4 → ℝ) (p : Point) : ℝ := ∑ i, barycentric i p * v i

theorem barycentric_continuous (i : Fin 4) : Continuous (barycentric i) := by
  fin_cases i <;> dsimp [barycentric] <;> fun_prop

theorem affineVertex_continuous (v : Fin 4 → ℝ) : Continuous (affineVertex v) := by
  apply continuous_finsetSum
  intro i _
  exact (barycentric_continuous i).mul continuous_const

theorem barycentric_nonneg {p : Point} (hp : p ∈ tetrahedron) (i : Fin 4) :
    0 ≤ barycentric i p := by
  rcases hp with ⟨⟨hx, hy, hz⟩, hsum⟩
  fin_cases i <;> simp only [barycentric, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    linarith [hx.1, hy.1, hz.1]

theorem affineVertex_nonneg {v : Fin 4 → ℝ} (hv : ∀ i, 0 ≤ v i)
    {p : Point} (hp : p ∈ tetrahedron) : 0 ≤ affineVertex v p := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (barycentric_nonneg hp i) (hv i))

theorem integral_barycentric_monomial (e : Fin 4 → ℕ) :
    (∫ p in tetrahedron, ∏ i : Fin 4, barycentric i p ^ e i) =
      (∏ i : Fin 4, (e i).factorial : ℝ) / ((∑ i : Fin 4, e i) + 3).factorial := by
  have he : e 1 + e 2 + e 3 + e 0 + 3 = (∑ i : Fin 4, e i) + 3 := by
    simp only [Fin.sum_univ_succ]
    omega
  have hf : (∫ p in tetrahedron, ∏ i : Fin 4, barycentric i p ^ e i) =
      ∫ p in tetrahedron, monomial (e 1) (e 2) (e 3) (e 0) p := by
    apply setIntegral_congr_fun measurableSet_tetrahedron
    intro p _
    simp [Fin.prod_univ_succ, barycentric, monomial]
    <;> ring
  rw [hf, integral_monomial, he]
  simp only [Fin.prod_univ_succ]
  ring

theorem integral_one : (∫ _p in tetrahedron, (1 : ℝ)) = 1 / 6 := by
  have h := integral_monomial 0 0 0 0
  norm_num [monomial] at h
  exact h

private theorem prod_barycentric_single (i : Fin 4) (p : Point) :
    (∏ r : Fin 4, barycentric r p ^ (if r = i then 1 else 0)) = barycentric i p := by
  calc
    _ = barycentric i p ^ (if i = i then 1 else 0) :=
      Finset.prod_eq_single i (fun r _ hri => by simp [hri]) (by simp)
    _ = _ := by simp

theorem integral_barycentric (i : Fin 4) :
    (∫ p in tetrahedron, barycentric i p) = 1 / 24 := by
  calc
    _ = ∫ p in tetrahedron,
        ∏ r : Fin 4, barycentric r p ^ (if r = i then 1 else 0) := by
      apply setIntegral_congr_fun measurableSet_tetrahedron
      intro p _
      exact (prod_barycentric_single i p).symm
    _ = _ := by
      rw [integral_barycentric_monomial]
      fin_cases i <;> norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ]

def delta (i j : Fin 4) : ℝ := if i = j then 1 else 0

theorem integral_barycentric_two (i j : Fin 4) :
    (∫ p in tetrahedron, barycentric i p * barycentric j p) = (1 + delta i j) / 120 := by
  let e : Fin 4 → ℕ := fun r => (if r = i then 1 else 0) + (if r = j then 1 else 0)
  have he (p : Point) : (∏ r : Fin 4, barycentric r p ^ e r) =
      barycentric i p * barycentric j p := by
    simp only [e, pow_add, Finset.prod_mul_distrib, prod_barycentric_single]
  calc
    _ = ∫ p in tetrahedron, ∏ r : Fin 4, barycentric r p ^ e r := by
      apply setIntegral_congr_fun measurableSet_tetrahedron
      intro p _
      exact (he p).symm
    _ = _ := by
      rw [integral_barycentric_monomial]
      fin_cases i <;> fin_cases j <;>
        norm_num [e, delta, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem integral_barycentric_three (i j k : Fin 4) :
    (∫ p in tetrahedron, barycentric i p * barycentric j p * barycentric k p) =
      (1 + delta i j + delta i k + delta j k + 2 * delta i j * delta i k) / 720 := by
  let e : Fin 4 → ℕ := fun r =>
    (if r = i then 1 else 0) + (if r = j then 1 else 0) + (if r = k then 1 else 0)
  have he (p : Point) : (∏ r : Fin 4, barycentric r p ^ e r) =
      barycentric i p * barycentric j p * barycentric k p := by
    simp only [e, pow_add, Finset.prod_mul_distrib, prod_barycentric_single]
  calc
    _ = ∫ p in tetrahedron, ∏ r : Fin 4, barycentric r p ^ e r := by
      apply setIntegral_congr_fun measurableSet_tetrahedron
      intro p _
      exact (he p).symm
    _ = _ := by
      rw [integral_barycentric_monomial]
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        norm_num [e, delta, Fin.sum_univ_succ, Fin.prod_univ_succ]

def vertexSum (v : Fin 4 → ℝ) : ℝ := ∑ i, v i
def dot (g l : Fin 4 → ℝ) : ℝ := ∑ i, g i * l i
def squareSum (l : Fin 4 → ℝ) : ℝ := ∑ i, (l i) ^ 2
def weightedSquareSum (g l : Fin 4 → ℝ) : ℝ := ∑ i, g i * (l i) ^ 2

/-- Actual affine gap mass = volume times the arithmetic vertex mean. -/
theorem integral_affineVertex (g : Fin 4 → ℝ) :
    (∫ p in tetrahedron, affineVertex g p) = vertexSum g / 24 := by
  have hi (i : Fin 4) : IntegrableOn (fun p => barycentric i p * g i) tetrahedron :=
    ((barycentric_continuous i).mul continuous_const).continuousOn.integrableOn_compact
      isCompact_tetrahedron
  rw [affineVertex, integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_mul_const, integral_barycentric]
  simp [vertexSum, Fin.sum_univ_succ]
  <;> ring

theorem integral_affineVertex_two (g l : Fin 4 → ℝ) :
    (∫ p in tetrahedron, affineVertex g p * affineVertex l p) =
      (vertexSum g * vertexSum l + dot g l) / 120 := by
  have he : (fun p => affineVertex g p * affineVertex l p) =
      (fun p => ∑ i : Fin 4, ∑ j : Fin 4,
        (g i * l j) * (barycentric i p * barycentric j p)) := by
    funext p
    simp only [affineVertex, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : Fin 4) : IntegrableOn
      (fun p => (g i * l j) * (barycentric i p * barycentric j p)) tetrahedron := by
    apply ContinuousOn.integrableOn_compact _ isCompact_tetrahedron
    exact (continuous_const.mul ((barycentric_continuous i).mul
      (barycentric_continuous j))).continuousOn
  have hs (i : Fin 4) : IntegrableOn (fun p => ∑ j : Fin 4,
      (g i * l j) * (barycentric i p * barycentric j p)) tetrahedron :=
    integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have hm (i : Fin 4) :
      (∫ p in tetrahedron, ∑ j : Fin 4,
        (g i * l j) * (barycentric i p * barycentric j p)) =
      ∑ j : Fin 4, (g i * l j) * ((1 + delta i j) / 120) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    simp only [integral_const_mul, integral_barycentric_two]
  rw [he, integral_finsetSum Finset.univ (fun i _ => hs i)]
  simp_rw [hm]
  simp [vertexSum, dot, delta, Fin.sum_univ_succ]
  <;> ring

/-- Third barycentric moments yield the actual second affine moment under
an affine gap weight. Correlations are kept in the mixed terms. -/
theorem integral_affineVertex_square (g l : Fin 4 → ℝ) :
    (∫ p in tetrahedron, affineVertex g p * (affineVertex l p) ^ 2) =
      (vertexSum g * ((vertexSum l) ^ 2 + squareSum l) +
        2 * dot g l * vertexSum l + 2 * weightedSquareSum g l) / 720 := by
  have he : (fun p => affineVertex g p * (affineVertex l p) ^ 2) =
      (fun p => ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
        (g i * l j * l k) * (barycentric i p * barycentric j p * barycentric k p)) := by
    funext p
    simp only [affineVertex, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hi (i j k : Fin 4) : IntegrableOn
      (fun p => (g i * l j * l k) *
        (barycentric i p * barycentric j p * barycentric k p)) tetrahedron := by
    apply ContinuousOn.integrableOn_compact _ isCompact_tetrahedron
    exact (continuous_const.mul (((barycentric_continuous i).mul
      (barycentric_continuous j)).mul (barycentric_continuous k))).continuousOn
  have hs (i j : Fin 4) : IntegrableOn (fun p => ∑ k : Fin 4,
      (g i * l j * l k) * (barycentric i p * barycentric j p * barycentric k p))
      tetrahedron := integrable_finsetSum Finset.univ (fun k _ => hi i j k)
  have hss (i : Fin 4) : IntegrableOn (fun p => ∑ j : Fin 4, ∑ k : Fin 4,
      (g i * l j * l k) * (barycentric i p * barycentric j p * barycentric k p))
      tetrahedron := integrable_finsetSum Finset.univ (fun j _ => hs i j)
  have hm (i j : Fin 4) :
      (∫ p in tetrahedron, ∑ k : Fin 4,
        (g i * l j * l k) * (barycentric i p * barycentric j p * barycentric k p)) =
      ∑ k : Fin 4, (g i * l j * l k) *
        ((1 + delta i j + delta i k + delta j k + 2 * delta i j * delta i k) / 720) := by
    rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
    simp only [integral_const_mul, integral_barycentric_three]
  have hmm (i : Fin 4) :
      (∫ p in tetrahedron, ∑ j : Fin 4, ∑ k : Fin 4,
        (g i * l j * l k) * (barycentric i p * barycentric j p * barycentric k p)) =
      ∑ j : Fin 4, ∑ k : Fin 4, (g i * l j * l k) *
        ((1 + delta i j + delta i k + delta j k + 2 * delta i j * delta i k) / 720) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hs i j)]
    simp_rw [hm]
  rw [he, integral_finsetSum Finset.univ (fun i _ => hss i)]
  simp_rw [hmm]
  simp [vertexSum, dot, squareSum, weightedSquareSum, delta, Fin.sum_univ_succ]
  <;> ring

def gapMass (g : Fin 4 → ℝ) : ℝ := ∫ p in tetrahedron, affineVertex g p
def weightedMean (g l : Fin 4 → ℝ) : ℝ :=
  (∫ p in tetrahedron, affineVertex g p * affineVertex l p) / gapMass g
def weightedSecond (g l : Fin 4 → ℝ) : ℝ :=
  (∫ p in tetrahedron, affineVertex g p * (affineVertex l p) ^ 2) / gapMass g
def weightedVariance (g l : Fin 4 → ℝ) : ℝ := weightedSecond g l - (weightedMean g l) ^ 2

theorem gapMass_eq (g : Fin 4 → ℝ) : gapMass g = (1 / 6 : ℝ) * vertexSum g / 4 := by
  rw [gapMass, integral_affineVertex]
  ring

theorem gapMass_pos {g : Fin 4 → ℝ} (hG : 0 < vertexSum g) : 0 < gapMass g := by
  rw [gapMass, integral_affineVertex]
  positivity

/-- Four vertices give denominator5 in the gap-weighted mean. This is
intentionally not presented as the dimension6 denominator8 or dimension8
denominator10 used by the source engines. -/
theorem weightedMean_eq (g l : Fin 4 → ℝ) (hG : vertexSum g ≠ 0) :
    weightedMean g l = (vertexSum l + dot g l / vertexSum g) / 5 := by
  rw [weightedMean, gapMass, integral_affineVertex, integral_affineVertex_two]
  field_simp [hG] <;> ring

theorem weightedSecond_eq (g l : Fin 4 → ℝ) (hG : vertexSum g ≠ 0) :
    weightedSecond g l =
      (vertexSum g * ((vertexSum l) ^ 2 + squareSum l) +
        2 * dot g l * vertexSum l + 2 * weightedSquareSum g l) / (30 * vertexSum g) := by
  rw [weightedSecond, gapMass, integral_affineVertex, integral_affineVertex_square]
  field_simp [hG] <;> ring

/-- A central moment of the actual weighted Lebesgue integral. -/
theorem centralMoment_eq (g l : Fin 4 → ℝ) (hG : vertexSum g ≠ 0) :
    (∫ p in tetrahedron, affineVertex g p *
      (affineVertex l p - weightedMean g l) ^ 2) / gapMass g = weightedVariance g l := by
  let m := weightedMean g l
  have hi₀ : IntegrableOn (affineVertex g) tetrahedron :=
    (affineVertex_continuous g).continuousOn.integrableOn_compact isCompact_tetrahedron
  have hi₁ : IntegrableOn (fun p => affineVertex g p * affineVertex l p) tetrahedron :=
    ((affineVertex_continuous g).mul (affineVertex_continuous l)).continuousOn.integrableOn_compact
      isCompact_tetrahedron
  have hi₂ : IntegrableOn (fun p => affineVertex g p * (affineVertex l p) ^ 2) tetrahedron :=
    ((affineVertex_continuous g).mul ((affineVertex_continuous l).pow 2)).continuousOn.integrableOn_compact
      isCompact_tetrahedron
  have he : (fun p => affineVertex g p * (affineVertex l p - m) ^ 2) =
      (fun p => (affineVertex g p * (affineVertex l p) ^ 2 -
        (2 * m) * (affineVertex g p * affineVertex l p)) + m ^ 2 * affineVertex g p) := by
    funext p
    ring
  have hm : gapMass g ≠ 0 := by rw [gapMass, integral_affineVertex]; exact div_ne_zero hG (by norm_num)
  change (∫ p in tetrahedron, affineVertex g p * (affineVertex l p - m) ^ 2) /
      gapMass g = weightedVariance g l
  rw [he, integral_add (hi₂.sub (hi₁.const_mul _)) (hi₀.const_mul _),
    integral_sub hi₂ (hi₁.const_mul _), integral_const_mul, integral_const_mul]
  dsimp [weightedVariance, weightedSecond, weightedMean, m, gapMass] at hm ⊢
  field_simp [hm] <;> ring

theorem weightedVariance_nonneg (g l : Fin 4 → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hG : 0 < vertexSum g) : 0 ≤ weightedVariance g l := by
  rw [← centralMoment_eq g l hG.ne']
  apply div_nonneg _ (gapMass_pos hG).le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_tetrahedron] with p hp
  exact mul_nonneg (affineVertex_nonneg hg hp) (sq_nonneg _)

section AffineTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The genuine affine change-of-variables theorem, in every finite
dimension. The multiplier is the absolute determinant, not its reciprocal
and not an ordering factorial. -/
theorem integral_affine_image (μ : Measure E) [IsAddHaarMeasure μ]
    (L : E ≃L[ℝ] E) (b : E) (D : Set E) (hD : MeasurableSet D) (f : E → ℝ) :
    (∫ y in (fun x => b + L x) '' D, f y ∂μ) =
      |L.toContinuousLinearMap.det| * ∫ x in D, f (b + L x) ∂μ := by
  have hd : ∀ x ∈ D, HasFDerivWithinAt (fun y => b + L y)
      L.toContinuousLinearMap D x := by
    intro x _
    exact (L.toContinuousLinearMap.hasFDerivAt.const_add b).hasFDerivWithinAt
  have hinj : InjOn (fun x => b + L x) D := by
    intro x _ y _ h
    exact L.injective (add_left_cancel h)
  have h := integral_image_eq_integral_abs_det_fderiv_smul μ hD hd hinj f
  simpa only [smul_eq_mul, integral_const_mul] using h

def transport (L : E ≃L[ℝ] E) (b : E) (f : E → ℝ) (y : E) : ℝ :=
  f (L.symm (y - b))

theorem transport_apply (L : E ≃L[ℝ] E) (b x : E) (f : E → ℝ) :
    transport L b f (b + L x) = f x := by
  simp [transport, add_sub_cancel_left]

theorem integral_affine_transport (μ : Measure E) [IsAddHaarMeasure μ]
    (L : E ≃L[ℝ] E) (b : E) (D : Set E) (hD : MeasurableSet D) (f : E → ℝ) :
    (∫ y in (fun x => b + L x) '' D, transport L b f y ∂μ) =
      |L.toContinuousLinearMap.det| * ∫ x in D, f x ∂μ := by
  rw [integral_affine_image μ L b D hD]
  simp only [transport_apply]

end AffineTransport

def physicalTetrahedron (L : Point ≃L[ℝ] Point) (b : Point) : Set Point :=
  (fun x => b + L x) '' tetrahedron

/-- Actual physical volume: canonical volume1/6 times the absolute
determinant. No determinant or volume is supplied as a numerical premise. -/
theorem physical_volume (L : Point ≃L[ℝ] Point) (b : Point) :
    (∫ _y in physicalTetrahedron L b, (1 : ℝ)) =
      |L.toContinuousLinearMap.det| / 6 := by
  rw [physicalTetrahedron, integral_affine_image volume L b tetrahedron
    measurableSet_tetrahedron, integral_one]
  ring

theorem physical_monomial (L : Point ≃L[ℝ] Point) (b₀ : Point) (a b c d : ℕ) :
    (∫ y in physicalTetrahedron L b₀, transport L b₀ (monomial a b c d) y) =
      |L.toContinuousLinearMap.det| *
        ((a.factorial : ℝ) * b.factorial * c.factorial * d.factorial /
          ((a + b + c + d + 3).factorial : ℝ)) := by
  rw [physicalTetrahedron, integral_affine_transport volume L b₀ tetrahedron
    measurableSet_tetrahedron, integral_monomial]

theorem physical_affine_mass (L : Point ≃L[ℝ] Point) (b : Point) (g : Fin 4 → ℝ) :
    (∫ y in physicalTetrahedron L b, transport L b (affineVertex g) y) =
      (|L.toContinuousLinearMap.det| / 6) * vertexSum g / 4 := by
  rw [physicalTetrahedron, integral_affine_transport volume L b tetrahedron
    measurableSet_tetrahedron, integral_affineVertex]
  ring

theorem physical_affine_first_moment (L : Point ≃L[ℝ] Point) (b : Point)
    (g l : Fin 4 → ℝ) :
    (∫ y in physicalTetrahedron L b,
      transport L b (affineVertex g) y * transport L b (affineVertex l) y) =
      |L.toContinuousLinearMap.det| *
        ((vertexSum g * vertexSum l + dot g l) / 120) := by
  have he : (fun y => transport L b (affineVertex g) y *
      transport L b (affineVertex l) y) =
      transport L b (fun x => affineVertex g x * affineVertex l x) := by rfl
  rw [he, physicalTetrahedron, integral_affine_transport volume L b tetrahedron
    measurableSet_tetrahedron, integral_affineVertex_two]

theorem physical_affine_second_moment (L : Point ≃L[ℝ] Point) (b : Point)
    (g l : Fin 4 → ℝ) :
    (∫ y in physicalTetrahedron L b,
      transport L b (affineVertex g) y * (transport L b (affineVertex l) y) ^ 2) =
      |L.toContinuousLinearMap.det| *
        ((vertexSum g * ((vertexSum l) ^ 2 + squareSum l) +
          2 * dot g l * vertexSum l + 2 * weightedSquareSum g l) / 720) := by
  have he : (fun y => transport L b (affineVertex g) y *
      (transport L b (affineVertex l) y) ^ 2) =
      transport L b (fun x => affineVertex g x * (affineVertex l x) ^ 2) := by rfl
  rw [he, physicalTetrahedron, integral_affine_transport volume L b tetrahedron
    measurableSet_tetrahedron, integral_affineVertex_square]

end

end ImbalancedChen.Certificates.P2AffineSimplexMomentLaw
