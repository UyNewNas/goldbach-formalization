import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-!
SOURCE ONLY. UNCOMPILED. K DEPENDENCY HOLD IS INHERITED. ZERO FORMAL CREDIT.

The finite polynomial guards below are UNEVALUATED proof scripts. They
are universal polynomial identities in nine independent real variables,
not tests on archived rows and not assumed integral identities. They
cover exactly the original degrees 0..6. No executable or producer is
run by this source authoring session.

The analytic bridge expands the actual barycentric power by Mathlib's
multinomial theorem and integrates every monomial using K.baryMoment_eq.
The guard identifies that factorial polynomial with the Newton recurrence
on TEN nodes, obtained by duplicating one of the SAME nine vertex nodes.
The final constructor supplies K.MomentRow.higherPowerMoments from finite
rational vertex encodings. No integral-valued assumption is accepted.
-/

namespace ImbalancedChen.P2OriginalSaving19HigherMoments

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SourceMeasure
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2DegreeSixLogGapSoundnessSourceOnly

/-- Newton's complete-homogeneous recurrence. Its power sum contains
all nine nodes AND a second occurrence of node `i`. The division is by
the current positive degree; it is not the barycentric normalization. -/
def duplicateH {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 9 → A) (i : Fin 9) : ℕ → A
  | 0 => 1
  | k + 1 => ((k + 1 : ℚ)⁻¹) •
      ∑ j : Fin (k + 1),
        ((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
          duplicateH y i (k - j.val)
termination_by k => k
decreasing_by omega

theorem duplicateH_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B)
    (y : Fin 9 → A) (i : Fin 9) (k : ℕ) :
    f (duplicateH y i k) = duplicateH (fun r => f (y r)) i k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [duplicateH]
    | succ k =>
      simp only [duplicateH, map_smul, map_sum, map_mul, map_add, map_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (k - j.val) (by omega)]

/-- Rational mixture before any common-denominator representation. -/
def rationalMoment (g y : Fin 9 → ℚ) (k : ℕ) : ℚ :=
  (∑ i : Fin 9, g i * duplicateH y i k) /
    ((∑ i : Fin 9, g i) * ((9 + k).choose k : ℚ))

def realMoment (g y : Fin 9 → ℝ) (k : ℕ) : ℝ :=
  (∑ i : Fin 9, g i * duplicateH y i k) /
    ((∑ i : Fin 9, g i) * ((9 + k).choose k : ℝ))

theorem rationalMoment_cast (g y : Fin 9 → ℚ) (k : ℕ) :
    (rationalMoment g y k : ℝ) =
      realMoment (fun i => (g i : ℝ)) (fun i => (y i : ℝ)) k := by
  unfold rationalMoment realMoment
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [duplicateH_map (Algebra.ofId ℚ ℝ)]

/-- The exact rational coefficient already proved by the held K
Lebesgue monomial theorem, including the residual coordinate 0. -/
def baryCoefficient (e : Fin 9 → ℕ) : ℚ :=
  (((e 0).factorial *
      P2Winner9NestedEightSimplexMoment.factorialProduct
        (List.ofFn (fun r : Fin 8 => e r.succ)) : ℕ) : ℚ) /
    (((e 0) + (List.ofFn (fun r : Fin 8 => e r.succ)).sum + 8).factorial : ℚ)

theorem baryCoefficient_cast (e : Fin 9 → ℕ) :
    (baryCoefficient e : ℝ) = baryMoment e := by
  rw [baryMoment_eq]
  simp [baryCoefficient]

def bumped (e : Fin 9 → ℕ) (i : Fin 9) : Fin 9 → ℕ :=
  fun r => e r + unitExponent i r

theorem bary_bumped (e : Fin 9 → ℕ) (i : Fin 9) (x : Point) :
    (∏ r : Fin 9, bary r x ^ bumped e i r) =
      bary i x * ∏ r : Fin 9, bary r x ^ e r := by
  simp only [bumped, pow_add, Finset.prod_mul_distrib, prod_unitExponent]
  ring

/-- The complete, untruncated multinomial expansion in degree `k`,
integrated against barycentric weight i. No row values occur here. -/
def integratedPower (y : Fin 9 → ℝ) (i : Fin 9) (k : ℕ) : ℝ :=
  ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 9)) k,
    ((Nat.multinomial Finset.univ e : ℝ) * (baryCoefficient (bumped e i) : ℝ)) *
        ∏ r : Fin 9, y r ^ e r

/-- CLOSED FINITE GUARD; UNEVALUATED.

Each side is a polynomial with rational coefficients and nine arbitrary
real arguments; the arguments are NOT enumerated or specialized to
archive values. `piAntidiag_univ_fin_eq_antidiagonalTuple` switches
the abstract finite enumeration to Mathlib's explicit tuple recursion.
There is no native evaluator, stored-answer literal or archive oracle.
The factor 9! is the integral of one barycentric coordinate inverted;
the additional binomial is precisely (9+k)!/(9! k!). -/
theorem integratedPower_newton_guard (y : Fin 9 → ℝ) (i : Fin 9) (k : ℕ)
    (hk : k ≤ 6) :
    integratedPower y i k =
      duplicateH y i k / ((9.factorial : ℝ) * ((9 + k).choose k : ℝ)) := by
  classical
  interval_cases k <;> fin_cases i <;>
    norm_num [integratedPower,
      Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple,
      List.Nat.antidiagonal, baryCoefficient, bumped, unitExponent,
      P2Winner9NestedEightSimplexMoment.factorialProduct, List.ofFn,
      Nat.multinomial, duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton,
      Algebra.smul_def] <;> ring

/-- Coefficients of the product of the geometric series of the nodes.
This is the complete-homogeneous polynomial, expressed without a
distinct-node or nonzero-node restriction. -/
def completeH {A : Type*} [CommRing A] : List A → ℕ → A
  | [], k => if k = 0 then 1 else 0
  | a :: as, k => ∑ j : Fin (k + 1), a ^ j.val * completeH as (k - j.val)

theorem completeH_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (as : List A) (k : ℕ) :
    f (completeH as k) = completeH (as.map f) k := by
  induction as generalizing k with
  | nil => by_cases hk : k = 0 <;> simp [completeH, hk]
  | cons a as ih => simp [completeH, map_sum, map_mul, map_pow, ih]

/-- Exactly the author's in-place update h[k] += y*h[k-1], with old
coefficients on the right for the shorter node list. -/
theorem completeH_cons_succ {A : Type*} [CommRing A]
    (a : A) (as : List A) (k : ℕ) :
    completeH (a :: as) (k + 1) =
      completeH as (k + 1) + a * completeH (a :: as) k := by
  simp only [completeH]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero, one_mul, Fin.val_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : k + 1 - (j.val + 1) = k - j.val := by omega
  rw [hs, pow_succ]
  ring

/-- CLOSED UNIVERSAL POLYNOMIAL GUARD; UNEVALUATED.
The nine-node geometric-series recurrence convolved with the extra
copy of node i equals the ten-node Newton recurrence. Only i and the
degree are enumerated; all nine rational nodes remain arbitrary. -/
theorem duplicateH_author_guard (y : Fin 9 → ℚ) (i : Fin 9) (k : ℕ)
    (hk : k ≤ 6) :
    duplicateH y i k = ∑ j : Fin (k + 1),
      completeH (List.ofFn y) (k - j.val) * y i ^ j.val := by
  interval_cases k <;> fin_cases i <;>
    norm_num [duplicateH, completeH, List.ofFn, Fin.sum_univ_succ,
      Algebra.smul_def] <;> ring

/-- The actual frozen author engine's numerator h*gp, before Q80 and
Q96. It is distinct from the independent duplicated-node algorithm. -/
def authorMoment (g y : Fin 9 → ℚ) (k : ℕ) : ℚ :=
  (∑ j : Fin (k + 1), completeH (List.ofFn y) (k - j.val) *
    ∑ i : Fin 9, g i * y i ^ j.val) /
      ((∑ i : Fin 9, g i) * ((9 + k).choose k : ℚ))

theorem authorMoment_eq_rationalMoment (g y : Fin 9 → ℚ) (k : ℕ)
    (hk : k ≤ 6) : authorMoment g y k = rationalMoment g y k := by
  unfold authorMoment rationalMoment
  congr 1
  simp_rw [duplicateH_author_guard y _ k hk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Integral-coefficient realization of the ten-node polynomial. -/
def integerDuplicateH (z : Fin 9 → ℤ) (i : Fin 9) (k : ℕ) : ℤ :=
  completeH (z i :: List.ofFn z) k

theorem integerDuplicateH_cast (z : Fin 9 → ℤ) (i : Fin 9) (k : ℕ)
    (hk : k ≤ 6) :
    (integerDuplicateH z i k : ℚ) = duplicateH (fun r => (z r : ℚ)) i k := by
  have hm := completeH_map (Int.castRingHom ℚ) (z i :: List.ofFn z) k
  have he : (integerDuplicateH z i k : ℚ) =
      completeH ((z i : ℚ) :: List.ofFn (fun r => (z r : ℚ))) k := by
    simpa [integerDuplicateH, List.map_ofFn] using hm
  rw [he, completeH, duplicateH_author_guard _ i k hk]
  apply Finset.sum_congr rfl
  intro j _
  ring

def integerNewtonNumerator (z : Fin 9 → ℤ) (i : Fin 9) (k : ℕ) : ℤ :=
  ∑ j : Fin (k + 1),
    ((∑ r : Fin 9, z r ^ (j.val + 1)) + z i ^ (j.val + 1)) *
      integerDuplicateH z i (k - j.val)

/-- The divisibility required by the independent engine's z//k
operation follows from its integer complete-homogeneous polynomial;
it is not a numerical assertion about a particular archived node set. -/
theorem integerNewtonNumerator_spec (z : Fin 9 → ℤ) (i : Fin 9) (k : ℕ)
    (hk : k + 1 ≤ 6) :
    integerNewtonNumerator z i k = (k + 1 : ℤ) * integerDuplicateH z i (k + 1) := by
  have hc (j : Fin (k + 1)) :
      (integerDuplicateH z i (k - j.val) : ℚ) =
        duplicateH (fun r => (z r : ℚ)) i (k - j.val) :=
    integerDuplicateH_cast z i _ (by omega)
  have hQ : (integerNewtonNumerator z i k : ℚ) =
      (k + 1 : ℚ) * (integerDuplicateH z i (k + 1) : ℚ) := by
    rw [integerDuplicateH_cast z i (k + 1) hk, duplicateH]
    simp only [integerNewtonNumerator, Int.cast_sum, Int.cast_mul, Int.cast_add,
      Int.cast_pow, hc, Algebra.smul_def, algebraMap_self]
    have hne : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp [hne]
  exact_mod_cast hQ

theorem integerNewtonNumerator_divisible (z : Fin 9 → ℤ) (i : Fin 9) (k : ℕ)
    (hk : k + 1 ≤ 6) : (k + 1 : ℤ) ∣ integerNewtonNumerator z i k :=
  ⟨integerDuplicateH z i (k + 1), integerNewtonNumerator_spec z i k hk⟩

theorem binomial_normalization (k : ℕ) :
    ((9 + k).choose k : ℚ) * k.factorial * 9.factorial =
      ((9 + k).factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 9 + k) (k := k) (by omega)
  have hs : 9 + k - k = 9 := by omega
  rw [hs] at h
  exact_mod_cast h

theorem integral_bary_interpolate_power (y : Fin 9 → ℝ) (i : Fin 9) (k : ℕ)
    (hk : k ≤ 6) :
    (∫ x in canonical, bary i x * interpolate y x ^ k) =
      duplicateH y i k /
        ((9.factorial : ℝ) * ((9 + k).choose k : ℝ)) := by
  classical
  let S := Finset.piAntidiag (Finset.univ : Finset (Fin 9)) k
  let term (e : Fin 9 → ℕ) (x : Point) :=
    ((Nat.multinomial Finset.univ e : ℝ) * ∏ r : Fin 9, y r ^ e r) *
      ∏ r : Fin 9, bary r x ^ bumped e i r
  have hi (e : Fin 9 → ℕ) : IntegrableOn (term e) canonical := by
    apply ContinuousOn.integrableOn_compact canonical_compact
    apply Continuous.continuousOn
    apply continuous_const.mul
    exact continuous_finsetProd _ fun r _ => (bary_continuous r).pow _
  have he (x : Point) : bary i x * interpolate y x ^ k = ∑ e ∈ S, term e x := by
    rw [interpolate, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [term, mul_pow, Finset.prod_mul_distrib, bary_bumped]
    ring
  have hint : (∫ x in canonical, bary i x * interpolate y x ^ k) =
      ∑ e ∈ S, ((Nat.multinomial Finset.univ e : ℝ) *
        (baryCoefficient (bumped e i) : ℝ)) * ∏ r : Fin 9, y r ^ e r := by
    simp_rw [he]
    rw [integral_finsetSum S (fun e _ => hi e)]
    apply Finset.sum_congr rfl
    intro e _
    rw [show term e = fun x =>
        ((Nat.multinomial Finset.univ e : ℝ) * ∏ r : Fin 9, y r ^ e r) *
          ∏ r : Fin 9, bary r x ^ bumped e i r from rfl,
      integral_const_mul]
    rw [show (∫ x in canonical, ∏ r : Fin 9, bary r x ^ bumped e i r) =
      baryMoment (bumped e i) from rfl, ← baryCoefficient_cast]
    ring
  rw [hint]
  exact integratedPower_newton_guard y i k hk

/-- The actual gap-weighted degree-k polynomial integral; the original
nine-vertex gap weights are retained independently of the node values. -/
theorem integral_interpolate_mul_power (g y : Fin 9 → ℝ) (k : ℕ) (hk : k ≤ 6) :
    (∫ x in canonical, interpolate g x * interpolate y x ^ k) =
      (∑ i : Fin 9, g i * duplicateH y i k) /
        ((9.factorial : ℝ) * ((9 + k).choose k : ℝ)) := by
  have hi (i : Fin 9) : IntegrableOn
      (fun x => g i * (bary i x * interpolate y x ^ k)) canonical :=
    (continuous_const.mul ((bary_continuous i).mul
      ((interpolate_continuous y).pow k))).continuousOn.integrableOn_compact
        canonical_compact
  have he (x : Point) : interpolate g x * interpolate y x ^ k =
      ∑ i : Fin 9, g i * (bary i x * interpolate y x ^ k) := by
    simp only [interpolate, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [integral_const_mul, integral_bary_interpolate_power y _ k hk]
  simp [mul_div_assoc, Finset.sum_div]

theorem scaledDeviation_interpolate (v : Fin 9 → Point) (top : ℝ)
    (j : Fin 10) (x : Point) :
    scaledDeviation top (fun t => factors t j) (pointInterpolate v x) =
      interpolate (fun i => 1 - factors (v i) j / top) x := by
  simp only [scaledDeviation, factors_interpolate, interpolate_sub,
    interpolate_const, interpolate_div]

/-- Analytic output on a genuine physical simplex. Its input contains
only invertibility, the literal physical vertex inequalities and G>0. -/
theorem physical_power_moment (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i))
    (hG : 0 < gapTotal (vertices L b)) (top : ℝ) (j : Fin 10)
    (k : ℕ) (hk : k ≤ 6) :
    (∫ t, scaledDeviation top (fun t => factors t j) t ^ k
      ∂simplexProbability L b) =
      realMoment (fun i => gap (vertices L b i))
        (fun i => 1 - factors (vertices L b i) j / top) k := by
  rw [simplexProbability, integral_weightedProbability _ _ continuous_gap.measurable
    (simplex_gap_nonneg L b hv) (gap_mass_pos L b hG)]
  change (∫ t in support L b, gap t *
      scaledDeviation top (fun t => factors t j) t ^ k) /
      (∫ t in support L b, gap t) = _
  rw [integral_support]
  simp_rw [← vertices_interpolate L b, gap_interpolate, scaledDeviation_interpolate]
  rw [integral_interpolate_mul_power _ _ k hk, integral_gap]
  have hJ : jacobian L ≠ 0 := (jacobian_pos L).ne'
  have hc : ((9 + k).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ 9 + k)).ne'
  unfold realMoment physicalVolume gapTotal at *
  norm_num
  field_simp [hJ, hG.ne', hc]
  ring

/-! Integer/common-denominator compatibility. The source below proves
homogeneity for every k, so clearing a denominator is algebra, not an
assumed agreement between two numerical evaluators. -/

theorem duplicateH_scale {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 9 → A) (i : Fin 9) (c : A) (k : ℕ) :
    duplicateH (fun r => c * y r) i k = c ^ k * duplicateH y i k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [duplicateH]
    | succ k =>
      rw [duplicateH, duplicateH]
      simp_rw [mul_pow]
      simp only [← Finset.mul_sum, ← mul_add]
      rw [mul_smul_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (k - j.val) (by omega)]
      have hj : j.val + 1 + (k - j.val) = k + 1 := by omega
      calc
        _ = (c ^ (j.val + 1) * c ^ (k - j.val)) *
            (((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
              duplicateH y i (k - j.val)) := by ring
        _ = _ := by rw [← pow_add, hj]

theorem rationalMoment_common_denominator (g z : Fin 9 → ℚ) (d : ℚ)
    (hd : d ≠ 0) (k : ℕ) :
    rationalMoment g (fun i => z i / d) k =
      (∑ i : Fin 9, g i * duplicateH z i k) /
        ((∑ i : Fin 9, g i) * ((9 + k).choose k : ℚ) * d ^ k) := by
  have hh (i : Fin 9) : duplicateH (fun r => z r / d) i k =
      (d ^ k)⁻¹ * duplicateH z i k := by
    simpa [div_eq_mul_inv, mul_comm, inv_pow] using duplicateH_scale z i d⁻¹ k
  unfold rationalMoment
  simp_rw [hh]
  simp only [inv_pow]
  rw [show (∑ i : Fin 9, g i * ((d ^ k)⁻¹ * duplicateH z i k)) =
      (∑ i : Fin 9, g i * duplicateH z i k) * (d ^ k)⁻¹ by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Multiplying all gap weights by a common denominator cancels. -/
theorem rationalMoment_gap_scale (g y : Fin 9 → ℚ) (c : ℚ)
    (hc : c ≠ 0) (k : ℕ) :
    rationalMoment (fun i => c * g i) y k = rationalMoment g y k := by
  unfold rationalMoment
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- Original integer interface. `z_i=U-v_i`, `d=U` in the author
engine, or the lcm of normalized-deviation denominators in the
independent Newton engine. No divisibility test is silently imported. -/
def integerScaledMoment (g z : Fin 9 → ℤ) (d : ℤ) (k : ℕ) : ℚ :=
  (∑ i : Fin 9, (g i : ℚ) * duplicateH (fun r => (z r : ℚ)) i k) /
    ((∑ i : Fin 9, (g i : ℚ)) * ((9 + k).choose k : ℚ) * (d : ℚ) ^ k)

theorem integerScaledMoment_eq (g z : Fin 9 → ℤ) (d : ℤ)
    (hd : d ≠ 0) (k : ℕ) :
    integerScaledMoment g z d k =
      rationalMoment (fun i => (g i : ℚ)) (fun i => (z i : ℚ) / (d : ℚ)) k := by
  symm
  exact rationalMoment_common_denominator _ _ _ (by exact_mod_cast hd) k

/-- No integral occurs in this replacement row boundary. The first
moment keeps K's finite mean/top encoding; degrees2..6 are the actual
duplicated-node rational computation from the SAME physical vertices. -/
structure AlgebraicMomentRow where
  linear : Point ≃L[ℝ] Point
  base : Point
  physicalVertices : ∀ i, PhysicalRows (vertices linear base i)
  positiveGapTotal : 0 < gapTotal (vertices linear base)
  massQ : ℚ
  meansQ : Fin 10 → ℚ
  topsQ : Fin 10 → ℚ
  momentsQ : Fin 10 → ℕ → ℚ
  gapsQ : Fin 9 → ℚ
  factorsQ : Fin 9 → Fin 10 → ℚ
  massEncoding : (massQ : ℝ) = physicalVolume linear * gapTotal (vertices linear base) / 9
  meansEncoding : ∀ j, (meansQ j : ℝ) = factorMean (vertices linear base) j
  topsEncoding : ∀ j, (topsQ j : ℝ) = vertexTop (vertices linear base) j
  gapsEncoding : ∀ i, (gapsQ i : ℝ) = gap (vertices linear base i)
  factorsEncoding : ∀ i j, (factorsQ i j : ℝ) = factors (vertices linear base i) j
  firstMomentEncoding : ∀ j, momentsQ j 1 = 1 - meansQ j / topsQ j
  higherMomentEncoding : ∀ j k, 2 ≤ k → k ≤ 6 →
    momentsQ j k = rationalMoment gapsQ (fun i => 1 - factorsQ i j / topsQ j) k

theorem higherPowerMoments_of_encoding (r : AlgebraicMomentRow)
    (j : Fin 10) (k : ℕ) (hk : 2 ≤ k) (hk6 : k ≤ 6) :
    (r.momentsQ j k : ℝ) = ∫ t,
      scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j) t ^ k
        ∂simplexProbability r.linear r.base := by
  rw [r.higherMomentEncoding j k hk hk6, rationalMoment_cast,
    physical_power_moment r.linear r.base r.physicalVertices
      r.positiveGapTotal (r.topsQ j : ℝ) j k hk6]
  congr 1
  · funext i
    exact r.gapsEncoding i
  · funext i
    push_cast
    rw [r.factorsEncoding i j]

/-- The old analytic field is now filled by the theorem above. -/
def AlgebraicMomentRow.toMomentRow (r : AlgebraicMomentRow) : MomentRow where
  linear := r.linear
  base := r.base
  physicalVertices := r.physicalVertices
  positiveGapTotal := r.positiveGapTotal
  massQ := r.massQ
  meansQ := r.meansQ
  topsQ := r.topsQ
  momentsQ := r.momentsQ
  massEncoding := r.massEncoding
  meansEncoding := r.meansEncoding
  topsEncoding := r.topsEncoding
  firstMomentEncoding := r.firstMomentEncoding
  higherPowerMoments := higherPowerMoments_of_encoding r

theorem algebraicRowFloor_sound (r : AlgebraicMomentRow) :
    (originalRowFloor r.toMomentRow : ℝ) ≤
      ∫ t in support r.linear r.base, conservativeDensity t :=
  originalRowFloor_sound r.toMomentRow

end

end ImbalancedChen.P2OriginalSaving19HigherMoments
