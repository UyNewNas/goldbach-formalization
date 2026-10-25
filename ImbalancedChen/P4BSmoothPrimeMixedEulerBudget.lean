import ImbalancedChen.P4BSmoothPrimeEulerAllOrders
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum

/-!
# Full mixed Euler jets of the original prime-variable four-wall profile

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-25).

The actual directional supplier retains its width-sensitive finite derivative
budget. Its finite envelope is converted below to a fixed-width bound before
the native Fréchet composition estimate is applied. Each native iterated
Fréchet derivative controls every mixed Euler partial of the actual
multiplicative chart.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped BigOperators ContDiff

/-- The chart in which coordinate partial derivatives are the genuine
commuting Euler derivatives of the original positive prime variables. -/
def smoothPrimeEulerChart (b : ℝ) (N : ℕ) (T width : ℝ)
    (p z : Fin 2 → ℝ) : ℝ :=
  smoothPrimeVariableProfile b N T width
    (fun i => p i * Real.exp (z i))

def primeEulerLogAffine (N : ℕ) (p z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  primeVariableLogPoint N p + (Real.log (N : ℝ))⁻¹ • z

theorem smoothPrimeEulerChart_eq_physicalProfile
    (b : ℝ) (N : ℕ) (T width : ℝ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) (z : Fin 2 → ℝ) :
    smoothPrimeEulerChart b N T width p z =
      smoothPhysicalProfile b N T width (primeEulerLogAffine N p z) := by
  have h := primeVariableLogPoint_primeEulerOrbit N hp z 1
  have horbit : primeEulerOrbit p z 1 = fun i => p i * Real.exp (z i) := by
    funext i
    simp [primeEulerOrbit]
  have hscale : (fun i : Fin 2 => z i / Real.log (N : ℝ)) =
      (Real.log (N : ℝ))⁻¹ • z := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [horbit, one_smul, hscale] at h
  exact congrArg (smoothPhysicalProfile b N T width) h

/-- The actual affine row after the normalized-log Euler change of
variables. The fourth physical wall's log N factor is retained. -/
def smoothEulerWallRow (b : ℝ) (N : ℕ) (i : Fin 4) :
    (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (Real.log (N : ℝ))⁻¹ • smoothPhysicalWallRow b N i

def smoothEulerWallMargin (b : ℝ) (N : ℕ) (T : ℝ)
    (p : Fin 2 → ℝ) (i : Fin 4) (z : Fin 2 → ℝ) : ℝ :=
  smoothPhysicalProfileMargin b N T (primeEulerLogAffine N p z) i

theorem smoothEulerWallMargin_eq_offset_add_row
    (b : ℝ) (N : ℕ) (T : ℝ) (p : Fin 2 → ℝ)
    (i : Fin 4) (z : Fin 2 → ℝ) :
    smoothEulerWallMargin b N T p i z =
      smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i +
        smoothEulerWallRow b N i z := by
  change smoothPhysicalProfileMargin b N T
    (primeVariableLogPoint N p + (Real.log (N : ℝ))⁻¹ • z) i = _
  rw [smoothPhysicalProfileMargin_line]
  simp [smoothEulerWallRow, smul_eq_mul]

theorem contDiff_smoothEulerWallMargin
    (b : ℝ) (N : ℕ) (T : ℝ) (p : Fin 2 → ℝ) (i : Fin 4) :
    ContDiff ℝ ∞ (smoothEulerWallMargin b N T p i) := by
  have h : ContDiff ℝ ∞ (fun z : Fin 2 → ℝ =>
      smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i +
        smoothEulerWallRow b N i z) :=
    contDiff_const.add (smoothEulerWallRow b N i).contDiff
  simpa only [smoothEulerWallMargin_eq_offset_add_row] using h

theorem fderiv_smoothEulerWallMargin
    (b : ℝ) (N : ℕ) (T : ℝ) (p z : Fin 2 → ℝ) (i : Fin 4) :
    fderiv ℝ (smoothEulerWallMargin b N T p i) z =
      smoothEulerWallRow b N i := by
  have h : HasFDerivAt (fun w : Fin 2 → ℝ =>
      smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i +
        smoothEulerWallRow b N i w) (smoothEulerWallRow b N i) z :=
    (smoothEulerWallRow b N i).hasFDerivAt.const_add _
  have heq : smoothEulerWallMargin b N T p i = fun w : Fin 2 → ℝ =>
      smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i +
        smoothEulerWallRow b N i w := by
    funext w
    exact smoothEulerWallMargin_eq_offset_add_row b N T p i w
  rw [heq]
  exact h.fderiv

/-- One fixed bound for every transformed wall row and every N>=2.
The inverse log N exactly pays for the physical upper wall's log N. -/
theorem smoothEulerWallRow_norm_le
    (b : ℝ) (N : ℕ) (hN : 2 ≤ N) (i : Fin 4) :
    ‖smoothEulerWallRow b N i‖ ≤
      (2 + |b|) * (1 + 1 / Real.log 2) := by
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le htwo (Real.log_le_log (by norm_num) hNreal)
  have hratio : (1 + Real.log (N : ℝ)) / Real.log (N : ℝ) ≤
      1 + 1 / Real.log 2 := by
    have hrecip : 1 / Real.log (N : ℝ) ≤ 1 / Real.log 2 :=
      div_le_div_of_nonneg_left (by norm_num) htwo
        (Real.log_le_log (by norm_num) hNreal)
    have hid : (1 + Real.log (N : ℝ)) / Real.log (N : ℝ) =
        1 + 1 / Real.log (N : ℝ) := by
      field_simp [hlogN.ne']
      ring
    rw [hid]
    exact add_le_add_left hrecip 1
  have hb : 0 ≤ 2 + |b| := by positivity
  rw [smoothEulerWallRow, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hlogN)]
  calc
    (Real.log (N : ℝ))⁻¹ * ‖smoothPhysicalWallRow b N i‖ ≤
        (Real.log (N : ℝ))⁻¹ *
          ((2 + |b|) * (1 + Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (smoothPhysicalWallRow_norm_le b N hN i)
        (inv_nonneg.mpr hlogN.le)
    _ = (2 + |b|) * ((1 + Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
      ring
    _ ≤ (2 + |b|) * (1 + 1 / Real.log 2) :=
      mul_le_mul_of_nonneg_left hratio hb

/-- The affine inner map has only one nonzero positive derivative order.
This is proved from the actual constant Fréchet derivative. -/
theorem norm_iteratedFDeriv_smoothEulerWallMargin_le_pow
    (b : ℝ) (N : ℕ) (T : ℝ) (p z : Fin 2 → ℝ) (i : Fin 4)
    (j : ℕ) (hj : 1 ≤ j) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ‖smoothEulerWallRow b N i‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (smoothEulerWallMargin b N T p i) z‖ ≤ R ^ j := by
  have hderiv : fderiv ℝ (smoothEulerWallMargin b N T p i) =
      fun _ => smoothEulerWallRow b N i := by
    funext w
    exact fderiv_smoothEulerWallMargin b N T p w i
  cases j with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      simpa only [norm_iteratedFDeriv_one, pow_one, hderiv] using hrow
    | succ n =>
      have hz : iteratedFDeriv ℝ (n + 1 + 1)
          (smoothEulerWallMargin b N T p i) z = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_right, hderiv]
        simp [iteratedFDeriv_succ_const]
      rw [hz, norm_zero]
      exact pow_nonneg hR _

/-- Native all-order composition estimate for one genuine smooth gate.
The factorial is paid once at the chosen order; no derivative bound is a
premise of the theorem. -/
theorem norm_iteratedFDeriv_smoothEulerWallFactor_le
    (k : ℕ) (b width : ℝ) (hwidth : 0 < width)
    (B : ℝ) (hB : 0 ≤ B)
    (hscalar : ∀ j : ℕ, j ≤ k → ∀ y : ℝ,
      |iteratedDeriv j (smoothGateUpperStep width) y| ≤ B)
    (N : ℕ) (hN : 2 ≤ N) (T : ℝ) (p z : Fin 2 → ℝ)
    (i : Fin 4) (j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j
      (fun w : Fin 2 → ℝ =>
        smoothGateUpperStep width (smoothEulerWallMargin b N T p i w)) z‖ ≤
      ((k.factorial : ℝ) * B) *
        ((2 + |b|) * (1 + 1 / Real.log 2)) ^ j := by
  let R : ℝ := (2 + |b|) * (1 + 1 / Real.log 2)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hR : 0 ≤ R :=
    mul_nonneg (by positivity) (add_nonneg zero_le_one
      (div_nonneg zero_le_one hlog2.le))
  have hinner : ContDiff ℝ ∞ (smoothEulerWallMargin b N T p i) :=
    contDiff_smoothEulerWallMargin b N T p i
  have houter : ContDiff ℝ ∞ (smoothGateUpperStep width) :=
    contDiff_smoothGateUpperStep width
  have hC (m : ℕ) (hm : m ≤ j) :
      ‖iteratedFDeriv ℝ m (smoothGateUpperStep width)
        (smoothEulerWallMargin b N T p i z)‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      using hscalar m (hm.trans hj) _
  have hD (m : ℕ) (hm : 1 ≤ m) (_hmj : m ≤ j) :
      ‖iteratedFDeriv ℝ m (smoothEulerWallMargin b N T p i) z‖ ≤ R ^ m :=
    norm_iteratedFDeriv_smoothEulerWallMargin_le_pow b N T p z i m hm
      R hR (smoothEulerWallRow_norm_le b N hN i)
  have hcomp := norm_iteratedFDeriv_comp_le houter hinner
    (by simp : (j : ℕ∞ω) ≤ ∞) z hC hD
  have hfac : (j.factorial : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  calc
    _ ≤ (j.factorial : ℝ) * B * R ^ j := by
      simpa only [Function.comp_def] using hcomp
    _ ≤ ((k.factorial : ℝ) * B) * R ^ j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR j)
      exact mul_le_mul_of_nonneg_right hfac hB

/-- A binomial Leibniz bound for native iterated Fréchet derivatives. -/
theorem norm_iteratedFDeriv_two_product_le
    (k : ℕ) (f g : (Fin 2 → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (z : Fin 2 → ℝ) (R Cf Cg : ℝ)
    (hR : 0 ≤ R) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hleft : ∀ j : ℕ, j ≤ k →
      ‖iteratedFDeriv ℝ j f z‖ ≤ Cf * R ^ j)
    (hright : ∀ j : ℕ, j ≤ k →
      ‖iteratedFDeriv ℝ j g z‖ ≤ Cg * R ^ j) :
    ‖iteratedFDeriv ℝ k (fun w => f w * g w) z‖ ≤
      Cf * Cg * (2 * R) ^ k := by
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j f z‖ *
          ‖iteratedFDeriv ℝ (k - j) g z‖ :=
      norm_iteratedFDeriv_mul_le hf hg z (by simp)
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (Cf * Cg * R ^ k) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hp : ‖iteratedFDeriv ℝ j f z‖ *
          ‖iteratedFDeriv ℝ (k - j) g z‖ ≤
          (Cf * R ^ j) * (Cg * R ^ (k - j)) :=
        mul_le_mul (hleft j hjk) (hright (k - j) (Nat.sub_le k j))
          (norm_nonneg _) (mul_nonneg hCf (pow_nonneg hR j))
      calc
        _ = (k.choose j : ℝ) *
            (‖iteratedFDeriv ℝ j f z‖ *
              ‖iteratedFDeriv ℝ (k - j) g z‖) := by ring
        _ ≤ (k.choose j : ℝ) *
            ((Cf * R ^ j) * (Cg * R ^ (k - j))) :=
          mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
        _ = (k.choose j : ℝ) * (Cf * Cg * (R ^ j * R ^ (k - j))) := by
          ring
        _ = (k.choose j : ℝ) * (Cf * Cg * R ^ k) := by
          rw [← pow_add, Nat.add_sub_of_le hjk]
    _ = 2 ^ k * (Cf * Cg * R ^ k) := by rw [← Finset.sum_mul, hsum]
    _ = Cf * Cg * (2 * R) ^ k := by rw [mul_pow]; ring

/-- Four actual factors, with a native mixed-jet norm rather than only
diagonal directional evaluations. -/
theorem norm_iteratedFDeriv_four_product_le
    (k : ℕ) (f : Fin 4 → (Fin 2 → ℝ) → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (z : Fin 2 → ℝ)
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hfactor : ∀ i : Fin 4, ∀ j : ℕ, j ≤ k →
      ‖iteratedFDeriv ℝ j (f i) z‖ ≤ B * R ^ j) :
    ‖iteratedFDeriv ℝ k (fun w => ∏ i : Fin 4, f i w) z‖ ≤
      B ^ 4 * (4 * R) ^ k := by
  let g0 : (Fin 2 → ℝ) → ℝ := fun w => f 0 w * f 1 w
  let g1 : (Fin 2 → ℝ) → ℝ := fun w => f 2 w * f 3 w
  have hg0 : ContDiff ℝ ∞ g0 := (hf 0).mul (hf 1)
  have hg1 : ContDiff ℝ ∞ g1 := (hf 2).mul (hf 3)
  have hpair0 (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j g0 z‖ ≤ (B * B) * (2 * R) ^ j :=
    norm_iteratedFDeriv_two_product_le j (f 0) (f 1) (hf 0) (hf 1)
      z R B B hR hB hB
      (fun m hm => hfactor 0 m (hm.trans hj))
      (fun m hm => hfactor 1 m (hm.trans hj))
  have hpair1 (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j g1 z‖ ≤ (B * B) * (2 * R) ^ j :=
    norm_iteratedFDeriv_two_product_le j (f 2) (f 3) (hf 2) (hf 3)
      z R B B hR hB hB
      (fun m hm => hfactor 2 m (hm.trans hj))
      (fun m hm => hfactor 3 m (hm.trans hj))
  have hprod : (fun w => ∏ i : Fin 4, f i w) = fun w => g0 w * g1 w := by
    funext w
    rw [Fin.prod_univ_four]
    dsimp [g0, g1]
    ring
  rw [hprod]
  have hfinal := norm_iteratedFDeriv_two_product_le k g0 g1 hg0 hg1
    z (2 * R) (B * B) (B * B) (mul_nonneg (by norm_num) hR)
    (mul_nonneg hB hB) (mul_nonneg hB hB) hpair0 hpair1
  simpa only [show (B * B) * (B * B) = B ^ 4 by ring,
    show (2 : ℝ) * (2 * R) = 4 * R by ring] using hfinal

/-- A scalar derivative envelope whose constant is selected before width,
derived directly from the actual width^-j finite derivative supplier. -/
theorem exists_smoothGateUpperStep_width_envelope (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ width : ℝ, 0 < width →
      ∀ j : ℕ, j ≤ k → ∀ y : ℝ,
        |iteratedDeriv j (smoothGateUpperStep width) y| ≤
          A * (1 + width⁻¹) ^ k := by
  obtain ⟨A, hA, hbudget⟩ :=
    exists_smoothGateUpperStep_finite_derivative_budget k
  refine ⟨A, hA, ?_⟩
  intro width hwidth j hj y
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hinv : 0 ≤ width⁻¹ := (inv_pos.mpr hwidth).le
  have hbase : 1 ≤ 1 + width⁻¹ := by linarith
  calc
    _ ≤ A / width ^ j := hbudget j hj width hwidth y
    _ = A * (width⁻¹) ^ j := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ A * (1 + width⁻¹) ^ j :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hinv (by linarith) j) hA0
    _ ≤ A * (1 + width⁻¹) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hj) hA0

/-- The full native mixed Euler jet is uniformly bounded at every order.
For each fixed k, b and width, C is chosen before N, T, p, and z. Since
the operator norm controls all tuple evaluations, every mixed coordinate
Euler partial of total order k obeys the same bound. -/
theorem exists_smoothPrimeEulerChart_all_mixed_budget
    (k : ℕ) (b width : ℝ) (hwidth : 0 < width) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ p z : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
        ‖iteratedFDeriv ℝ k (smoothPrimeEulerChart b N T width p) z‖ ≤ C := by
  obtain ⟨A, hA, hscalarA⟩ := exists_smoothGateUpperStep_width_envelope k
  let B : ℝ := A * (1 + width⁻¹) ^ k
  have hbase : 0 ≤ 1 + width⁻¹ :=
    add_nonneg zero_le_one (inv_pos.mpr hwidth).le
  have hB : 0 ≤ B := mul_nonneg (zero_le_one.trans hA) (pow_nonneg hbase k)
  have hscalar (j : ℕ) (hj : j ≤ k) (y : ℝ) :
      |iteratedDeriv j (smoothGateUpperStep width) y| ≤ B :=
    hscalarA width hwidth j hj y
  let R : ℝ := (2 + |b|) * (1 + 1 / Real.log 2)
  let Q : ℝ := (k.factorial : ℝ) * B
  let C : ℝ := Q ^ 4 * (4 * R) ^ k
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hR : 0 ≤ R :=
    mul_nonneg (by positivity) (add_nonneg zero_le_one
      (div_nonneg zero_le_one hlog2.le))
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) hB
  have hC : 0 ≤ C :=
    mul_nonneg (pow_nonneg hQ 4)
      (pow_nonneg (mul_nonneg (by norm_num) hR) k)
  refine ⟨C, hC, ?_⟩
  intro N hN T p z hp
  let f : Fin 4 → (Fin 2 → ℝ) → ℝ := fun i w =>
    smoothGateUpperStep width (smoothEulerWallMargin b N T p i w)
  have hf (i : Fin 4) : ContDiff ℝ ∞ (f i) :=
    (contDiff_smoothGateUpperStep width).comp
      (contDiff_smoothEulerWallMargin b N T p i)
  have hfactor (i : Fin 4) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (f i) z‖ ≤ Q * R ^ j :=
    norm_iteratedFDeriv_smoothEulerWallFactor_le k b width hwidth
      B hB hscalar N hN T p z i j hj
  have hfour := norm_iteratedFDeriv_four_product_le k f hf z R Q hR hQ hfactor
  have hchart : smoothPrimeEulerChart b N T width p =
      fun w => ∏ i : Fin 4, f i w := by
    funext w
    rw [smoothPrimeEulerChart_eq_physicalProfile b N T width hp w]
    rfl
  rw [hchart]
  exact hfour

/-- Every ordered tuple of coordinate Euler directions, including mixed
orders and repeated coordinates, is controlled by the same fixed-order
constant. Taking each direction to be a coordinate unit vector gives the
ordinary mixed Euler partial bound. -/
theorem exists_smoothPrimeEulerChart_all_mixed_evaluations_budget
    (k : ℕ) (b width : ℝ) (hwidth : 0 < width) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ p z : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
      ∀ directions : Fin k → (Fin 2 → ℝ),
        ‖(iteratedFDeriv ℝ k (smoothPrimeEulerChart b N T width p) z)
          directions‖ ≤ C * ∏ j : Fin k, ‖directions j‖ := by
  obtain ⟨C, hC, hbudget⟩ :=
    exists_smoothPrimeEulerChart_all_mixed_budget k b width hwidth
  refine ⟨C, hC, ?_⟩
  intro N hN T p z hp directions
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (smoothPrimeEulerChart b N T width p) z‖ *
        ∏ j : Fin k, ‖directions j‖ :=
      (iteratedFDeriv ℝ k (smoothPrimeEulerChart b N T width p) z).le_opNorm
        directions
    _ ≤ C * ∏ j : Fin k, ‖directions j‖ :=
      mul_le_mul_of_nonneg_right (hbudget N hN T p z hp)
        (Finset.prod_nonneg (fun j _ => norm_nonneg (directions j)))

/-- Explicit width-sensitive native mixed Euler budget. The constant
depends only on order and b. A width of size (log N)^(-B) therefore costs
a fixed polylogarithmic power 4*k*B, with no hidden N dependence. -/
theorem exists_smoothPrimeEulerChart_explicit_width_mixed_budget
    (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ p z : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
        ‖iteratedFDeriv ℝ k (smoothPrimeEulerChart b N T width p) z‖ ≤
          C * (1 + width⁻¹) ^ (4 * k) := by
  obtain ⟨A, hA, hscalarA⟩ := exists_smoothGateUpperStep_width_envelope k
  let R : ℝ := (2 + |b|) * (1 + 1 / Real.log 2)
  let C : ℝ := (((k.factorial : ℝ) * A) ^ 4) * (4 * R) ^ k
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hR : 0 ≤ R :=
    mul_nonneg (by positivity) (add_nonneg zero_le_one
      (div_nonneg zero_le_one hlog2.le))
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hC : 0 ≤ C :=
    mul_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hA0) 4)
      (pow_nonneg (mul_nonneg (by norm_num) hR) k)
  refine ⟨C, hC, ?_⟩
  intro width hwidth N hN T p z hp
  let S : ℝ := 1 + width⁻¹
  let B : ℝ := A * S ^ k
  let Q : ℝ := (k.factorial : ℝ) * B
  have hS : 0 ≤ S := by
    dsimp [S]
    have hi : 0 ≤ width⁻¹ := (inv_pos.mpr hwidth).le
    linarith
  have hB : 0 ≤ B := mul_nonneg hA0 (pow_nonneg hS k)
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) hB
  have hscalar (j : ℕ) (hj : j ≤ k) (y : ℝ) :
      |iteratedDeriv j (smoothGateUpperStep width) y| ≤ B :=
    hscalarA width hwidth j hj y
  let f : Fin 4 → (Fin 2 → ℝ) → ℝ := fun i w =>
    smoothGateUpperStep width (smoothEulerWallMargin b N T p i w)
  have hf (i : Fin 4) : ContDiff ℝ ∞ (f i) :=
    (contDiff_smoothGateUpperStep width).comp
      (contDiff_smoothEulerWallMargin b N T p i)
  have hfactor (i : Fin 4) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (f i) z‖ ≤ Q * R ^ j :=
    norm_iteratedFDeriv_smoothEulerWallFactor_le k b width hwidth
      B hB hscalar N hN T p z i j hj
  have hfour := norm_iteratedFDeriv_four_product_le k f hf z R Q hR hQ hfactor
  have hchart : smoothPrimeEulerChart b N T width p =
      fun w => ∏ i : Fin 4, f i w := by
    funext w
    rw [smoothPrimeEulerChart_eq_physicalProfile b N T width hp w]
    rfl
  rw [← hchart] at hfour
  calc
    _ ≤ Q ^ 4 * (4 * R) ^ k := hfour
    _ = C * S ^ (4 * k) := by
      dsimp [Q, B, C]
      rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm k 4]
      ring

end

end ImbalancedChen.P4B
