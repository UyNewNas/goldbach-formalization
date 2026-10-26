import ImbalancedChen.P5ZU1011AdoptedRowSmoothTensor
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual finite adopted-row smoothing and its arithmetic error norm. The
reserve is evaluated at EVERY original arithmetic point with its original
reciprocal-phi weight, including prime points on row walls. Its fixed-width
limit is a genuine continuous-test integral. No arbitrary boundary-null
shortcut, strong distribution licence, or enhanced sieve density is used.
The remaining thin-reserve integral estimate is deliberately not assumed.
-/
namespace ImbalancedChen.P5Z.U1011AdoptedMaskSmoothArithmeticError
noncomputable section
open Set Filter Topology MeasureTheory Classical
open scoped BigOperators
open Certificates.PairedV2
open U1011CompactLogIntervalSmoothing U1011AdoptedRowSmoothTensor

def maskIndicator (S : Finset Row) (x : ℝ × ℝ) : ℝ :=
  if ∃ r ∈ S, x ∈ FullMask.P1E0E1.pairCell r then 1 else 0

def smoothMask (S : Finset Row) (inner : Bool) (δ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ r ∈ S, atom inner δ r x

def reserve (S : Finset Row) (δ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ r ∈ S, (atom false δ r x - atom true δ r x)

theorem maskIndicator_eq_row_sum (S : Finset Row) (x : ℝ × ℝ) :
    maskIndicator S x = ∑ r ∈ S, rowIndicator r x := by
  by_cases hex : ∃ r ∈ S, x ∈ FullMask.P1E0E1.pairCell r
  · obtain ⟨r, hr, hx⟩ := hex
    rw [maskIndicator, if_pos ⟨r, hr, hx⟩]
    symm
    calc
      _ = rowIndicator r x := by
        apply Finset.sum_eq_single r
        · intro s hs hsr
          have hn : x ∉ FullMask.P1E0E1.pairCell s :=
            fun h => hsr (FullMask.P1E0E1.pairCell_unique_owner h hx)
          simp [rowIndicator, hn]
        · intro hn
          exact (hn hr).elim
      _ = 1 := by simp [rowIndicator, hx]
  · rw [maskIndicator, if_neg hex]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hn : x ∉ FullMask.P1E0E1.pairCell r := fun h => hex ⟨r, hr, h⟩
    simp [rowIndicator, hn]

theorem mask_sandwich {δ : ℝ} (hδ : 0 < δ) (S : Finset Row) (x : ℝ × ℝ) :
    smoothMask S true δ x ≤ maskIndicator S x ∧
      maskIndicator S x ≤ smoothMask S false δ x := by
  rw [maskIndicator_eq_row_sum]
  exact ⟨Finset.sum_le_sum (fun r _ => inner_le_row hδ r x),
    Finset.sum_le_sum (fun r _ => row_le_outer hδ r x)⟩

theorem reserve_eq_difference (S : Finset Row) (δ : ℝ) (x : ℝ × ℝ) :
    reserve S δ x = smoothMask S false δ x - smoothMask S true δ x := by
  simp only [reserve, smoothMask, Finset.sum_sub_distrib]

theorem reserve_nonneg {δ : ℝ} (hδ : 0 < δ) (S : Finset Row) (x : ℝ × ℝ) :
    0 ≤ reserve S δ x := by
  rw [reserve_eq_difference]
  exact sub_nonneg.mpr ((mask_sandwich hδ S x).1.trans (mask_sandwich hδ S x).2)

theorem mask_error_le_reserve {δ : ℝ} (hδ : 0 < δ)
    (S : Finset Row) (inner : Bool) (x : ℝ × ℝ) :
    |maskIndicator S x - smoothMask S inner δ x| ≤ reserve S δ x := by
  obtain ⟨hl, hu⟩ := mask_sandwich hδ S x
  rw [reserve_eq_difference, abs_le]
  cases inner <;> constructor <;> linarith

def rowBoundary (δ : ℝ) (r : Row) (x : ℝ × ℝ) : Prop :=
  innerReserve δ (loT r) (hiT r) x.1 ∨ outerReserve δ (loT r) (hiT r) x.1 ∨
    innerReserve δ (loU r) (hiU r) x.2 ∨ outerReserve δ (loU r) (hiU r) x.2

/-- Nonzero reserve lies in literal one-sided row strips, including the
appropriate original endpoints. This is a pointwise arithmetic statement. -/
theorem row_gap_zero_off_boundary {δ : ℝ} (hδ : 0 < δ)
    (r : Row) (x : ℝ × ℝ) (hx : ¬ rowBoundary δ r x) :
    atom false δ r x - atom true δ r x = 0 := by
  have hti : literal (loT r) (hiT r) x.1 - weight true δ (loT r) (hiT r) x.1 = 0 := by
    by_contra hn
    exact hx (Or.inl (inner_error_support hδ hn))
  have hto : weight false δ (loT r) (hiT r) x.1 - literal (loT r) (hiT r) x.1 = 0 := by
    by_contra hn
    exact hx (Or.inr (Or.inl (outer_error_support hδ hn)))
  have hui : literal (loU r) (hiU r) x.2 - weight true δ (loU r) (hiU r) x.2 = 0 := by
    by_contra hn
    exact hx (Or.inr (Or.inr (Or.inl (inner_error_support hδ hn))))
  have huo : weight false δ (loU r) (hiU r) x.2 - literal (loU r) (hiU r) x.2 = 0 := by
    by_contra hn
    exact hx (Or.inr (Or.inr (Or.inr (outer_error_support hδ hn))))
  have ht : weight false δ (loT r) (hiT r) x.1 = weight true δ (loT r) (hiT r) x.1 := by linarith
  have hu : weight false δ (loU r) (hiU r) x.2 = weight true δ (loU r) (hiU r) x.2 := by linarith
  simp only [atom, ht, hu, sub_self]

theorem reserve_support {δ : ℝ} (hδ : 0 < δ) (S : Finset Row) (x : ℝ × ℝ)
    (hx : reserve S δ x ≠ 0) : ∃ r ∈ S, rowBoundary δ r x := by
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro r hr
  exact row_gap_zero_off_boundary hδ r x (fun hb => hn ⟨r, hr, hb⟩)

def pairPoint (v : Fin 4 → ℝ) : ℝ × ℝ := (v 0, v 1)

/-- Actual signed test error with full original prime harmonic weights.
In particular, no arithmetic point on an original row wall is discarded. -/
theorem actualPrimeBox_mask_smoothing_error {δ : ℝ} (hδ : 0 < δ)
    (S : Finset Row) (inner : Bool) (N : ℕ) (a b : Fin 4 → ℝ)
    (f : (Fin 4 → ℝ) → ℝ) :
    |actualPrimeBoxTestSum N a b (fun v => f v * maskIndicator S (pairPoint v)) -
      actualPrimeBoxTestSum N a b (fun v => f v * smoothMask S inner δ (pairPoint v))| ≤
    actualPrimeBoxTestSum N a b (fun v => |f v| * reserve S δ (pairPoint v)) := by
  unfold actualPrimeBoxTestSum
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul,
    abs_of_nonneg (actualPrimeBoxWeight_nonneg hp)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mask_error_le_reserve hδ S inner _) (abs_nonneg _))
    (actualPrimeBoxWeight_nonneg hp)

theorem continuous_reserve (S : Finset Row) (δ : ℝ) : Continuous (reserve S δ) := by
  apply continuous_finsetSum
  intro r hr
  exact (contDiff_atom false δ r).continuous.sub (contDiff_atom true δ r).continuous

/-- Width and the ORIGINAL finite row set are fixed before N. This limit
controls the exact raw boundary error norm, rather than deleting its walls. -/
theorem tendsto_actualPrimeBox_reserve (S : Finset Row) (δ : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      (fun v => |f v| * reserve S δ (pairPoint v))) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)),
        (|f v| * reserve S δ (pairPoint v)) * ∏ i, 1 / v i)) := by
  apply tendsto_actualPrimeBoxTestSum_cube (by norm_num) (by norm_num)
  exact (hf.abs.mul ((continuous_reserve S δ).comp
    ((continuous_apply 0).prodMk (continuous_apply 1)))).continuousOn

/-- Continuous native increasing prime pair, read in the original
decreasing log orientation. The formula is the literal native mask map. -/
def primeLogPair (N : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.log p.2 / Real.log (N : ℝ), Real.log p.1 / Real.log (N : ℝ))

def primeWeight (inner : Bool) (δ : ℝ) (r : Row) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  atom inner δ r (primeLogPair N p)

theorem primeWeight_eq_nativeAtom (inner : Bool) (δ : ℝ) (r : Row)
    (N : ℕ) (p : ℕ × ℕ) :
    primeWeight inner δ r N ((p.1 : ℝ), (p.2 : ℝ)) = nativeAtom inner δ r N p := rfl

/-- Independent Mellin translations in the two original prime variables.
The first derivative index belongs to the larger prime, as in the mask. -/
def primeFlowJet (i j : ℕ) (inner : Bool) (δ : ℝ) (r : Row)
    (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv j (fun t => iteratedDeriv i (fun s =>
    primeWeight inner δ r N (p.1 * Real.exp t, p.2 * Real.exp s)) 0) 0

theorem primeWeight_flow {p : ℝ × ℝ} (hp : 0 < p.1 ∧ 0 < p.2)
    (inner : Bool) (δ : ℝ) (r : Row) (N : ℕ) (s t : ℝ) :
    primeWeight inner δ r N (p.1 * Real.exp t, p.2 * Real.exp s) =
      weight inner δ (loT r) (hiT r)
        ((primeLogPair N p).1 + (Real.log (N : ℝ))⁻¹ * s) *
      weight inner δ (loU r) (hiU r)
        ((primeLogPair N p).2 + (Real.log (N : ℝ))⁻¹ * t) := by
  dsimp [primeWeight, atom, primeLogPair]
  rw [Real.log_mul hp.2.ne' (Real.exp_pos s).ne', Real.log_exp,
    Real.log_mul hp.1.ne' (Real.exp_pos t).ne', Real.log_exp]
  congr 1 <;> congr 1 <;> simp only [div_eq_mul_inv] <;> ring

/-- Exact mixed Mellin-flow budget identification for actual separated
prime-log factors, including both zeroth derivative indices. -/
theorem primeFlowJet_eq_logJet {p : ℝ × ℝ} (hp : 0 < p.1 ∧ 0 < p.2)
    (i j : ℕ) (inner : Bool) (δ : ℝ) (r : Row) (N : ℕ) :
    primeFlowJet i j inner δ r N p =
      (Real.log (N : ℝ))⁻¹ ^ (i + j) * mixedJet i j inner δ r (primeLogPair N p) := by
  have ht := P4B.iteratedDeriv_comp_real_affine i
    (weight inner δ (loT r) (hiT r)) (contDiff_weight inner δ _ _)
    (primeLogPair N p).1 (Real.log (N : ℝ))⁻¹ 0
  have hu := P4B.iteratedDeriv_comp_real_affine j
    (weight inner δ (loU r) (hiU r)) (contDiff_weight inner δ _ _)
    (primeLogPair N p).2 (Real.log (N : ℝ))⁻¹ 0
  simp only [mul_zero, add_zero] at ht hu
  unfold primeFlowJet
  simp_rw [primeWeight_flow hp inner δ r N, iteratedDeriv_mul_const_field]
  rw [iteratedDeriv_const_mul_field, ht, hu, mixedJet_eq_tensor, pow_add]
  ring

/-- Genuine native mixed Euler/Mellin derivative payment. After the width
is fixed this has no positive power of log N; all native moduli remain
unchanged. This supplies derivative regularity, not distribution itself. -/
theorem exists_primeFlowJet_budget (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (inner : Bool) (δ : ℝ), 0 < δ →
      ∀ (r : Row) (N : ℕ), 2 ≤ N → ∀ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 →
      |primeFlowJet i j inner δ r N p| ≤ C / (δ * Real.log (N : ℝ)) ^ (i + j) := by
  obtain ⟨C, hC, hbound⟩ := exists_mixedJet_budget i j
  refine ⟨C, hC, ?_⟩
  intro inner δ hδ r N hN p hp
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  rw [primeFlowJet_eq_logJet hp, abs_mul, abs_pow,
    abs_of_nonneg (inv_nonneg.mpr hlog.le)]
  calc
    _ ≤ (Real.log (N : ℝ))⁻¹ ^ (i + j) * (C / δ ^ (i + j)) :=
      mul_le_mul_of_nonneg_left (hbound inner δ hδ r _)
        (pow_nonneg (inv_nonneg.mpr hlog.le) _)
    _ = C / (δ * Real.log (N : ℝ)) ^ (i + j) := by
      rw [mul_pow, inv_pow]
      ring

end
end ImbalancedChen.P5Z.U1011AdoptedMaskSmoothArithmeticError
