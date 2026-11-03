import ImbalancedChen.P5U7OriginalPhysicalPP
import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import ImbalancedChen.CurrentChenP5U9OrderedPhysicalPP
import ImbalancedChen.CurrentChenUpsilon9HarmonicMean
import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral
import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal positive outer smoothings of the original U7, U8 and U9 log walls.
The original hard source coefficients are unchanged. The U7 prime and
semiprime labels remain separate; all three U9 branch labels remain
separate. Equality at a weak terminal wall is retained by the one plateau.
The smoothing has no coprimality or primality predicate in its definition.

This supplies actual smooth logarithmic profiles and their exact plateau
on each original source. It does not assert that signed PP is monotone in
the source weight. Full-modulus boundary/centre-filter payment, physical
Euler budgets, the actual retained-mode estimate and density are separate
obligations. No desired count, PP or boundary estimate is a premise.
-/

namespace ImbalancedChen.P5OriginalU789SmoothLogSources

noncomputable section
open Classical
open scoped BigOperators
open P4B
open P5U7OriginalPhysicalPP

def logPoint {k N : ℕ} (u : Fin k → Fin (N + 1)) : Fin k → ℝ :=
  actualPrimeTupleLog N (fun i => (u i).val)

private theorem tuple_pos {k N : ℕ} {u : Fin k → Fin (N + 1)}
    (hu : u ∈ Part3.labelledPrimeTuples k N) : ∀ i, 0 < (u i).val :=
  fun i => ((Finset.mem_filter.mp hu).2 i).pos

private theorem log_floor {k N : ℕ} (hN : 2 ≤ N)
    {u : Fin k → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples k N)
    (i : Fin k) {a : ℝ} (ha : (N : ℝ) ^ a ≤ ((u i).val : ℝ)) :
    a ≤ logPoint u i := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [← Real.rpow_le_rpow_left_iff hNr]
  exact ha.trans_eq (actualPrimeTupleLog_rpow (by omega)
    (fun j => (u j).val) (tuple_pos hu) i).symm

private theorem log_ceiling {k N : ℕ} (hN : 2 ≤ N)
    {u : Fin k → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples k N)
    (i : Fin k) {a : ℝ} (ha : ((u i).val : ℝ) ≤ (N : ℝ) ^ a) :
    logPoint u i ≤ a := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [← Real.rpow_le_rpow_left_iff hNr]
  exact (actualPrimeTupleLog_rpow (by omega)
    (fun j => (u j).val) (tuple_pos hu) i).trans_le ha

private theorem log_order {k N : ℕ} (hN : 2 ≤ N)
    {u : Fin k → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples k N)
    {i j : Fin k} (hij : (u i).val ≤ (u j).val) :
    logPoint u i ≤ logPoint u j := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by exact_mod_cast tuple_pos hu i) (by exact_mod_cast hij))
    (Real.log_pos hNr).le

private theorem log_product_lt_one {k N : ℕ} (hN : 2 ≤ N)
    {u : Fin k → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples k N)
    (hp : Part3.labelledProduct u < N) : (∑ i, logPoint u i) < 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hprod : 0 < Part3.labelledProduct u :=
    Finset.prod_pos (fun i _ => tuple_pos hu i)
  rw [logPoint, actualPrimeTupleLog_sum_prod _ (tuple_pos hu)]
  apply (div_lt_one (Real.log_pos hNr)).mpr
  exact Real.log_lt_log (by exact_mod_cast hprod) (by exact_mod_cast hp)

/-- Original U7 prime branch: d, p1<p2, p2<=q, original square, full product. -/
def margin7Three (v : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![v 0 - 59 / 250, v 1 - v 0, v 2 - v 1,
    1 - v 0 - 2 * v 1, 1 - (v 0 + v 1 + v 2)]

/-- Original U7 semiprime branch includes r=s and p2=r literally. -/
def margin7Four (v : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![v 0 - 59 / 250, v 1 - v 0, v 2 - v 1, v 3 - v 2,
    1 - v 0 - 2 * v 1, 1 - (v 0 + v 1 + v 2 + v 3)]

/-- Original U8 has the separate first/second N^(1/3) walls. -/
def margin8 (v : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![v 0 - 417 / 5000, 1 / 3 - v 0, v 1 - 1 / 3,
    1 - v 0 - 2 * v 1, v 2 - v 1, 1 - (v 0 + v 1 + v 2)]

/-- Undo only the original fixed branch permutation; never sort again. -/
def original9Log (j : Fin 3) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![![v 1, v 2, v 0], ![v 0, v 2, v 1], ![v 0, v 1, v 2]] j

/-- Two branch margins. The unused second margin is the constant one. -/
def branch9Margins (j : Fin 3) (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![![x 0 - x 2, 1], ![x 2 - x 0, x 1 - x 2], ![x 2 - x 1, 1]] j

/-- U9 retains sqrt(N/(p1*p2))<=q, different from U8's q>=p2. -/
def margin9 (j : Fin 3) (v : Fin 3 → ℝ) : Fin 8 → ℝ :=
  let x := original9Log j v
  ![x 0 - 19 / 125, 59 / 250 - x 0, x 1 - 59 / 250,
    1 - x 0 - 2 * x 1, x 0 + x 1 + 2 * x 2 - 1,
    1 - (x 0 + x 1 + x 2), branch9Margins j x 0, branch9Margins j x 1]

def outer7Three (width : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∏ i : Fin 5, smoothGateUpperStep width (margin7Three v i)
def outer7Four (width : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ∏ i : Fin 6, smoothGateUpperStep width (margin7Four v i)
def outer8 (width : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∏ i : Fin 6, smoothGateUpperStep width (margin8 v i)
def outer9 (j : Fin 3) (width : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∏ i : Fin 8, smoothGateUpperStep width (margin9 j v i)

private theorem gate_product_bounds {k m : ℕ} (g : (Fin k → ℝ) → Fin m → ℝ)
    (width : ℝ) (v : Fin k → ℝ) :
    0 ≤ (∏ i : Fin m, smoothGateUpperStep width (g v i)) ∧
      (∏ i : Fin m, smoothGateUpperStep width (g v i)) ≤ 1 :=
  finite_gate_ramp_product_bounds Finset.univ _
    (fun i _ => smoothGateUpperStep_bounds width (g v i))

theorem original_outer_bounds (width : ℝ) :
    (∀ v, 0 ≤ outer7Three width v ∧ outer7Three width v ≤ 1) ∧
    (∀ v, 0 ≤ outer7Four width v ∧ outer7Four width v ≤ 1) ∧
    (∀ v, 0 ≤ outer8 width v ∧ outer8 width v ≤ 1) ∧
    (∀ j v, 0 ≤ outer9 j width v ∧ outer9 j width v ≤ 1) := by
  exact ⟨gate_product_bounds margin7Three width, gate_product_bounds margin7Four width,
    gate_product_bounds margin8 width, fun j => gate_product_bounds (margin9 j) width⟩

theorem contDiff_outer7Three (width : ℝ) : ContDiff ℝ ∞ (outer7Three width) := by
  apply contDiff_prod
  intro i _
  apply (contDiff_smoothGateUpperStep width).comp
  fin_cases i <;> dsimp [margin7Three] <;> fun_prop

theorem contDiff_outer7Four (width : ℝ) : ContDiff ℝ ∞ (outer7Four width) := by
  apply contDiff_prod
  intro i _
  apply (contDiff_smoothGateUpperStep width).comp
  fin_cases i <;> dsimp [margin7Four] <;> fun_prop

theorem contDiff_outer8 (width : ℝ) : ContDiff ℝ ∞ (outer8 width) := by
  apply contDiff_prod
  intro i _
  apply (contDiff_smoothGateUpperStep width).comp
  fin_cases i <;> dsimp [margin8] <;> fun_prop

theorem contDiff_outer9 (j : Fin 3) (width : ℝ) : ContDiff ℝ ∞ (outer9 j width) := by
  apply contDiff_prod
  intro i _
  apply (contDiff_smoothGateUpperStep width).comp
  fin_cases j <;> fin_cases i <;>
    dsimp [margin9, original9Log, branch9Margins] <;> fun_prop

theorem actual7Three_margins {N : ℕ} (hN : 2 ≤ N)
    {u : Fin 3 → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples 3 N)
    (hw : weight3 N u ≠ 0) : ∀ i, 0 ≤ margin7Three (logPoint u) i := by
  have hp := tuple_pos hu
  have hs := weight3_sorted_primitive hw
  have hf := log_floor hN hu 0 (weight3_lower_power hw 0)
  have h01 := log_order hN hu hs.1.le
  have h12 := log_order hN hu hs.2.1
  have hsq := (currentChenUpsilon9_sqrt_log_iff hN (hp 0) (hp 1)).mp
    (weight3_original_walls hw).2.2.2
  have hsum := log_product_lt_one hN hu hs.2.2.1
  simp only [Fin.sum_univ_three] at hsum
  intro i
  fin_cases i <;> dsimp [margin7Three, logPoint, actualPrimeTupleLog] at * <;> linarith

theorem actual7Four_margins {N : ℕ} (hN : 2 ≤ N)
    {u : Fin 4 → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples 4 N)
    (hw : weight4 N u ≠ 0) : ∀ i, 0 ≤ margin7Four (logPoint u) i := by
  have hp := tuple_pos hu
  have hs := weight4_sorted_primitive hw
  have hf := log_floor hN hu 0 (weight4_lower_power hw 0)
  have h01 := log_order hN hu hs.1.le
  have h12 := log_order hN hu hs.2.1
  have h23 := log_order hN hu hs.2.2.1
  have hsq := (currentChenUpsilon9_sqrt_log_iff hN (hp 0) (hp 1)).mp
    (weight4_original_walls hw).2.2.2.2
  have hsum := log_product_lt_one hN hu hs.2.2.2.1
  simp only [Fin.sum_univ_four] at hsum
  intro i
  fin_cases i <;> dsimp [margin7Four, logPoint, actualPrimeTupleLog] at * <;> linarith

theorem actual8_margins {N : ℕ} (hN : 2 ≤ N)
    {u : Fin 3 → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples 3 N)
    (hw : P5U8SharpKSource.physicalWeight N u ≠ 0) :
    ∀ i, 0 ≤ margin8 (logPoint u) i := by
  have ht : P5U8SharpKSource.physicalInverse u ∈ P5U8SharpKSource.arithmeticTriples N := by
    by_contra hn
    exact hw (by simp [P5U8SharpKSource.physicalWeight, hn])
  obtain ⟨_, _, hfirst, hsecond, hcap⟩ :=
    Finset.mem_filter.mp (P5U8SharpKSource.arithmetic_data ht).1
  have hp := tuple_pos hu
  have hs := P5U8SharpKSource.physicalWeight_support_data hw
  have hf := log_floor hN hu 0 (P5U8SharpKSource.physicalWeight_lower_power hw 0)
  have hfirst' := log_ceiling hN hu 0 hfirst.le
  have hsecond' := log_floor hN hu 1 hsecond
  have h12 := log_order hN hu hs.2.1
  have hsq := (currentChenUpsilon9_sqrt_log_iff hN (hp 0) (hp 1)).mp hcap
  have hsum := log_product_lt_one hN hu hs.2.2.1
  simp only [Fin.sum_univ_three] at hsum
  intro i
  fin_cases i <;> dsimp [margin8, logPoint, actualPrimeTupleLog] at * <;> linarith

private theorem log_quotient_lower {N a b q : ℕ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hcut : Real.sqrt ((N : ℝ) / ((a : ℝ) * (b : ℝ))) ≤ (q : ℝ)) :
    0 ≤ Real.log (a : ℝ) / Real.log (N : ℝ) +
      Real.log (b : ℝ) / Real.log (N : ℝ) +
        2 * (Real.log (q : ℝ) / Real.log (N : ℝ)) - 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hab := mul_pos haR hbR
  have hlog := Real.log_pos hNr
  have h := Real.log_le_log (Real.sqrt_pos.mpr (div_pos hNp hab)) hcut
  rw [Real.log_sqrt (div_nonneg hNp.le hab.le), Real.log_div hNp.ne' hab.ne',
    Real.log_mul haR.ne' hbR.ne'] at h
  have hnum : 0 ≤ Real.log (a : ℝ) + Real.log (b : ℝ) +
      2 * Real.log (q : ℝ) - Real.log (N : ℝ) := by linarith
  have hh := div_nonneg hnum hlog.le
  convert hh using 1 <;> field_simp [hlog.ne'] <;> ring

/-- The branch permutation is an exact log dictionary on original labels. -/
theorem original9Log_dictionary {N : ℕ} (j : Fin 3) (u : Fin 3 → Fin (N + 1)) :
    original9Log j (logPoint u) = actualPrimeTupleLog N
      ![(p5z_u9_physicalInverse j u).1.1, (p5z_u9_physicalInverse j u).1.2,
        (p5z_u9_physicalInverse j u).2] := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [original9Log, logPoint, actualPrimeTupleLog, p5z_u9_physicalInverse]

theorem actual9_margins {N : ℕ} (hN : 2 ≤ N) (j : Fin 3)
    {u : Fin 3 → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples 3 N)
    (hw : p5z_u9_orderedPhysicalWeight j N u ≠ 0) :
    ∀ i, 0 ≤ margin9 j (logPoint u) i := by
  have ht := p5z_u9_orderedPhysicalWeight_support hw
  have hd := p5z_u9_order_source_data (Finset.mem_filter.mp ht).1
  have hbranch := (Finset.mem_filter.mp ht).2
  have hprime := chenY9PrimeSelector_ordered_prime_data hd.1
  obtain ⟨_, hlo, hhi, hsecond, hcap⟩ := Finset.mem_filter.mp hd.1
  let t := p5z_u9_physicalInverse j u
  have hp0 : 0 < t.1.1 := hprime.1.pos
  have hp1 : 0 < t.1.2 := hprime.2.1.pos
  have hp2 : 0 < t.2 := hd.2.2.1.pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  have hlo' := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hlo
  have hhi' := Real.log_le_log (by exact_mod_cast hp0) hhi.le
  have hs' := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hsecond
  rw [Real.log_rpow hNp] at hlo' hhi' hs'
  have hloD := div_le_div_of_nonneg_right hlo' hlog.le
  have hhiD := div_le_div_of_nonneg_right hhi' hlog.le
  have hsD := div_le_div_of_nonneg_right hs' hlog.le
  simp only [mul_div_cancel_right₀ _ hlog.ne'] at hloD hhiD hsD
  have hsq := (currentChenUpsilon9_sqrt_log_iff hN hp0 hp1).mp hcap
  have hcut := log_quotient_lower hN hp0 hp1 hp2 hd.2.2.2.2.1
  have hsum := log_product_lt_one hN hu
    (p5z_u9_orderedPhysicalWeight_support_data hNr.le hw).2.2.1
  simp only [Fin.sum_univ_three] at hsum
  have horder (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
      Real.log (a : ℝ) / Real.log (N : ℝ) ≤ Real.log (b : ℝ) / Real.log (N : ℝ) :=
    div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)) hlog.le
  have hb0 : 0 ≤ branch9Margins j (original9Log j (logPoint u)) 0 ∧
      0 ≤ branch9Margins j (original9Log j (logPoint u)) 1 := by
    rw [original9Log_dictionary]
    fin_cases j
    · have ho : t.2 < t.1.1 := by simpa [t, p5z_u9_orderGate] using hbranch
      have hh := horder t.2 t.1.1 hp2 ho.le
      change 0 ≤ Real.log (t.1.1 : ℝ) / Real.log (N : ℝ) -
        Real.log (t.2 : ℝ) / Real.log (N : ℝ) ∧ (0 : ℝ) ≤ 1
      exact ⟨sub_nonneg.mpr hh, zero_le_one⟩
    · have ho : t.1.1 ≤ t.2 ∧ t.2 < t.1.2 := by
        simpa [t, p5z_u9_orderGate] using hbranch
      have hh := horder t.1.1 t.2 hp0 ho.1
      have hh' := horder t.2 t.1.2 hp2 ho.2.le
      change 0 ≤ Real.log (t.2 : ℝ) / Real.log (N : ℝ) -
        Real.log (t.1.1 : ℝ) / Real.log (N : ℝ) ∧
        0 ≤ Real.log (t.1.2 : ℝ) / Real.log (N : ℝ) -
          Real.log (t.2 : ℝ) / Real.log (N : ℝ)
      exact ⟨sub_nonneg.mpr hh, sub_nonneg.mpr hh'⟩
    · have ho : t.1.2 ≤ t.2 := by simpa [t, p5z_u9_orderGate] using hbranch
      have hh := horder t.1.2 t.2 hp1 ho
      change 0 ≤ Real.log (t.2 : ℝ) / Real.log (N : ℝ) -
        Real.log (t.1.2 : ℝ) / Real.log (N : ℝ) ∧ (0 : ℝ) ≤ 1
      exact ⟨sub_nonneg.mpr hh, zero_le_one⟩
  have hsumOriginal : Real.log (t.1.1 : ℝ) / Real.log (N : ℝ) +
      Real.log (t.1.2 : ℝ) / Real.log (N : ℝ) +
      Real.log (t.2 : ℝ) / Real.log (N : ℝ) < 1 := by
    dsimp [t]
    fin_cases j <;> simp only [p5z_u9_physicalInverse,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
      dsimp [logPoint, actualPrimeTupleLog] at hsum <;> linarith only [hsum]
  intro i
  fin_cases i
  · change 0 ≤ original9Log j (logPoint u) 0 - 19 / 125
    rw [original9Log_dictionary]
    change 0 ≤ Real.log (t.1.1 : ℝ) / Real.log (N : ℝ) - 19 / 125
    exact sub_nonneg.mpr hloD
  · change 0 ≤ 59 / 250 - original9Log j (logPoint u) 0
    rw [original9Log_dictionary]
    change 0 ≤ 59 / 250 - Real.log (t.1.1 : ℝ) / Real.log (N : ℝ)
    exact sub_nonneg.mpr hhiD
  · change 0 ≤ original9Log j (logPoint u) 1 - 59 / 250
    rw [original9Log_dictionary]
    change 0 ≤ Real.log (t.1.2 : ℝ) / Real.log (N : ℝ) - 59 / 250
    exact sub_nonneg.mpr hsD
  · change 0 ≤ 1 - original9Log j (logPoint u) 0 - 2 * original9Log j (logPoint u) 1
    rw [original9Log_dictionary]
    change 0 ≤ 1 - Real.log (t.1.1 : ℝ) / Real.log (N : ℝ) -
      2 * (Real.log (t.1.2 : ℝ) / Real.log (N : ℝ))
    linarith only [hsq]
  · change 0 ≤ original9Log j (logPoint u) 0 + original9Log j (logPoint u) 1 +
      2 * original9Log j (logPoint u) 2 - 1
    rw [original9Log_dictionary]
    exact hcut
  · change 0 ≤ 1 - (original9Log j (logPoint u) 0 + original9Log j (logPoint u) 1 +
      original9Log j (logPoint u) 2)
    rw [original9Log_dictionary]
    change 0 ≤ 1 - (Real.log (t.1.1 : ℝ) / Real.log (N : ℝ) +
      Real.log (t.1.2 : ℝ) / Real.log (N : ℝ) + Real.log (t.2 : ℝ) / Real.log (N : ℝ))
    exact sub_nonneg.mpr hsumOriginal.le
  · exact hb0.1
  · exact hb0.2

private theorem outer_eq_one {m : ℕ} {width : ℝ} (hw : 0 < width)
    (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (∏ i : Fin m, smoothGateUpperStep width (g i)) = 1 := by
  apply Finset.prod_eq_one
  intro i _
  exact smoothGateUpperStep_eq_one hw (hg i)

/-- All original nonzero sources lie on the exact one plateau. The
threshold 2 precedes width, source tuple and U9 branch; no rho is involved. -/
theorem actual_sources_on_plateau {N : ℕ} (hN : 2 ≤ N)
    {width : ℝ} (hw : 0 < width) :
    (∀ u ∈ Part3.labelledPrimeTuples 3 N, weight3 N u ≠ 0 →
      outer7Three width (logPoint u) = 1) ∧
    (∀ u ∈ Part3.labelledPrimeTuples 4 N, weight4 N u ≠ 0 →
      outer7Four width (logPoint u) = 1) ∧
    (∀ u ∈ Part3.labelledPrimeTuples 3 N, P5U8SharpKSource.physicalWeight N u ≠ 0 →
      outer8 width (logPoint u) = 1) ∧
    (∀ j u, u ∈ Part3.labelledPrimeTuples 3 N → p5z_u9_orderedPhysicalWeight j N u ≠ 0 →
      outer9 j width (logPoint u) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu hs
    exact outer_eq_one hw _ (actual7Three_margins hN hu hs)
  · intro u hu hs
    exact outer_eq_one hw _ (actual7Four_margins hN hu hs)
  · intro u hu hs
    exact outer_eq_one hw _ (actual8_margins hN hu hs)
  · intro j u hu hs
    exact outer_eq_one hw _ (actual9_margins hN j hu hs)

/-- The full-product wall is scaled by log N. Thus its permitted support
is exp(width)*N, not N^(1+width). The preceding raw log polytopes alone
must not be used as a complete-product O(N) licence. -/
def productUpper {k : ℕ} (N : ℕ) (width : ℝ) (v : Fin k → ℝ) : ℝ :=
  smoothGateUpperStep width ((1 - ∑ i, v i) * Real.log (N : ℝ))

def physicalOuter7Three (N : ℕ) (width : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  outer7Three width v * productUpper N width v
def physicalOuter7Four (N : ℕ) (width : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  outer7Four width v * productUpper N width v
def physicalOuter8 (N : ℕ) (width : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  outer8 width v * productUpper N width v
def physicalOuter9 (j : Fin 3) (N : ℕ) (width : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  outer9 j width v * productUpper N width v

theorem contDiff_productUpper (k N : ℕ) (width : ℝ) :
    ContDiff ℝ ∞ (@productUpper k N width) := by
  apply (contDiff_smoothGateUpperStep width).comp
  fun_prop

theorem contDiff_physicalOuters (N : ℕ) (width : ℝ) :
    ContDiff ℝ ∞ (physicalOuter7Three N width) ∧
    ContDiff ℝ ∞ (physicalOuter7Four N width) ∧
    ContDiff ℝ ∞ (physicalOuter8 N width) ∧
    (∀ j, ContDiff ℝ ∞ (physicalOuter9 j N width)) := by
  exact ⟨(contDiff_outer7Three width).mul (contDiff_productUpper 3 N width),
    (contDiff_outer7Four width).mul (contDiff_productUpper 4 N width),
    (contDiff_outer8 width).mul (contDiff_productUpper 3 N width),
    fun j => (contDiff_outer9 j width).mul (contDiff_productUpper 3 N width)⟩

private theorem productUpper_one {k N : ℕ} (hN : 2 ≤ N) {width : ℝ} (hw : 0 < width)
    {u : Fin k → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples k N)
    (hp : Part3.labelledProduct u < N) : productUpper N width (logPoint u) = 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact smoothGateUpperStep_eq_one hw (mul_nonneg
    (sub_nonneg.mpr (log_product_lt_one hN hu hp).le) (Real.log_pos hNr).le)

theorem actual_sources_on_physical_plateau {N : ℕ} (hN : 2 ≤ N)
    {width : ℝ} (hw : 0 < width) :
    (∀ u ∈ Part3.labelledPrimeTuples 3 N, weight3 N u ≠ 0 →
      physicalOuter7Three N width (logPoint u) = 1) ∧
    (∀ u ∈ Part3.labelledPrimeTuples 4 N, weight4 N u ≠ 0 →
      physicalOuter7Four N width (logPoint u) = 1) ∧
    (∀ u ∈ Part3.labelledPrimeTuples 3 N, P5U8SharpKSource.physicalWeight N u ≠ 0 →
      physicalOuter8 N width (logPoint u) = 1) ∧
    (∀ j u, u ∈ Part3.labelledPrimeTuples 3 N → p5z_u9_orderedPhysicalWeight j N u ≠ 0 →
      physicalOuter9 j N width (logPoint u) = 1) := by
  have hplateau := actual_sources_on_plateau hN hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu hs
    rw [physicalOuter7Three, hplateau.1 u hu hs,
      productUpper_one hN hw hu (weight3_sorted_primitive hs).2.2.1, one_mul]
  · intro u hu hs
    rw [physicalOuter7Four, hplateau.2.1 u hu hs,
      productUpper_one hN hw hu (weight4_sorted_primitive hs).2.2.2.1, one_mul]
  · intro u hu hs
    rw [physicalOuter8, hplateau.2.2.1 u hu hs,
      productUpper_one hN hw hu (P5U8SharpKSource.physicalWeight_support_data hs).2.2.1,
      one_mul]
  · intro j u hu hs
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    rw [physicalOuter9, hplateau.2.2.2 j u hu hs,
      productUpper_one hN hw hu (p5z_u9_orderedPhysicalWeight_support_data hNr hs).2.2.1,
      one_mul]

/-- Exact complete-product support on every independent prime tuple,
including tuples outside the original source. No rho or density is used. -/
theorem productUpper_complete_support {k N : ℕ} (hN : 2 ≤ N)
    {width : ℝ} (hw : 0 < width) {u : Fin k → Fin (N + 1)}
    (hu : u ∈ Part3.labelledPrimeTuples k N)
    (hn : productUpper N width (logPoint u) ≠ 0) :
    (Part3.labelledProduct u : ℝ) < Real.exp width * (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  have hprod : 0 < Part3.labelledProduct u :=
    Finset.prod_pos (fun i _ => tuple_pos hu i)
  have hprodR : (0 : ℝ) < Part3.labelledProduct u := by exact_mod_cast hprod
  have hs := smoothGateUpperStep_nonzero_support hw hn
  change -width < (1 - ∑ i, logPoint u i) * Real.log (N : ℝ) at hs
  rw [logPoint, actualPrimeTupleLog_sum_prod _ (tuple_pos hu)] at hs
  have heq : (1 - Real.log (Part3.labelledProduct u : ℝ) / Real.log (N : ℝ)) *
      Real.log (N : ℝ) = Real.log (N : ℝ) - Real.log (Part3.labelledProduct u : ℝ) := by
    field_simp [hlog.ne']
  change -width < (1 - Real.log (Part3.labelledProduct u : ℝ) / Real.log (N : ℝ)) *
    Real.log (N : ℝ) at hs
  rw [heq] at hs
  have hlogBound : Real.log (Part3.labelledProduct u : ℝ) < width + Real.log (N : ℝ) := by
    linarith only [hs]
  have hh := Real.exp_lt_exp.mpr hlogBound
  simpa only [Real.exp_log hprodR, Real.exp_add, Real.exp_log hNp] using hh

/-- A convenient common reserve inside all the unchanged original floors.
These are smoothing parameters, not replacements for 59/250, 417/5000,
or 19/125 in the source definitions above. -/
def maximumWidth : ℝ := 417 / 40000
def commonPrimeFloor : ℝ := 417 / 10000

private theorem margin_gt_neg_width {k m : ℕ}
    {g : (Fin k → ℝ) → Fin m → ℝ} {width : ℝ} (hw : 0 < width)
    {v : Fin k → ℝ} (hn : (∏ i : Fin m, smoothGateUpperStep width (g v i)) ≠ 0)
    (i : Fin m) : -width < g v i :=
  smoothGateUpperStep_nonzero_support hw
    (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i))

/-- Uniform positive original-prime floor on the entire smoothed support,
not merely on its old hard source. U9's third floor is deduced from its
own quotient-square wall and original first/second walls. -/
theorem original_outer_positive_floor {width : ℝ}
    (hw : 0 < width) (hwidth : width ≤ maximumWidth) :
    (∀ v, outer7Three width v ≠ 0 → ∀ i, commonPrimeFloor < v i) ∧
    (∀ v, outer7Four width v ≠ 0 → ∀ i, commonPrimeFloor < v i) ∧
    (∀ v, outer8 width v ≠ 0 → ∀ i, commonPrimeFloor < v i) ∧
    (∀ j v, outer9 j width v ≠ 0 → ∀ i, commonPrimeFloor < v i) := by
  dsimp [maximumWidth] at hwidth
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hn i
    have h0 := margin_gt_neg_width (g := margin7Three) hw hn 0
    have h1 := margin_gt_neg_width (g := margin7Three) hw hn 1
    have h2 := margin_gt_neg_width (g := margin7Three) hw hn 2
    fin_cases i <;> dsimp [margin7Three, commonPrimeFloor] at * <;> linarith
  · intro v hn i
    have h0 := margin_gt_neg_width (g := margin7Four) hw hn 0
    have h1 := margin_gt_neg_width (g := margin7Four) hw hn 1
    have h2 := margin_gt_neg_width (g := margin7Four) hw hn 2
    have h3 := margin_gt_neg_width (g := margin7Four) hw hn 3
    fin_cases i <;> dsimp [margin7Four, commonPrimeFloor] at * <;> linarith
  · intro v hn i
    have h0 := margin_gt_neg_width (g := margin8) hw hn 0
    have h2 := margin_gt_neg_width (g := margin8) hw hn 2
    have h4 := margin_gt_neg_width (g := margin8) hw hn 4
    fin_cases i <;> dsimp [margin8, commonPrimeFloor] at * <;> linarith
  · intro j v hn i
    have h0 := margin_gt_neg_width (g := margin9 j) hw hn 0
    have h1 := margin_gt_neg_width (g := margin9 j) hw hn 1
    have h2 := margin_gt_neg_width (g := margin9 j) hw hn 2
    have h3 := margin_gt_neg_width (g := margin9 j) hw hn 3
    have h4 := margin_gt_neg_width (g := margin9 j) hw hn 4
    fin_cases j <;> fin_cases i <;>
      dsimp [margin9, original9Log, commonPrimeFloor] at * <;> linarith

/-- The raw profiles are only internal factors of the physical weights.
Every physical smoothing has the same fixed positive exponent floor. -/
theorem physical_outer_positive_floor {width : ℝ}
    (hw : 0 < width) (hwidth : width ≤ maximumWidth) (N : ℕ) :
    (∀ v, physicalOuter7Three N width v ≠ 0 → ∀ i, commonPrimeFloor < v i) ∧
    (∀ v, physicalOuter7Four N width v ≠ 0 → ∀ i, commonPrimeFloor < v i) ∧
    (∀ v, physicalOuter8 N width v ≠ 0 → ∀ i, commonPrimeFloor < v i) ∧
    (∀ j v, physicalOuter9 j N width v ≠ 0 → ∀ i, commonPrimeFloor < v i) := by
  have hs := original_outer_positive_floor hw hwidth
  exact ⟨fun v hn => hs.1 v (mul_ne_zero_iff.mp hn).1,
    fun v hn => hs.2.1 v (mul_ne_zero_iff.mp hn).1,
    fun v hn => hs.2.2.1 v (mul_ne_zero_iff.mp hn).1,
    fun j v hn => hs.2.2.2 j v (mul_ne_zero_iff.mp hn).1⟩

private theorem prime_floor_of_log {k N : ℕ} (hN : 2 ≤ N)
    {u : Fin k → Fin (N + 1)} (hu : u ∈ Part3.labelledPrimeTuples k N)
    (hfloor : ∀ i, commonPrimeFloor < logPoint u i) :
    ∀ i, (N : ℝ) ^ commonPrimeFloor < ((u i).val : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  intro i
  exact (Real.rpow_lt_rpow_of_exponent_lt hNr (hfloor i)).trans_eq
    (actualPrimeTupleLog_rpow (by omega) (fun j => (u j).val) (tuple_pos hu) i)

/-- Complete source-support statement at every legal width. The one
threshold precedes all six original family labels, every tuple and width.
The complete product is bounded by the same fixed constant exp(maximumWidth).
This statement has no coefficient, PP, or density premise. -/
theorem actual_smoothing_prime_support {N : ℕ} (hN : 2 ≤ N)
    {width : ℝ} (hw : 0 < width) (hwidth : width ≤ maximumWidth) :
    (∀ u ∈ Part3.labelledPrimeTuples 3 N, physicalOuter7Three N width (logPoint u) ≠ 0 →
      (∀ i, (N : ℝ) ^ commonPrimeFloor < ((u i).val : ℝ)) ∧
        (Part3.labelledProduct u : ℝ) < Real.exp maximumWidth * (N : ℝ)) ∧
    (∀ u ∈ Part3.labelledPrimeTuples 4 N, physicalOuter7Four N width (logPoint u) ≠ 0 →
      (∀ i, (N : ℝ) ^ commonPrimeFloor < ((u i).val : ℝ)) ∧
        (Part3.labelledProduct u : ℝ) < Real.exp maximumWidth * (N : ℝ)) ∧
    (∀ u ∈ Part3.labelledPrimeTuples 3 N, physicalOuter8 N width (logPoint u) ≠ 0 →
      (∀ i, (N : ℝ) ^ commonPrimeFloor < ((u i).val : ℝ)) ∧
        (Part3.labelledProduct u : ℝ) < Real.exp maximumWidth * (N : ℝ)) ∧
    (∀ j u, u ∈ Part3.labelledPrimeTuples 3 N → physicalOuter9 j N width (logPoint u) ≠ 0 →
      (∀ i, (N : ℝ) ^ commonPrimeFloor < ((u i).val : ℝ)) ∧
        (Part3.labelledProduct u : ℝ) < Real.exp maximumWidth * (N : ℝ)) := by
  have hs := physical_outer_positive_floor hw hwidth N
  have hcap {k : ℕ} {u : Fin k → Fin (N + 1)}
      (hu : u ∈ Part3.labelledPrimeTuples k N)
      (hn : productUpper N width (logPoint u) ≠ 0) :
      (Part3.labelledProduct u : ℝ) < Real.exp maximumWidth * (N : ℝ) :=
    (productUpper_complete_support hN hw hu hn).trans_le
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hwidth) (Nat.cast_nonneg N))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu hn
    exact ⟨prime_floor_of_log hN hu (hs.1 _ hn), hcap hu (mul_ne_zero_iff.mp hn).2⟩
  · intro u hu hn
    exact ⟨prime_floor_of_log hN hu (hs.2.1 _ hn), hcap hu (mul_ne_zero_iff.mp hn).2⟩
  · intro u hu hn
    exact ⟨prime_floor_of_log hN hu (hs.2.2.1 _ hn), hcap hu (mul_ne_zero_iff.mp hn).2⟩
  · intro j u hu hn
    exact ⟨prime_floor_of_log hN hu (hs.2.2.2 j _ hn), hcap hu (mul_ne_zero_iff.mp hn).2⟩

end
end ImbalancedChen.P5OriginalU789SmoothLogSources
