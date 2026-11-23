import ImbalancedChen.Part5OriginalH430PrimeRegularGerms
import ImbalancedChen.Part5OriginalH430SameQHistoryCells
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-! At fixed frozen precision the allowed exponents form the finite image of
the actual root code. On chronological integer words the next complete square
has wall prefixSum + 2 * next = frozen level. The following majorant pays all
these walls at once in the actual coprime prime-box measure before N is chosen. -/
namespace ImbalancedChen.Part5OriginalH430SquareStripPrimeMass

noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430SameQHistoryCells
open Part5OriginalH430PrimeRegularGerms

abbrev Walls (r n : ℕ) := RootCode n × Fin r

def prefix {r : ℕ} (x : Fin r → ℝ) (i : Fin r) : ℝ :=
  ∑ j : Fin r with j.val < i.val, x j

def wall {r n : ℕ} (w : Walls r n) (x : Fin r → ℝ) : ℝ :=
  prefix x w.2 + 2*x w.2 - codeLevel n w.1

def width (j : ℕ) : ℝ := 1/((j:ℝ)+1)

theorem width_pos (j : ℕ) : 0 < width j := by unfold width; positivity

def thin {r : ℕ} (n j : ℕ) (x : Fin r → ℝ) : Prop :=
  ∃ w : Walls r n, |wall w x| ≤ width j

private def polynomial {r n : ℕ} (w : Walls r n) : Poly r :=
  (∑ j : Fin r with j.val < w.2.val, MvPolynomial.X j) +
    2*MvPolynomial.X w.2 - MvPolynomial.C (codeLevel n w.1)

private theorem evaluation {r n : ℕ} (w : Walls r n) (x : Fin r → ℝ) :
    ev (polynomial w) x = wall w x := by
  simp [ev,polynomial,wall,prefix]

private theorem proper {r n : ℕ} (w : Walls r n) : polynomial w ≠ 0 := by
  intro h
  have zero := evaluation w (fun _ => (0:ℝ))
  have one := evaluation w (fun _ => (1:ℝ))
  rw [h] at zero one
  simp [ev,wall,prefix] at zero one
  have hn : 0 ≤ (((Finset.univ : Finset (Fin r)).filter
    (fun j => j.val < w.2.val)).card : ℝ) := by positivity
  linarith

private def bump (δ y : ℝ) : ℝ := max 0 (min 1 ((2*δ-|y|)/δ))

private theorem bump_one {δ y : ℝ} (hd : 0<δ) (h : |y| ≤ δ) : bump δ y = 1 := by
  have h1 : 1 ≤ (2*δ-|y|)/δ := (le_div_iff₀ hd).mpr (by linarith)
  simp [bump,min_eq_left h1]

private theorem bump_zero {δ y : ℝ} (hd : 0<δ) (h : 2*δ ≤ |y|) : bump δ y = 0 := by
  have h0 : (2*δ-|y|)/δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  exact max_eq_left ((min_le_right _ _).trans h0)

private def majorant (r n j : ℕ) (x : Fin r → ℝ) : ℝ :=
  min 1 (∑ w : Walls r n, bump (width j) (wall w x))

private theorem majorant_bounds (r n j : ℕ) (x : Fin r → ℝ) :
    0 ≤ majorant r n j x ∧ majorant r n j x ≤ 1 :=
  ⟨le_min zero_le_one (Finset.sum_nonneg (fun _ _ => le_max_left _ _)),min_le_left _ _⟩

private theorem majorant_one {r n j : ℕ} {x : Fin r → ℝ} (h : thin n j x) :
    majorant r n j x = 1 := by
  obtain ⟨w,hw⟩ := h
  apply min_eq_left
  calc
    (1:ℝ) = bump (width j) (wall w x) := (bump_one (width_pos j) hw).symm
    _ ≤ _ := Finset.single_le_sum (f := fun v : Walls r n => bump (width j) (wall v x))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ w)

private theorem majorant_continuous (r n j : ℕ) : Continuous (majorant r n j) := by
  unfold majorant bump wall prefix
  fun_prop

private theorem eventually_zero (r n : ℕ) :
    ∀ᵐ x : Fin r → ℝ, ∀ᶠ j : ℕ in atTop, majorant r n j x = 0 := by
  have each (w : Walls r n) : ∀ᵐ x : Fin r → ℝ, wall w x ≠ 0 := by
    simpa only [evaluation] using ae_poly_ne (polynomial w) (proper w)
  filter_upwards [Filter.eventually_all.mpr each] with x hx
  have e (w : Walls r n) : ∀ᶠ j : ℕ in atTop, bump (width j) (wall w x) = 0 := by
    have h : 0 < |wall w x| / 2 := half_pos (abs_pos.mpr (hx w))
    have ht : Tendsto width atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ht.eventually (eventually_lt_nhds h)] with j hj
    exact bump_zero (width_pos j) (by linarith)
  filter_upwards [Filter.eventually_all.mpr e] with j hj
  simp [majorant,hj]

def stripMass (r n j N : ℕ) (a : ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin r => a) (fun _ => 1)
    (fun x => if thin n j x then 1 else 0)

/-- A common width for every physical level permitted by rootCode n and every
prefix of this rank. The order is n, then a sufficiently small width, then N.
The estimate is for actual coprime prime tuples, including repeated letters. -/
theorem prime_square_strip (r n : ℕ) {a eps : ℝ} (ha : 0<a) (hb : a<1) (he : 0<eps) :
    ∀ᶠ j in atTop, ∀ᶠ N in atTop, stripMass r n j N a < eps := by
  let A := fun _ : Fin r => a
  let B := fun _ : Fin r => (1:ℝ)
  let K := fun x : Fin r → ℝ => ∏ i, 1/x i
  let I := fun j => ∫ x in logPrimeBox A B, majorant r n j x * K x
  have hK : IntegrableOn K (logPrimeBox A B) := integrableOn_logPrimeBox_one_div A B (fun _ => ha)
  have hKmeas : Measurable K := Finset.measurable_prod _ (fun _ _ =>
    measurable_const.div (measurable_pi_apply _))
  have hlim : Tendsto I atTop (𝓝 0) := by
    have hlim' : Tendsto I atTop (𝓝 (∫ _x in logPrimeBox A B, (0:ℝ))) := by
      apply tendsto_integral_of_dominated_convergence K
      · intro j
        exact ((majorant_continuous r n j).measurable.mul hKmeas).aestronglyMeasurable
      · exact hK
      · intro j
        filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox A B)] with x hx
        have hp : 0 ≤ K x := Finset.prod_nonneg (fun i _ =>
          (one_div_pos.mpr (ha.trans_le (mem_logPrimeBox.mp hx i).1)).le)
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (majorant_bounds r n j x).1 hp)]
        exact (mul_le_mul_of_nonneg_right (majorant_bounds r n j x).2 hp).trans_eq (one_mul _)
      · filter_upwards [ae_restrict_of_ae (eventually_zero r n)] with x hx
        apply tendsto_const_nhds.congr'
        filter_upwards [hx] with j hj
        simp [hj]
    simpa only [integral_zero] using hlim'
  filter_upwards [hlim.eventually (eventually_lt_nhds he)] with j hj
  have hN := tendsto_actualPrimeBoxTestSum_cube ha hb (majorant r n j)
    (majorant_continuous r n j).continuousOn
  filter_upwards [hN.eventually (eventually_lt_nhds hj)] with N hN
  apply lt_of_le_of_lt _ hN
  unfold stripMass actualPrimeBoxTestSum
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
  by_cases hs : thin n j (actualPrimeTupleLog N p)
  · simp [hs,majorant_one hs]
  · simpa only [if_neg hs] using (majorant_bounds r n j (actualPrimeTupleLog N p)).1

end
end ImbalancedChen.Part5OriginalH430SquareStripPrimeMass
