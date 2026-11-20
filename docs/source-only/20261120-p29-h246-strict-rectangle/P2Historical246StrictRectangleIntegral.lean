import ImbalancedChen.P2Historical246StrictDebit

/-! SOURCE ONLY / UNEVALUATED. Exact real lower bound on one closed
rectangle inside the original H246 row-0 D5 strict-ceiling cut. This is
not an arithmetic-prime-density lower bound, a reserve payment or an
H247 endpoint. -/
namespace ImbalancedChen.P2Historical246StrictRectangleIntegral
noncomputable section
open Set MeasureTheory Finset Filter
open scoped Classical BigOperators Topology
open P2Historical246StrictDebit P2Historical246StrictCeilingChildUpper
open P2HistoricalScheduledPointReads P5OriginalActionMassBound
open P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def rectLow : Point := ![(4999/20000 : ℝ), (5999/20000 : ℝ)]
def rectHigh : Point := ![(5001/20000 : ℝ), (6001/20000 : ℝ)]
def cutRect : Set Point := Icc rectLow rectHigh

def h52 : ℝ := floorValue (outputAt 246 true) (52 : Fin 200)

theorem h52_positive : 0 < h52 := by
  unfold h52 floorValue
  exact div_pos (by exact_mod_cast actualH246_cell52_positive) (by positivity)

/-- The endpoints are deliberately inside the earlier OPEN rectangle,
so closed-boundary points remain in the same original open cell. -/
theorem cutRect_coordinate_bounds {x : Point} (hx : x ∈ cutRect) :
    (2499/10000 : ℝ) < x 0 ∧ x 0 < 2501/10000 ∧
      (2999/10000 : ℝ) < x 1 ∧ x 1 < 3001/10000 := by
  have h0 := hx.1 0
  have h1 := hx.2 0
  have h2 := hx.1 1
  have h3 := hx.2 1
  norm_num [cutRect,rectLow,rectHigh] at h0 h1 h2 h3
  constructor <;> try constructor <;> linarith

/-- This is a subset statement in the literal row-0 D5 real geometry,
not a claim that any particular arithmetic prime pair exists. -/
theorem cutRect_in_original_strict_cut {x : Point} (hx : x ∈ cutRect) :
    x ∈ W2PairDomain (originalW2At 0) 0 ∧ x 0 < 2/7 ∧ 2/7 < x 1 := by
  obtain ⟨h0,h1,h2,h3⟩ := cutRect_coordinate_bounds hx
  have hw0 : (249/1000 : ℝ) < x 0 := by linarith
  have hw1 : x 0 < (251/1000 : ℝ) := by linarith
  have hw2 : (299/1000 : ℝ) < x 1 := by linarith
  have hw3 : x 1 < (301/1000 : ℝ) := by linarith
  have h := first_original_row_ceiling_cuts_open_rectangle hw0 hw1 hw2 hw3
  have hxid : ![x 0,x 1] = x := by funext i; fin_cases i <;> rfl
  rw [hxid] at h
  exact h

/-- Literal old H246 profile equals the retained positive cell 52 value
throughout the entire closed rectangle, including its boundary. -/
theorem cutRect_table_constant {x : Point} (hx : x ∈ cutRect) :
    tableFunction false (outputAt 246 true) (pairProfile (originalW2At 0) 0 x) = h52 := by
  obtain ⟨h0,h1,h2,h3⟩ := cutRect_coordinate_bounds hx
  have hcell := first_row_profile_in_cell52 h0 h1 h2 h3
  have hxid : ![x 0,x 1] = x := by funext i; fin_cases i <;> rfl
  rw [hxid] at hcell
  let rho := pairProfile (originalW2At 0) 0 x
  let atom : FloorAtom := Sum.inl (52 : Fin 200)
  have hmem : rho ∈ upperAtomSet atom := by
    change (((1 : ℝ) ≤ rho ∧ rho ≤ 5) ∧
      (floorGrid 52 < rho ∧ rho < floorGrid 53))
    norm_num [floorGrid]
    constructor <;> constructor <;> linarith [hcell.1,hcell.2]
  rw [tableFunction_upper]
  unfold upperFloor
  calc
    _ = (upperAtomSet atom).indicator (fun _ => floorAtomValue (outputAt 246 true) atom) rho := by
      apply Finset.sum_eq_single atom
      · intro c _ hca
        exact indicator_of_notMem (fun hc => hca (P5Z.U11H248.upperAtom_unique hc hmem)) _
      · intro h
        exact (h (Finset.mem_univ atom)).elim
    _ = _ := by simp [hmem,atom,floorAtomValue,h52]

theorem cutRect_subset_ambient {x : Point} (hx : x ∈ cutRect) : x ∈ pairAmbient := by
  obtain ⟨h0,h1,h2,h3⟩ := cutRect_coordinate_bounds hx
  change ((fun _ : Fin 2 => (1/5 : ℝ)) ≤ x) ∧ x ≤ (fun _ : Fin 2 => (1/2 : ℝ))
  constructor <;> intro i <;> fin_cases i <;> linarith

/-- The ORIGINAL kernel is at least one on this small rectangle. -/
theorem cutRect_kernel_ge_one {x : Point} (hx : x ∈ cutRect) : 1 ≤ pairKernel x := by
  obtain ⟨h0,h1,h2,h3⟩ := cutRect_coordinate_bounds hx
  have hu : 0 < x 0 := by linarith
  have hv : 0 < x 1 := by linarith
  have hr : 0 < 1-x 0-x 1 := by linarith
  have hru : (1/5 : ℝ) ≤ 1-x 0-x 1 := by linarith
  have hu1 : x 0 ≤ 1 := by linarith
  have hv1 : x 1 ≤ 1 := by linarith
  have hr1 : 1-x 0-x 1 ≤ 1 := by linarith
  have huv : x 0*x 1 ≤ 1 := by
    have h := mul_le_mul hu1 hv1 hv.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h]
  have hden : x 0*x 1*(1-x 0-x 1) ≤ 1 := by
    have h := mul_le_mul huv hr1 hr.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h]
  have hpos : 0 < x 0*x 1*(1-x 0-x 1) := mul_pos (mul_pos hu hv) hr
  rw [pairKernel_eq_raw (cutRect_subset_ambient hx) hru]
  apply (le_div_iff₀ hpos).2
  linarith

/-- Exact two-dimensional Lebesgue area in the existing Point measure. -/
theorem cutRect_volume : (volume cutRect).toReal = 1/100000000 := by
  rw [cutRect, Real.volume_Icc_pi_toReal (by intro i; fin_cases i <;> norm_num [rectLow,rectHigh])]
  norm_num [rectLow,rectHigh,Fin.prod_univ_two]

/-- Explicit real integral lower bound for the literal H246 row-0
profile on a subset of the strict ceiling cut. The factor /5 is NOT
applied here; no count or reserve licence is inferred. -/
theorem cutRect_old_profile_integral_lower :
    h52/100000000 ≤
      ∫ x in cutRect, pairKernel x * tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x) := by
  have hi : IntegrableOn (fun x : Point => pairKernel x * h52) cutRect :=
    (pairKernel_continuous.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hc : IntegrableOn (fun _ : Point => h52) cutRect :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have heq : (∫ x in cutRect, pairKernel x * tableFunction false (outputAt 246 true)
      (pairProfile (originalW2At 0) 0 x)) = ∫ x in cutRect, pairKernel x * h52 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    rw [cutRect_table_constant hx]
  rw [heq]
  calc
    h52/100000000 = ∫ _x in cutRect, h52 := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
        smul_eq_mul, cutRect_volume]
      ring
    _ ≤ ∫ x in cutRect, pairKernel x * h52 := by
      apply setIntegral_mono_on hc hi measurableSet_Icc
      intro x hx
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutRect_kernel_ge_one hx) h52_positive.le

theorem cutRect_old_profile_integral_positive :
    0 < ∫ x in cutRect, pairKernel x * tableFunction false (outputAt 246 true)
      (pairProfile (originalW2At 0) 0 x) :=
  (div_pos h52_positive (by norm_num)).trans_le cutRect_old_profile_integral_lower


/-- On the actual D5 rectangle, the clamped kernel is exactly the
original 1/[u v (1-u-v)] manuscript kernel. -/
theorem cutRect_original_kernel {x : Point} (hx : x ∈ cutRect) :
    pairKernel x * tableFunction false (outputAt 246 true)
      (pairProfile (originalW2At 0) 0 x) =
    tableFunction false (outputAt 246 true) (pairProfile (originalW2At 0) 0 x) /
      (x 0*x 1*(1-x 0-x 1)) := by
  obtain ⟨h0,h1,h2,h3⟩ := cutRect_coordinate_bounds hx
  have hr : (1/5 : ℝ) ≤ 1-x 0-x 1 := by linarith
  rw [pairKernel_eq_raw (cutRect_subset_ambient hx) hr]
  ring

/-- Same real integral bound in the original W2 kernel and old H246
normalization, before the one /5. -/
theorem cutRect_original_integral_lower :
    h52/100000000 ≤
      ∫ x in cutRect, tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x) / (x 0*x 1*(1-x 0-x 1)) := by
  have heq : (∫ x in cutRect, pairKernel x * tableFunction false (outputAt 246 true)
      (pairProfile (originalW2At 0) 0 x)) =
      ∫ x in cutRect, tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x) / (x 0*x 1*(1-x 0-x 1)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact cutRect_original_kernel hx
  rw [← heq]
  exact cutRect_old_profile_integral_lower

/-- The original W2 accounting divides this one positive pair
contribution by 5 exactly once. -/
theorem cutRect_original_W2_contribution_lower :
    h52/500000000 ≤
      (∫ x in cutRect, tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x) / (x 0*x 1*(1-x 0-x 1)))/5 := by
  have h := cutRect_original_integral_lower
  linarith only [h]


/-- The actual row-0 D5 domain rejected by the real relative ceiling
2/7. This is an integral domain, not a discrete prime carrier. -/
def realStrictCut : Set Point :=
  W2PairDomain (originalW2At 0) 0 ∩ {x | (2/7 : ℝ) < x 1}

theorem cutRect_subset_realStrictCut : cutRect ⊆ realStrictCut := by
  intro x hx
  have h := cutRect_in_original_strict_cut hx
  exact ⟨h.1,h.2.2⟩

theorem realStrictCut_subset_ambient : realStrictCut ⊆ pairAmbient := by
  intro x hx
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem 0)
  exact (W2PairDomain_geometry hg 0 hx.1).1

/-- Explicit positive lower bound for the full REAL row-0 strict-cut
profile integral. This does not assert a corresponding arithmetic
prime-mass lower bound or pay any numerical reserve. -/
theorem realStrictCut_profile_integral_lower :
    h52/100000000 ≤
      ∫ x in realStrictCut, pairKernel x * tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x) := by
  have hkernel : IntegrableOn pairKernel pairAmbient :=
    pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hambient : IntegrableOn (fun x : Point => pairKernel x *
      tableFunction false (outputAt 246 true) (pairProfile (originalW2At 0) 0 x)) pairAmbient := by
    exact integrableOn_weightedTable false (outputAt 246 true)
      (measurable_pairProfile (originalW2At 0) 0) measurableSet_Icc hkernel
  have hcut := hambient.mono_set realStrictCut_subset_ambient
  have hnonneg (x : Point) : 0 ≤ pairKernel x *
      tableFunction false (outputAt 246 true) (pairProfile (originalW2At 0) 0 x) :=
    mul_nonneg (pairKernel_nonneg x) (tableFunction_nonnegative false actualH246_nonnegative _)
  have hmono := setIntegral_mono_set hcut (Filter.Eventually.of_forall hnonneg)
    (Filter.Eventually.of_forall cutRect_subset_realStrictCut)
  exact cutRect_old_profile_integral_lower.trans hmono

theorem realStrictCut_W2_lower :
    h52/500000000 ≤
      (∫ x in realStrictCut, pairKernel x * tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x))/5 := by
  have h := realStrictCut_profile_integral_lower
  linarith only [h]

end
end ImbalancedChen.P2Historical246StrictRectangleIntegral
