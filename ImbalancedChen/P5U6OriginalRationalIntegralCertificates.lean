import ImbalancedChen.P5U6OriginalRationalBoxBounds
import ImbalancedChen.LogPrimeBoxMesh

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Generated rational inner/outer staircases of the ORIGINAL Runbo domain.
The two original bands are [417/5000,19/125) and [19/125,59/250).
The inclusive product wall is u+t<=833/2500. Every outer point is covered;
every inner half-open cell is contained in the domain and has unique owner.
Whole rectangle areas are exact rationals. Real kernel inequalities and
integrability are supplied by actual proofs, never by certificate premises.
No finite rational check is evaluated and no saved endpoint is asserted.
-/

namespace ImbalancedChen.P5U6OriginalRationalIntegralCertificates

noncomputable section

open Set MeasureTheory Classical
open scoped BigOperators
open P5U6OriginalRationalBoxBounds
open P5U6AdoptedH248BindingSourceOnly P5U6RetainedAdoptedIntegralSourceOnly

def lo : Fin 2 → ℚ := ![417 / 5000, 19 / 125]
def hi : Fin 2 → ℚ := ![19 / 125, 59 / 250]
def point (a b : ℚ) (n k : ℕ) : ℚ := a + (k : ℚ) * ((b - a) / (n + 1 : ℕ))
abbrev Index (n : ℕ) := Fin 2 → Fin (n + 1)

def lowerCorner (n : ℕ) (j : Index n) (i : Fin 2) : ℚ := point (lo i) (hi i) n (j i).val
def upperCorner (n : ℕ) (j : Index n) (i : Fin 2) : ℚ := point (lo i) (hi i) n ((j i).val + 1)
def gridBox (n : ℕ) (j : Index n) : Box :=
  ⟨lowerCorner n j 0, upperCorner n j 0, lowerCorner n j 1, upperCorner n j 1⟩
def cell (n : ℕ) (j : Index n) : Set (Fin 2 → ℝ) :=
  logPrimeBox (fun i => (lowerCorner n j i : ℝ)) (fun i => (upperCorner n j i : ℝ))
def inner (n : ℕ) : Finset (Index n) := Finset.univ.filter fun j =>
  (gridBox n j).uHi + (gridBox n j).tHi ≤ 833 / 2500
def outer (n : ℕ) : Finset (Index n) := Finset.univ.filter fun j =>
  (gridBox n j).uLo + (gridBox n j).tLo ≤ 833 / 2500
def area (n : ℕ) (j : Index n) : ℚ :=
  ((gridBox n j).uHi - (gridBox n j).uLo) *
    ((gridBox n j).tHi - (gridBox n j).tLo)

theorem point_cast (a b : ℚ) (n k : ℕ) :
    (point a b n k : ℝ) = logPrimeMeshPoint (a : ℝ) (b : ℝ) n k := by
  simp [point, logPrimeMeshPoint, logPrimeMeshStep]

theorem corner_bounds (n : ℕ) (j : Index n) (i : Fin 2) :
    lo i ≤ lowerCorner n j i ∧ lowerCorner n j i < upperCorner n j i ∧
      upperCorner n j i ≤ hi i := by
  have hab : (lo i : ℝ) < (hi i : ℝ) := by fin_cases i <;> norm_num [lo, hi]
  have h := logPrimeMeshLoHi_bounds (d := 1) hab n (fun _ => j i) 0
  have hL : (lo i : ℝ) ≤ (lowerCorner n j i : ℝ) := by
    simpa only [lowerCorner, point_cast, logPrimeMeshLo] using h.1
  have hM : (lowerCorner n j i : ℝ) < (upperCorner n j i : ℝ) := by
    simpa only [lowerCorner, upperCorner, point_cast, logPrimeMeshLo, logPrimeMeshHi] using h.2.1
  have hU : (upperCorner n j i : ℝ) ≤ (hi i : ℝ) := by
    simpa only [upperCorner, point_cast, logPrimeMeshHi] using h.2.2
  exact ⟨by exact_mod_cast hL, by exact_mod_cast hM, by exact_mod_cast hU⟩

theorem gridBox_admissible (n : ℕ) (j : Index n) : (gridBox n j).Admissible := by
  have hu := corner_bounds n j 0
  have ht := corner_bounds n j 1
  dsimp [lo, hi] at hu ht
  change 0 < lowerCorner n j 0 ∧ 0 < lowerCorner n j 1 ∧
    upperCorner n j 0 + upperCorner n j 1 < 1 / 2
  constructor
  · linarith only [hu.1]
  constructor
  · linarith only [ht.1]
  · linarith only [hu.2.2, ht.2.2]

theorem cell_measurable (n : ℕ) (j : Index n) : MeasurableSet (cell n j) :=
  measurableSet_logPrimeBox _ _

theorem cell_subset_box (n : ℕ) (j : Index n) : cell n j ⊆ (gridBox n j).cell := by
  intro x hx
  have h := mem_logPrimeBox.mp hx
  exact ⟨(h 0).1, (h 0).2.le, (h 1).1, (h 1).2.le⟩

theorem cell_subset_rectangle (n : ℕ) (j : Index n) :
    cell n j ⊆ currentChenUpsilon6LogRectangle := by
  intro x hx
  have h := mem_logPrimeBox.mp hx
  have h0 := corner_bounds n j 0
  have h1 := corner_bounds n j 1
  have h0L : (417 / 5000 : ℝ) ≤ lowerCorner n j 0 := by exact_mod_cast h0.1
  have h0U : (upperCorner n j 0 : ℝ) ≤ 19 / 125 := by exact_mod_cast h0.2.2
  have h1L : (19 / 125 : ℝ) ≤ lowerCorner n j 1 := by exact_mod_cast h1.1
  have h1U : (upperCorner n j 1 : ℝ) ≤ 59 / 250 := by exact_mod_cast h1.2.2
  exact mem_currentChenUpsilon6LogRectangle.mpr
    ⟨h0L.trans (h 0).1, (h 0).2.trans_le h0U,
      h1L.trans (h 1).1, (h 1).2.trans_le h1U⟩

theorem inner_cell_subset_domain (n : ℕ) {j : Index n} (hj : j ∈ inner n) :
    cell n j ⊆ currentChenUpsilon6LogDomain 0 := by
  intro x hx
  have hB := cell_subset_box n j hx
  have hcap : ((gridBox n j).uHi : ℝ) + (gridBox n j).tHi ≤ 833 / 2500 := by
    exact_mod_cast (Finset.mem_filter.mp hj).2
  exact ⟨cell_subset_rectangle n j hx, by
    change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0
    linarith only [hB.2.1, hB.2.2.2, hcap]⟩

theorem domain_cell_is_outer (n : ℕ) {j : Index n} {x : Fin 2 → ℝ}
    (hD : x ∈ currentChenUpsilon6LogDomain 0) (hx : x ∈ cell n j) : j ∈ outer n := by
  have hB := cell_subset_box n j hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hcap : ((gridBox n j).uLo : ℝ) + (gridBox n j).tLo ≤ 833 / 2500 := by
    have hDcap := hD.2
    change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0 at hDcap
    linarith only [hB.1, hB.2.2.1, hDcap]
  exact_mod_cast hcap

/-- Actual original half-open rectangle coverage, before the product test. -/
theorem rectangle_cell_cover (n : ℕ) {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) : ∃ j : Index n, x ∈ cell n j := by
  have hcoords (i : Fin 2) : x i ∈ Ico (lo i : ℝ) (hi i : ℝ) := by
    have h := mem_currentChenUpsilon6LogRectangle.mp hx
    fin_cases i
    · exact ⟨h.1, h.2.1⟩
    · exact ⟨h.2.2.1, h.2.2.2⟩
  have hex (i : Fin 2) := exists_logPrimeMeshInterval (lo i : ℝ) (hi i : ℝ) n (hcoords i)
  choose j hj using hex
  refine ⟨j, mem_logPrimeBox.mpr ?_⟩
  intro i
  simpa only [lowerCorner, upperCorner, point_cast] using hj i

theorem domain_outer_cover (n : ℕ) {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogDomain 0) : ∃ j ∈ outer n, x ∈ cell n j := by
  obtain ⟨j, hj⟩ := rectangle_cell_cover n hx.1
  exact ⟨j, domain_cell_is_outer n hx hj, hj⟩

theorem cell_unique {n : ℕ} {j k : Index n} {x : Fin 2 → ℝ}
    (hj : x ∈ cell n j) (hk : x ∈ cell n k) : j = k := by
  ext i
  have hJ := mem_logPrimeBox.mp hj i
  have hK := mem_logPrimeBox.mp hk i
  have hab : (lo i : ℝ) ≤ (hi i : ℝ) := by fin_cases i <;> norm_num [lo, hi]
  have hJ' : (fun _ : Fin 1 => x i) ∈
      logPrimeMeshCell (lo i : ℝ) (hi i : ℝ) n (fun _ => j i) := by
    apply mem_logPrimeMeshCell.mpr
    intro v
    simpa only [lowerCorner, upperCorner, point_cast, logPrimeMeshLo, logPrimeMeshHi] using hJ
  have hK' : (fun _ : Fin 1 => x i) ∈
      logPrimeMeshCell (lo i : ℝ) (hi i : ℝ) n (fun _ => k i) := by
    apply mem_logPrimeMeshCell.mpr
    intro v
    simpa only [lowerCorner, upperCorner, point_cast, logPrimeMeshLo, logPrimeMeshHi] using hK
  exact congrFun (logPrimeMeshCell_unique hab hJ' hK') 0

theorem area_nonneg (n : ℕ) (j : Index n) : 0 ≤ area n j :=
  mul_nonneg (sub_nonneg.mpr (corner_bounds n j 0).2.1.le)
    (sub_nonneg.mpr (corner_bounds n j 1).2.1.le)

/-- Exact rational 2D area, with no product-wall clipping substituted. -/
theorem cell_volume_real (n : ℕ) (j : Index n) :
    volume.real (cell n j) = (area n j : ℝ) := by
  rw [Measure.real, cell, logPrimeBox, volume_pi_pi]
  simp only [Real.volume_Ico, Fin.prod_univ_two, ENNReal.toReal_mul]
  have h0 : (0 : ℝ) ≤ (upperCorner n j 0 : ℝ) - lowerCorner n j 0 :=
    sub_nonneg.mpr (by exact_mod_cast (corner_bounds n j 0).2.1.le)
  have h1 : (0 : ℝ) ≤ (upperCorner n j 1 : ℝ) - lowerCorner n j 1 :=
    sub_nonneg.mpr (by exact_mod_cast (corner_bounds n j 1).2.1.le)
  rw [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1]
  simp only [area, gridBox, Rat.cast_mul, Rat.cast_sub]

def densityLower (n precision : ℕ) (j : Index n) : ℚ :=
  max 0 ((gridBox n j).kernelLower precision)
def densityUpper (n precision : ℕ) (j : Index n) : ℚ :=
  max 0 ((gridBox n j).kernelUpper precision)
def minorant (n precision : ℕ) (j : Index n) : (Fin 2 → ℝ) → ℝ :=
  (cell n j).indicator (fun _ => (densityLower n precision j : ℝ))
def majorant (n precision : ℕ) (j : Index n) : (Fin 2 → ℝ) → ℝ :=
  (cell n j).indicator (fun _ => (densityUpper n precision j : ℝ))

theorem kernel_cell_bounds (n precision : ℕ) (j : Index n) {x : Fin 2 → ℝ}
    (hx : x ∈ cell n j) (hD : x ∈ currentChenUpsilon6LogDomain 0) :
    (densityLower n precision j : ℝ) ≤ adoptedKernel x ∧
      adoptedKernel x ≤ (densityUpper n precision j : ℝ) := by
  have h := (gridBox n j).kernel_bounds (gridBox_admissible n j) precision
    (cell_subset_box n j hx) hD
  simp only [densityLower, densityUpper, Rat.cast_max, Rat.cast_zero]
  exact ⟨max_le (adoptedKernel_nonneg (by norm_num) hD) h.1,
    h.2.trans (le_max_right _ _)⟩

theorem cell_constant_integrable (n : ℕ) (j : Index n) (q : ℚ) :
    Integrable ((cell n j).indicator (fun _ : Fin 2 → ℝ => (q : ℝ))) := by
  let C : Set (Fin 2 → ℝ) := Icc (fun i => (lowerCorner n j i : ℝ))
    (fun i => (upperCorner n j i : ℝ))
  have hc : IsCompact C := isCompact_Icc
  have hsub : cell n j ⊆ C := by
    intro x hx
    exact ⟨fun i => (mem_logPrimeBox.mp hx i).1,
      fun i => (mem_logPrimeBox.mp hx i).2.le⟩
  exact ((continuousOn_const.integrableOn_compact hc).mono_set hsub).integrable_indicator
    (cell_measurable n j)

theorem integral_cell_constant (n : ℕ) (j : Index n) (q : ℚ) :
    (∫ x, (cell n j).indicator (fun _ : Fin 2 → ℝ => (q : ℝ)) x) =
      ((q * area n j : ℚ) : ℝ) := by
  rw [integral_indicator (cell_measurable n j), integral_const]
  simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
    smul_eq_mul, cell_volume_real, Rat.cast_mul]
  ring

theorem domain_measurable : MeasurableSet (currentChenUpsilon6LogDomain 0) :=
  P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0
theorem kernel_indicator_integrable :
    Integrable ((currentChenUpsilon6LogDomain 0).indicator adoptedKernel) :=
  (integrableOn_adoptedEnhancedKernel (by norm_num : (0 : ℝ) ≤ 0)).integrable_indicator
    domain_measurable
theorem kernel_indicator_nonneg (x : Fin 2 → ℝ) :
    0 ≤ (currentChenUpsilon6LogDomain 0).indicator adoptedKernel x := by
  by_cases hx : x ∈ currentChenUpsilon6LogDomain 0
  · simpa only [indicator_of_mem hx] using adoptedKernel_nonneg (by norm_num) hx
  · simp only [indicator_of_notMem hx, le_refl]
theorem majorant_nonneg (n precision : ℕ) (j : Index n) (x : Fin 2 → ℝ) :
    0 ≤ majorant n precision j x := by
  by_cases hx : x ∈ cell n j
  · rw [majorant, indicator_of_mem hx]
    exact_mod_cast (le_max_left (0 : ℚ) ((gridBox n j).kernelUpper precision))
  · simp only [majorant, indicator_of_notMem hx, le_refl]

def rationalLower (n precision : ℕ) : ℚ :=
  ∑ j ∈ inner n, densityLower n precision j * area n j
def rationalUpper (n precision : ℕ) : ℚ :=
  ∑ j ∈ outer n, densityUpper n precision j * area n j

/-- Genuine automatic lower certificate for the original full adopted U6. -/
theorem rationalLower_le_fullIntegral (n precision : ℕ) :
    (rationalLower n precision : ℝ) ≤ fullIntegral 0 := by
  have hf : Integrable (fun x => ∑ j ∈ inner n, minorant n precision j x) :=
    integrable_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)
  have hpoint (x : Fin 2 → ℝ) : (∑ j ∈ inner n, minorant n precision j x) ≤
      (currentChenUpsilon6LogDomain 0).indicator adoptedKernel x := by
    by_cases hex : ∃ j ∈ inner n, x ∈ cell n j
    · obtain ⟨j, hj, hxj⟩ := hex
      have hD := inner_cell_subset_domain n hj hxj
      have heq : (∑ k ∈ inner n, minorant n precision k x) = minorant n precision j x := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          exact indicator_of_notMem (fun hxk => hkj (cell_unique hxk hxj)) _
        · intro hnot
          exact (hnot hj).elim
      rw [heq, minorant, indicator_of_mem hxj, indicator_of_mem hD]
      exact (kernel_cell_bounds n precision j hxj hD).1
    · have hz : (∑ j ∈ inner n, minorant n precision j x) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun hxj => hex ⟨j, hj, hxj⟩) _
      rw [hz]
      exact kernel_indicator_nonneg x
  calc
    (rationalLower n precision : ℝ) =
        ∑ j ∈ inner n, ((densityLower n precision j * area n j : ℚ) : ℝ) := by
      simp [rationalLower]
    _ = ∑ j ∈ inner n, ∫ x, minorant n precision j x := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_cell_constant n j _).symm
    _ = ∫ x, ∑ j ∈ inner n, minorant n precision j x :=
      (integral_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)).symm
    _ ≤ ∫ x, (currentChenUpsilon6LogDomain 0).indicator adoptedKernel x :=
      integral_mono hf kernel_indicator_integrable hpoint
    _ = fullIntegral 0 := integral_indicator domain_measurable

/-- Genuine automatic whole-outer-cell upper certificate; product-wall
straddles are paid rather than discarded as arithmetic-empty endpoints. -/
theorem fullIntegral_le_rationalUpper (n precision : ℕ) :
    fullIntegral 0 ≤ (rationalUpper n precision : ℝ) := by
  have hg : Integrable (fun x => ∑ j ∈ outer n, majorant n precision j x) :=
    integrable_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
  have hpoint (x : Fin 2 → ℝ) :
      (currentChenUpsilon6LogDomain 0).indicator adoptedKernel x ≤
        ∑ j ∈ outer n, majorant n precision j x := by
    by_cases hx : x ∈ currentChenUpsilon6LogDomain 0
    · obtain ⟨j, hj, hxj⟩ := domain_outer_cover n hx
      rw [indicator_of_mem hx]
      calc
        adoptedKernel x ≤ (densityUpper n precision j : ℝ) :=
          (kernel_cell_bounds n precision j hxj hx).2
        _ = majorant n precision j x := (indicator_of_mem hxj _).symm
        _ ≤ _ := Finset.single_le_sum (fun k _ => majorant_nonneg n precision k x) hj
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun j _ => majorant_nonneg n precision j x)
  calc
    fullIntegral 0 = ∫ x, (currentChenUpsilon6LogDomain 0).indicator adoptedKernel x :=
      (integral_indicator domain_measurable).symm
    _ ≤ ∫ x, ∑ j ∈ outer n, majorant n precision j x :=
      integral_mono kernel_indicator_integrable hg hpoint
    _ = ∑ j ∈ outer n, ∫ x, majorant n precision j x :=
      integral_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
    _ = ∑ j ∈ outer n, ((densityUpper n precision j * area n j : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_cell_constant n j _
    _ = (rationalUpper n precision : ℝ) := by simp [rationalUpper]

theorem original_integral_enclosure (nL pL nU pU : ℕ) :
    (rationalLower nL pL : ℝ) ≤ fullIntegral 0 ∧
      fullIntegral 0 ≤ (rationalUpper nU pU : ℝ) :=
  ⟨rationalLower_le_fullIntegral nL pL, fullIntegral_le_rationalUpper nU pU⟩

/-- A finite rational statement only; no assertion that an instance passes. -/
def directedCheck (nL pL nU pU : ℕ) (lower upper : ℚ) : Bool := decide
  (lower ≤ rationalLower nL pL ∧ rationalUpper nU pU ≤ upper)

theorem directedCheck_sound (nL pL nU pU : ℕ) (lower upper : ℚ)
    (hcheck : directedCheck nL pL nU pU lower upper = true) :
    (lower : ℝ) ≤ fullIntegral 0 ∧ fullIntegral 0 ≤ (upper : ℝ) := by
  have hc : lower ≤ rationalLower nL pL ∧ rationalUpper nU pU ≤ upper :=
    of_decide_eq_true hcheck
  have hL : (lower : ℝ) ≤ (rationalLower nL pL : ℝ) := by exact_mod_cast hc.1
  have hU : (rationalUpper nU pU : ℝ) ≤ (upper : ℝ) := by exact_mod_cast hc.2
  exact ⟨hL.trans (rationalLower_le_fullIntegral nL pL),
    (fullIntegral_le_rationalUpper nU pU).trans hU⟩

end

end ImbalancedChen.P5U6OriginalRationalIntegralCertificates
