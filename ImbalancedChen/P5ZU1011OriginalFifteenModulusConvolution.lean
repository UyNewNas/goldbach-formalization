import ImbalancedChen.P5ZU1011OriginalFifteenNativeGridDispatch
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The literal physical modulus convolution of the selected original15 fixed
native grid rows. Each mark is an ACTUAL chosen ordinary tuple and a
nonzero divisor coefficient from its selected native support. The ONE
sigma(q) is its signed finite fibre sum at q=full four-prime prefix*d.
Main, prime-AP, centre and estimator sums push forward against this same
sigma, before norms. A finite N-independent maximum of native levels pays
the physical support. No unit bound on the fibre SUM is assumed.

Unique top-four factorization, squarefreeness and the aggregated unit bound
are deliberately left for the companion arithmetic factorization module.
No H248 density meaning, PP/distribution license or final mean is supplied.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenModulusConvolution

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells U1011OriginalFifteenNativeGridDispatch
open U1011OriginalSixteenPolicyBank.BoxCertificates
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

abbrev Mark := Σ _ : Four, ℕ
def activeRows (n N : ℕ) (t : Four) : Finset ℕ :=
  (selectedSupport n N t).filter (fun d => selectedCoefficient n N t d ≠ 0)
def marks (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset Mark :=
  (ordinaryTuples n N E).sigma (activeRows n N)
def modulus (m : Mark) : ℕ := fullPrefix m.1 * m.2
def weight (n N : ℕ) (m : Mark) : ℝ := selectedCoefficient n N m.1 m.2
def modulusSupport (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset ℕ := (marks n N E).image modulus
def fibre (n N : ℕ) (E : ℕ × ℕ → Prop) (q : ℕ) : Finset Mark :=
  (marks n N E).filter (fun m => modulus m = q)
def sigma (n N : ℕ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ m ∈ fibre n N E q, weight n N m

/-- Native source ownership, active actual support and coefficient are
extracted from the literal chosen tuple; no factorization witness is an input. -/
theorem mark_cell_data {n N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {m : Mark}
    (hm : m ∈ marks n N E) :
    ∃ i : Index n, i ∈ activeCells n ∧ m.1 ∈ selectedTuples n N E i ∧
      m.2 ∈ U1011OriginalFifteenFixedCellNative.support (policy i) (gridBox n i.2) N ∧
      weight n N m = U1011OriginalFifteenFixedCellNative.coefficient (policy i) (gridBox n i.2) N m.2 ∧
      U1011OriginalFifteenFixedCellNative.coefficient (policy i) (gridBox n i.2) N m.2 ≠ 0 := by
  obtain ⟨ht,hd⟩ := Finset.mem_sigma.mp hm
  obtain ⟨i,hi,_⟩ := ordinary_has_unique_active_cell hN ht
  have hrow := selected_row_eq_fixed_cell hi.2
  obtain ⟨hd,hnz⟩ := Finset.mem_filter.mp hd
  rw [hrow.2.1] at hd
  have heq := hrow.2.2 m.2
  exact ⟨i,hi.1,hi.2,hd,heq,by rw [← heq]; exact hnz⟩

/-- Actual full physical modulus with centre-prime deletion retained. -/
theorem mark_modulus_positive_coprime {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {m : Mark} (hm : m ∈ marks n N E) :
    0 < modulus m ∧ Nat.Coprime (modulus m) N := by
  obtain ⟨i,hi,ht,hd,_,_⟩ := mark_cell_data hN hm
  have hsource := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hjoint := P5U1011JointOverlap.originalU11_mem_joint
    (by exact_mod_cast (Nat.le_of_lt hN)) hsource
  have hbpos : 0 < fullPrefix m.1 := by
    rw [fullPrefix_eq_multiplier]
    exact P5U1011JointOverlap.joint_multiplier_pos hjoint
  have hbcop : Nat.Coprime (fullPrefix m.1) N := subproduct_coprime_target hjoint Finset.univ
  have hdpos : 0 < m.2 := Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree _ _ _ hd).ne_zero
  have hdcop := actualSmallRosserSupport_coprime_target _ _ _ hd
  exact ⟨mul_pos hbpos hdpos,Nat.coprime_mul_iff_left.mpr ⟨hbcop,hdcop⟩⟩

theorem mark_weight_abs_le_one {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {m : Mark} (hm : m ∈ marks n N E) : |weight n N m| ≤ 1 := by
  obtain ⟨i,_,_,_,heq,_⟩ := mark_cell_data hN hm
  rw [heq]
  exact actualSmallRosserPlus_abs_le_one _ _ _ _ _

/-- Exact actual selected-row double sum as a signed marked sum. Zero
coefficients are removed using their actual values, before regrouping. -/
theorem double_sum_eq_marks (n N : ℕ) (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ ordinaryTuples n N E, ∑ d ∈ selectedSupport n N t,
      selectedCoefficient n N t d * F (fullPrefix t * d)) =
      ∑ m ∈ marks n N E, weight n N m * F (modulus m) := by
  rw [marks,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro t ht
  unfold activeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : selectedCoefficient n N t d = 0 <;> simp [weight,modulus,hz]

/-- ONE literal finite modulus coefficient, unchanged for every signed
test. No existence or generic rho supplier is assumed. -/
theorem exact_pushforward (n N : ℕ) (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ ordinaryTuples n N E, ∑ d ∈ selectedSupport n N t,
      selectedCoefficient n N t d * F (fullPrefix t * d)) =
      ∑ q ∈ modulusSupport n N E, sigma n N E q * F q := by
  rw [double_sum_eq_marks]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := marks n N E) (t := modulusSupport n N E) (g := modulus)
    (fun m hm => Finset.mem_image_of_mem modulus hm) (fun m => weight n N m * F (modulus m))
  rw [← h]
  apply Finset.sum_congr rfl
  intro q hq
  unfold sigma fibre
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

theorem AP_pushforward (n N : ℕ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ ordinaryTuples n N E, selectedAP n N t) =
      ∑ q ∈ modulusSupport n N E, sigma n N E q * chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q :=
  exact_pushforward n N E _

theorem centre_pushforward (n N : ℕ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ ordinaryTuples n N E, selectedCentre n N t) =
      ∑ q ∈ modulusSupport n N E, sigma n N E q * chenCentrePrimeAPCount N N q :=
  exact_pushforward n N E _

theorem estimator_pushforward (n N : ℕ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ ordinaryTuples n N E, selectedEstimator n N t) =
      ∑ q ∈ modulusSupport n N E, sigma n N E q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) :=
  exact_pushforward n N E _

private theorem selected_row_identity {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ ordinaryTuples n N E) :
    selectedEstimator n N t = selectedMain n N t + selectedAP n N t - selectedCentre n N t := by
  obtain ⟨i,hi,_⟩ := ordinary_has_unique_active_cell hN ht
  have hterms := selected_terms_eq_fixed_cell hi.2
  rw [hterms.1,hterms.2.1,hterms.2.2.1,hterms.2.2.2]
  have hcell := (Finset.mem_filter.mp hi.2).1
  obtain ⟨hsource,hgeom⟩ := Finset.mem_filter.mp hcell
  exact U1011OriginalFifteenFixedCellNative.estimator_same_coefficient hN hsource (policy i)
    (policy_lt_fifteen i) (gridBox n i.2) (gridBox_valid n i.2)
    (gridBox_lower_positive n i.2 3) ((mem_activeCells i).mp hi.1) (cell_subset_closed_box n i.2 hgeom)

/-- The true finite main also uses the SAME sigma/phi(q). Its equality is
derived from the native same-rho identity and actual AP definition. -/
theorem main_pushforward {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ ordinaryTuples n N E, selectedMain n N t) =
      ∑ q ∈ modulusSupport n N E, sigma n N E q *
        (trueLogarithmicIntegral N / (Nat.totient q : ℝ)) := by
  have hrows : (∑ t ∈ ordinaryTuples n N E, selectedEstimator n N t) =
      ∑ t ∈ ordinaryTuples n N E, selectedMain n N t + selectedAP n N t - selectedCentre n N t :=
    Finset.sum_congr rfl (fun t ht => selected_row_identity hN ht)
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,estimator_pushforward,
    AP_pushforward,centre_pushforward] at hrows
  have hsplit :
      (∑ q ∈ modulusSupport n N E, sigma n N E q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) =
      (∑ q ∈ modulusSupport n N E, sigma n N E q *
        (trueLogarithmicIntegral N / (Nat.totient q : ℝ))) +
      (∑ q ∈ modulusSupport n N E, sigma n N E q * chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q) -
      ∑ q ∈ modulusSupport n N E, sigma n N E q * chenCentrePrimeAPCount N N q := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    unfold chenQuotientPrimeAPError
    ring
  linarith

def levelValues (n : ℕ) : Finset ℚ := insert (1 / 2)
  ((activeCells n).image (fun i => U1011OriginalFifteenFixedCellNative.nu (policy i) (gridBox n i.2)))
theorem levelValues_nonempty (n : ℕ) : (levelValues n).Nonempty := ⟨1 / 2,Finset.mem_insert_self _ _⟩
def maxLevel (n : ℕ) : ℚ := (levelValues n).max' (levelValues_nonempty n)

/-- A finite maximum is fixed BEFORE N; every actual physical modulus
is below its power. No square-root or PP license follows merely from this. -/
theorem mark_modulus_lt_maxLevel {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {m : Mark} (hm : m ∈ marks n N E) :
    (modulus m : ℝ) < (N : ℝ) ^ (maxLevel n : ℝ) := by
  obtain ⟨i,hi,ht,hd,heq,hnz⟩ := mark_cell_data hN hm
  have hcell := (Finset.mem_filter.mp ht).1
  obtain ⟨hsource,hgeom⟩ := Finset.mem_filter.mp hcell
  have hcap := U1011OriginalFifteenFixedCellNative.active_full_modulus_cap hN hsource
    (policy i) (policy_lt_fifteen i) (gridBox n i.2) (cell_subset_closed_box n i.2 hgeom) hnz
  have hlevelQ : U1011OriginalFifteenFixedCellNative.nu (policy i) (gridBox n i.2) ≤ maxLevel n := by
    apply Finset.le_max'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  have hlevel : (U1011OriginalFifteenFixedCellNative.nu (policy i) (gridBox n i.2) : ℝ) ≤
      (maxLevel n : ℝ) := by exact_mod_cast hlevelQ
  have hdpos := (active_parameters (⟨i,hi⟩ : ActiveCell n)).2.1
  have hdposR : (0 : ℝ) < (U1011OriginalFifteenFixedCellNative.delta (policy i) (gridBox n i.2) : ℝ) := by
    exact_mod_cast hdpos
  exact hcap.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Nat.le_of_lt hN)) (by linarith))

theorem sigma_zero_off_support {n N q : ℕ} {E : ℕ × ℕ → Prop}
    (hq : q ∉ modulusSupport n N E) : sigma n N E q = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm,hmod⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m,hm,hmod⟩)).elim

theorem sigma_abs_le_fibre_card {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) (q : ℕ) :
    |sigma n N E q| ≤ ((fibre n N E q).card : ℝ) := by
  unfold sigma
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ m ∈ fibre n N E q, |weight n N m|) ≤ ∑ _m ∈ fibre n N E q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mark_weight_abs_le_one hN (Finset.mem_filter.mp hm).1
    _ = _ := by simp

end
end ImbalancedChen.P5Z.U1011OriginalFifteenModulusConvolution
