import ImbalancedChen.P5ActualOccurrencePlateauWordBudget
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Concrete complete-product eta and original-group psi. The cutoffs, their
logarithmic finite-order constants and actual occurrence-word bounds are
constructed, not supplied as derivative-envelope fields. Marked arithmetic
coordinates and rho do not enter this independent geometric chart.
-/
namespace ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open ActualOccurrencePlateauWordBudget
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift

/-- A single fixed complete-product trim, before target and chart choices. -/
def eta (s : ℝ) : ℝ := Real.smoothTransition (s - 1)
def chi (s : ℝ) : ℝ := 1 - eta s
def psi (s : ℝ) : ℝ := chi s - chi (2 * s)
def etaLog (x : ℝ) : ℝ := eta (Real.exp x)
def psiLog (x : ℝ) : ℝ := psi (Real.exp x)

theorem eta_smooth : ContDiff ℝ ∞ eta :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
theorem psi_smooth : ContDiff ℝ ∞ psi := by
  unfold psi chi
  exact (contDiff_const.sub eta_smooth).sub
    (contDiff_const.sub (eta_smooth.comp (contDiff_const.mul contDiff_id)))
theorem etaLog_smooth : ContDiff ℝ ∞ etaLog := eta_smooth.comp Real.contDiff_exp
theorem psiLog_smooth : ContDiff ℝ ∞ psiLog := psi_smooth.comp Real.contDiff_exp

theorem eta_bounds (s : ℝ) : 0 ≤ eta s ∧ eta s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
theorem eta_zero {s : ℝ} (hs : s ≤ 1) : eta s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem eta_one {s : ℝ} (hs : 2 ≤ s) : eta s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem psi_eq_eta_difference (s : ℝ) : psi s = eta (2 * s) - eta s := by
  unfold psi chi
  ring

theorem etaLog_zero {x : ℝ} (hx : x ≤ 0) : etaLog x = 0 :=
  eta_zero (Real.exp_le_one_iff.mpr hx)
theorem etaLog_one {x : ℝ} (hx : Real.log 2 ≤ x) : etaLog x = 1 := by
  apply eta_one
  calc
    (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp x := Real.exp_le_exp.mpr hx

theorem etaLog_derivative_zero_left (n : ℕ) {x : ℝ} (hx : x < 0) :
    iteratedDeriv n etaLog x = 0 := by
  have heq : etaLog =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact etaLog_zero hy.le
  simpa using Filter.EventuallyEq.iteratedDeriv_eq n heq

theorem etaLog_derivative_zero_right (n : ℕ) (hn : 0 < n)
    {x : ℝ} (hx : Real.log 2 < x) : iteratedDeriv n etaLog x = 0 := by
  have heq : etaLog =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact etaLog_one hy.le
  simpa [iteratedDeriv_const, if_neg hn.ne'] using
    Filter.EventuallyEq.iteratedDeriv_eq n heq

/-- A bound for each actual scalar log-Euler order, including order zero. -/
theorem exists_etaLog_order_bound (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, |iteratedDeriv n etaLog x| ≤ C := by
  cases n with
  | zero =>
      refine ⟨1, le_rfl, ?_⟩
      intro x
      simp only [iteratedDeriv_zero]
      change |eta (Real.exp x)| ≤ 1
      rw [abs_of_nonneg (eta_bounds (Real.exp x)).1]
      exact (eta_bounds (Real.exp x)).2
  | succ n =>
      have hcont : Continuous (iteratedDeriv (n + 1) etaLog) :=
        ContDiff.continuous_iteratedDeriv (n + 1) etaLog_smooth (by simp)
      obtain ⟨B, hB⟩ :=
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Real.log 2))).exists_bound_of_continuousOn
          hcont.continuousOn
      refine ⟨max B 1, le_max_right _ _, ?_⟩
      intro x
      by_cases hl : x < 0
      · rw [etaLog_derivative_zero_left (n + 1) hl, abs_zero]
        exact zero_le_one.trans (le_max_right _ _)
      by_cases hr : Real.log 2 < x
      · rw [etaLog_derivative_zero_right (n + 1) (by omega) hr, abs_zero]
        exact zero_le_one.trans (le_max_right _ _)
      have hb : |iteratedDeriv (n + 1) etaLog x| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB x ⟨le_of_not_gt hl, le_of_not_gt hr⟩
      exact hb.trans (le_max_left _ _)

theorem psiLog_zero_left {x : ℝ} (hx : x ≤ -Real.log 2) : psiLog x = 0 := by
  have he : Real.exp x ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp x ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hx
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [psiLog, psi_eq_eta_difference, eta_zero (by linarith : 2 * Real.exp x ≤ 1),
    eta_zero (by linarith : Real.exp x ≤ 1), sub_self]

theorem psiLog_zero_right {x : ℝ} (hx : Real.log 2 ≤ x) : psiLog x = 0 := by
  have he : 2 ≤ Real.exp x := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  rw [psiLog, psi_eq_eta_difference, eta_one (by linarith : 2 ≤ 2 * Real.exp x),
    eta_one he, sub_self]

theorem psiLog_compact : HasCompactSupport psiLog := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-Real.log 2) (Real.log 2)))
  intro x hx
  constructor
  · by_contra h
    exact hx (psiLog_zero_left (lt_of_not_ge h).le)
  · by_contra h
    exact hx (psiLog_zero_right (lt_of_not_ge h).le)

theorem psiLog_iterated_compact (n : ℕ) : HasCompactSupport (iteratedDeriv n psiLog) := by
  induction n with
  | zero => simpa using psiLog_compact
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem exists_psiLog_order_bound (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, |iteratedDeriv n psiLog x| ≤ C := by
  let f := iteratedDeriv n psiLog
  have hc : HasCompactSupport f := psiLog_iterated_compact n
  have hcont : Continuous f := ContDiff.continuous_iteratedDeriv n psiLog_smooth (by simp)
  obtain ⟨B, hB⟩ := hc.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport f
  · have hb : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
    exact hb.trans (le_max_left _ _)
  · have hf : f x = 0 := by
      by_contra hn
      exact hx (subset_closure hn)
    change |f x| ≤ _
    rw [hf, abs_zero]
    exact zero_le_one.trans (le_max_right _ _)

/-- Finite-order maximization, before every translation and scale. -/
theorem finite_order_constants (f : ℝ → ℝ)
    (hb : ∀ n : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ x, |iteratedDeriv n f x| ≤ C)
    (r : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n ≤ r, ∀ x, |iteratedDeriv n f x| ≤ C := by
  induction r with
  | zero =>
      obtain ⟨C, hC, h⟩ := hb 0
      exact ⟨C, hC, fun n hn x => by have : n = 0 := by omega; simpa [this] using h x⟩
  | succ r ih =>
      obtain ⟨C, hC, h⟩ := ih
      obtain ⟨D, hD, hd⟩ := hb (r + 1)
      refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
      intro n hn x
      by_cases hnr : n ≤ r
      · exact (h n hnr x).trans (le_max_left _ _)
      · have : n = r + 1 := by omega
        simpa [this] using (hd x).trans (le_max_right C D)

def scalarLift {m : ℕ} (b : ℝ) (f : ℝ → ℝ) (z : Fin m → ℝ) : ℝ :=
  f (b + ∑ a, z a)

theorem sum_shift {m : ℕ} (z : Fin m → ℝ) (a : Fin m) (t : ℝ) :
    (∑ b, (z + Pi.single a t) b) = (∑ b, z b) + t := by
  simpa [groupLog] using
    groupLog_shift (fun _ : Fin m => (0 : Fin 1)) 0 z a t

theorem occOne_scalarLift {m : ℕ} (a : Fin m) (b : ℝ) (f : ℝ → ℝ)
    (z : Fin m → ℝ) : occOne a (scalarLift b f) z = scalarLift b (deriv f) z := by
  have heq : (fun t : ℝ => scalarLift b f (z + Pi.single a t)) =
      fun t => f ((b + ∑ a, z a) + t) := by
    funext t
    simp [scalarLift, sum_shift, add_assoc]
  rw [occOne, heq, deriv_comp_const_add]
  simp [scalarLift]

theorem occWord_scalarLift {m : ℕ} (w : List (Fin m)) (b : ℝ) (f : ℝ → ℝ) :
    occWord w (scalarLift b f) = scalarLift b (iteratedDeriv w.length f) := by
  induction w with
  | nil => simp [occWord]
  | cons a w ih =>
      change occOne a (occWord w (scalarLift b f)) = _
      rw [ih]
      funext z
      rw [occOne_scalarLift]
      simp [iteratedDeriv_succ]

/-- Different original groups are independent. A letter changes precisely
its unique owner's scalar factor, even when owner labels repeat. -/
def groupTensor {k m : ℕ} (owner : Fin m → Fin k) (b : Fin k → ℝ)
    (g : Fin k → ℝ → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∏ i, g i (b i + groupLog owner i z)

theorem occOne_groupTensor {k m : ℕ} (owner : Fin m → Fin k)
    (b : Fin k → ℝ) (g : Fin k → ℝ → ℝ) (a : Fin m) (z : Fin m → ℝ) :
    occOne a (groupTensor owner b g) z =
      groupTensor owner b (Function.update g (owner a) (deriv (g (owner a)))) z := by
  let j := owner a
  let rest := ∏ i ∈ (Finset.univ.erase j), g i (b i + groupLog owner i z)
  have hcurve : (fun t : ℝ => groupTensor owner b g (z + Pi.single a t)) =
      fun t => g j ((b j + groupLog owner j z) + t) * rest := by
    funext t
    unfold groupTensor
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp [j, groupLog_shift, add_assoc]
    · apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [groupLog_shift, j, Ne.symm hij, rest]
  have hout : groupTensor owner b (Function.update g j (deriv (g j))) z =
      deriv (g j) (b j + groupLog owner j z) * rest := by
    unfold groupTensor
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [Function.update_of_ne hij, rest]
  rw [occOne, hcurve, deriv_mul_const_field, deriv_comp_const_add]
  simpa [j] using hout.symm

theorem occWord_groupTensor {k m : ℕ} (owner : Fin m → Fin k)
    (b : Fin k → ℝ) (f : ℝ → ℝ) (w : List (Fin m)) :
    occWord w (groupTensor owner b (fun _ => f)) =
      groupTensor owner b (fun i => iteratedDeriv ((w.map owner).count i) f) := by
  induction w with
  | nil => simp [occWord]
  | cons a w ih =>
      change occOne a (occWord w (groupTensor owner b (fun _ => f))) = _
      rw [ih]
      funext z
      rw [occOne_groupTensor]
      congr 1
      funext i x
      by_cases hi : i = owner a
      · subst i
        simp [iteratedDeriv_succ]
      · simp [hi, Ne.symm hi, Function.update_of_ne hi]

theorem count_le_word_length {α : Type*} [DecidableEq α] (w : List α) (i : α) :
    w.count i ≤ w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
      by_cases h : a = i <;> simp [h, ih] <;> omega

theorem groupTensor_word_bound {k m : ℕ} (owner : Fin m → Fin k)
    (b : Fin k → ℝ) (f : ℝ → ℝ) (w : List (Fin m)) (z : Fin m → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n ≤ w.length, ∀ x, |iteratedDeriv n f x| ≤ M) :
    |occWord w (groupTensor owner b (fun _ => f)) z| ≤ M ^ k := by
  rw [occWord_groupTensor]
  unfold groupTensor
  rw [Finset.abs_prod]
  calc
    (∏ i, |iteratedDeriv ((w.map owner).count i) f (b i + groupLog owner i z)|) ≤
        ∏ _i : Fin k, M := by
      apply Finset.prod_le_prod (fun i hi => abs_nonneg _)
      intro i hi
      apply hb
      simpa using (count_le_word_length (w.map owner) i)
    _ = M ^ k := by simp

theorem groupLog_total {k m : ℕ} (owner : Fin m → Fin k) (z : Fin m → ℝ) :
    (∑ i, groupLog owner i z) = ∑ a, z a := by
  unfold groupLog
  rw [Finset.sum_comm]
  simp

theorem completeProduct {k m : ℕ} (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (z : Fin m → ℝ) :
    (∏ i, groupProduct owner U i z) =
      (∏ i, groupBase owner U i) * Real.exp (∑ a, z a) := by
  simp only [groupProduct, Finset.prod_mul_distrib, ← Real.exp_sum, groupLog_total]

def actualEta {k m : ℕ} (T : ℕ) (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (kappa0 : ℝ) (z : Fin m → ℝ) : ℝ :=
  eta ((∏ i, groupProduct owner U i z) / (T : ℝ) ^ (1 - kappa0))
def actualPsi {k m : ℕ} (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (R : Fin k → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∏ i, psi (groupProduct owner U i z / R i)

theorem actualEta_eq_scalarLift {k m : ℕ} (T : ℕ) (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (kappa0 : ℝ) (hT : 0 < (T : ℝ)) (hU : ∀ a, 0 < U a) :
    actualEta T owner U kappa0 =
      scalarLift (Real.log ((∏ i, groupBase owner U i) / (T : ℝ) ^ (1 - kappa0))) etaLog := by
  have hb : 0 < (∏ i, groupBase owner U i) / (T : ℝ) ^ (1 - kappa0) :=
    div_pos (Finset.prod_pos (fun i hi => groupBase_pos owner U hU i))
      (Real.rpow_pos_of_pos hT _)
  funext z
  unfold actualEta scalarLift etaLog
  rw [Real.exp_add, Real.exp_log hb, completeProduct]
  congr 1
  ring

theorem actualPsi_eq_groupTensor {k m : ℕ} (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (R : Fin k → ℝ) (hU : ∀ a, 0 < U a) (hR : ∀ i, 0 < R i) :
    actualPsi owner U R = groupTensor owner
      (fun i => Real.log (groupBase owner U i / R i)) (fun _ => psiLog) := by
  funext z
  unfold actualPsi groupTensor
  apply Finset.prod_congr rfl
  intro i hi
  unfold psiLog groupProduct
  rw [Real.exp_add, Real.exp_log (div_pos (groupBase_pos owner U hU i) (hR i))]
  congr 1
  ring

theorem actualEta_smooth {k m : ℕ} (T : ℕ) (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (kappa0 : ℝ) : ContDiff ℝ ∞ (actualEta T owner U kappa0) := by
  unfold actualEta
  apply eta_smooth.comp
  apply ContDiff.div_const
  apply contDiff_prod
  intro i hi
  exact groupProduct_smooth owner U i

theorem actualPsi_smooth {k m : ℕ} (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (R : Fin k → ℝ) : ContDiff ℝ ∞ (actualPsi owner U R) := by
  unfold actualPsi
  apply contDiff_prod
  intro i hi
  exact psi_smooth.comp ((groupProduct_smooth owner U i).div_const (R i))

def actualChart {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (kappa0 : ℝ) (z : Fin m → ℝ) : ℝ :=
  A.ambient T k (fun i => groupProduct owner U i z) *
    actualEta T owner U kappa0 z * actualPsi owner U R z * plateau m z

theorem actualChart_smooth {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (kappa0 : ℝ) :
    ContDiff ℝ ∞ (actualChart A T k owner U R kappa0) := by
  exact (((family_grouped_smooth A T k owner U).mul
    (actualEta_smooth T owner U kappa0)).mul (actualPsi_smooth owner U R)).mul
    (plateau_smooth m)

theorem actualChart_compact {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (kappa0 : ℝ) :
    HasCompactSupport (actualChart A T k owner U R kappa0) := by
  apply (plateau_compact m).mono'
  intro z hz
  apply subset_tsupport (plateau m)
  intro heq
  exact hz (by simp [actualChart, heq])

/-- A genuine fixed polylog budget for the complete actual geometric chart.
All three cutoff budgets are proved above or in batch 30b; none is supplied
as a final chart-envelope premise. The bound is ready for D_T integration. -/
theorem exists_actualChart_word_budget {kStar : ℕ} (A : Family kStar) :
    ∃ C : ℝ, ∃ B : ℕ, 0 ≤ C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ)
        (kappa0 : ℝ) (w : List (Fin m)) (z : Fin m → ℝ),
        0 < (T : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
        m ≤ 6 * kStar → w.length ≤ 12 * kStar →
        |occWord w (actualChart A T k owner U R kappa0) z| ≤
          C * Real.log ((T : ℝ) + 2) ^ B := by
  obtain ⟨CA, B, MC, hCA, hMC, hfamily⟩ := family_chart_actual_plateau_bound A
  obtain ⟨ME, hME, be⟩ := finite_order_constants etaLog exists_etaLog_order_bound (12 * kStar)
  obtain ⟨MP, hMP, bp⟩ := finite_order_constants psiLog exists_psiLog_order_bound (12 * kStar)
  let C : ℝ := (4 : ℝ) ^ (12 * kStar) * (CA : ℝ) * ME * MP ^ kStar * MC
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, B, hC, ?_⟩
  intro T k m owner U R kappa0 w z hT hU hR hm hw
  have he : ∀ v : List (Fin m), v.length ≤ 12 * kStar →
      |occWord v (actualEta T owner U kappa0) z| ≤ ME := by
    intro v hv
    rw [actualEta_eq_scalarLift T owner U kappa0 hT hU, occWord_scalarLift]
    exact be v.length hv _
  have hp : ∀ v : List (Fin m), v.length ≤ 12 * kStar →
      |occWord v (actualPsi owner U R) z| ≤ MP ^ kStar := by
    intro v hv
    rw [actualPsi_eq_groupTensor owner U R hU hR]
    apply (groupTensor_word_bound owner _ psiLog v z MP (zero_le_one.trans hMP)
      (fun n hn x => bp n (hn.trans hv) x)).trans
    exact pow_le_pow_right₀ hMP (rank_le A k)
  have hraw := hfamily T k m owner U w z
    (actualEta T owner U kappa0) (actualPsi owner U R) ME (MP ^ kStar) hm hw
    (actualEta_smooth T owner U kappa0) (actualPsi_smooth owner U R)
    (zero_le_one.trans hME) (by positivity) he hp
  have hlog : 0 ≤ Real.log ((T : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hmul : 0 ≤ ((CA : ℝ) * Real.log ((T : ℝ) + 2) ^ B) * ME * MP ^ kStar * MC :=
    by positivity
  calc
    |occWord w (actualChart A T k owner U R kappa0) z| ≤
        (4 : ℝ) ^ w.length *
          (((CA : ℝ) * Real.log ((T : ℝ) + 2) ^ B) * ME * MP ^ kStar * MC) := hraw
    _ ≤ (4 : ℝ) ^ (12 * kStar) *
          (((CA : ℝ) * Real.log ((T : ℝ) + 2) ^ B) * ME * MP ^ kStar * MC) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) hmul
    _ = C * Real.log ((T : ℝ) + 2) ^ B := by dsimp [C]; ring

end
end ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget
