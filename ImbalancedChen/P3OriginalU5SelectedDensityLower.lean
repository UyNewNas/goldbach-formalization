import ImbalancedChen.P3OriginalU5FrontierParameters
import ImbalancedChen.P3OriginalU5ResidualComparison
import ImbalancedChen.P3OriginalU5OrdinaryRootDensity

/-! Positive signed density of the literal original U5 selected policy.
Only changed frontiers incur the uniform Rosser comparison error. Their
actual reciprocal weights, with all occurrences retained, are bounded by
the proved fixed receiver window. No positivity or distribution hypothesis
is imposed on the selected policy. -/

namespace ImbalancedChen.P3OriginalU5SelectedDensityLower

noncomputable section
open scoped Classical List BigOperators
open P2LowerCapPlanIntegerRetention (coordinate)
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P3OriginalU5WarmRosserAdmission (incoming rowLevel)
open P3OriginalU5ThreeFrontierIdentity (frontierChange original_U5_fullDensity_eq_three_frontiers)
open P3OriginalU5ChangedFrontierSupport (changedHistories changedMass
  original_U5_changed_frontier_window eventually_original_U5_changedMass_le)
open P3OriginalU5FrontierParameters (residualExponent original_U5_frontier_parameters)
open P3OriginalU5ResidualComparison (exists_ordinary_residual_comparison)
open P3OriginalU5OrdinaryRootDensity (ordinaryRootDensity exists_ordinary_root_row_lower
  exists_pairSupport_harmonic_lower)
open P5OriginalU5CausalFinite (pairSupport cutoff fullDensity)

private abbrev weight (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

private def changeTerm (N enum : ℕ) (Q : List ℕ → ℝ) (H : List ℕ) : ℝ :=
  actualFrozenFrontierDensityTerm true N enum Q H -
    actualFrozenFrontierDensityTerm true N enum (fun K => Q K.tail) H

private theorem sum_eq_filter {α : Type*} (L : List α) (p : α → Bool) (f : α → ℝ)
    (hz : ∀ x ∈ L, p x ≠ true → f x = 0) :
    (L.map f).sum = ((L.filter p).map f).sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have ht := ih (fun y hy => hz y (List.mem_cons_of_mem x hy))
    by_cases hp : p x = true
    · simpa [hp] using congrArg (fun t => f x + t) ht
    · simpa [hp, hz x List.mem_cons_self hp] using ht

private theorem frontierChange_eq_changed_sum (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (enum k : ℕ) :
    frontierChange R bank b N t enum k =
      ((changedHistories R bank b N t enum k).map
        (changeTerm N enum (rowLevel R bank b N t))).sum := by
  let L := (firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t))
    weight [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))).map (fun s => s.selectedPrefix)
  let p (H : List ℕ) := decide ((incoming R bank b N t H).cap ≠
    (incoming R bank b N t H.tail).cap)
  have hz (H : List ℕ) (_hH : H ∈ L) (hn : p H ≠ true) :
      changeTerm N enum (rowLevel R bank b N t) H = 0 := by
    have he : (incoming R bank b N t H).cap = (incoming R bank b N t H.tail).cap := by
      by_contra hne
      exact hn (by simp only [p, decide_eq_true_eq]; exact hne)
    simp only [changeTerm, actualFrozenFrontierDensityTerm, rowLevel, he, sub_self]
  simpa only [L, p, frontierChange, changedHistories, changeTerm,
    List.map_map, Function.comp_def] using sum_eq_filter L p _ hz

private theorem changed_weight_nonneg (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum k : ℕ) (hk : 0 < k) (H : List ℕ)
    (hH : H ∈ changedHistories R bank b N t enum k) : 0 ≤ (H.map weight).prod := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have hprime := (original_U5_changed_frontier_window R bank b hN ht enum k hk H hH).2 p hp |>.1
  exact div_nonneg zero_le_one (sub_nonneg.mpr (by exact_mod_cast hprime.one_lt.le))

/-- Each displayed change is charged only on its actual changed states.
The threshold is fixed before the target, mesh, bank, buffer and marks. -/
theorem exists_original_U5_frontier_payment (R : PairRange) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N → ∀ {mesh : ℕ} (bank : CandidateBank mesh)
      (b : ℚ), 0 ≤ b → b ≤ 1/1000 → ∀ t ∈ pairSupport N, ∀ enum k : ℕ,
        1 ≤ k → k ≤ 3 →
          (-eta * singularSeries N / Real.log (N : ℝ)) * changedMass R bank b N t enum k ≤
            frontierChange R bank b N t enum k := by
  obtain ⟨N0, hN0, hcompare⟩ := exists_ordinary_residual_comparison (R.epsilon : ℝ) eta
    (by exact_mod_cast R.epsilon_pos) heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven mesh bank b hb₀ hb t ht enum k hk₁ hk₃
  have hN2 : 2 ≤ N := hN0.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let Q := rowLevel R bank b N t
  let E := -eta * singularSeries N / Real.log (N : ℝ)
  have hterm (H : List ℕ) (hH : H ∈ changedHistories R bank b N t enum k) :
      E * (H.map weight).prod ≤ changeTerm N enum Q H := by
    have hwindow := original_U5_changed_frontier_window R bank b hN2 ht enum k hk₁ H hH
    have hw := changed_weight_nonneg R bank b hN2 ht enum k hk₁ H hH
    obtain ⟨hmap, _⟩ := List.mem_filter.mp hH
    obtain ⟨s, hsFront, rfl⟩ := List.mem_map.mp hmap
    have hp := original_U5_frontier_parameters R bank b hb₀ hb hN2 ht enum k hk₁ hk₃ s hsFront
    let H := s.selectedPrefix
    let u := coordinate N (H.headD 0)
    let O := residualExponent N (Q H.tail) H
    let M := residualExponent N (Q H) H
    have hne : H ≠ [] := by
      intro he
      have hl := hp.length_eq
      change H.length = k at hl
      rw [he] at hl
      simp only [List.length_nil] at hl
      omega
    have hhead : H.headD 0 ∈ H := by
      cases he : H with
      | nil => exact (hne he).elim
      | cons p ps => exact List.mem_cons_self
    have hdu : (R.epsilon : ℝ) ≤ u := by
      apply (Real.rpow_le_rpow_left_iff hNr).mp
      rw [hp.head_power]
      exact (hwindow.2 _ hhead).2.2.1
    have hc := hcompare N hN hEven u O M hdu hp.coord_le_old hp.old_le_new hp.new_le_one
      enum (by rw [hp.head_power]; exact hp.head_le_cap)
    have hprod := mul_le_mul_of_nonneg_left hc.1 hw
    have hprod2 (hk : k = 2) := mul_le_mul_of_nonneg_left (hc.2 (hp.two_coord_le_old hk)) hw
    dsimp only [u, O, M] at hprod
    rw [hp.head_power, hp.old_power, hp.new_power] at hprod
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · have he : evenListLength s.selectedPrefix = false := by simpa using hp.parity_eq
      have hr : ordinaryRosserResidualLower true s.selectedPrefix.length = false := by
        rw [hp.length_eq]; decide
      simp only [changeTerm, actualFrozenFrontierDensityTerm, he, hr, Bool.false_eq_true,
        if_false, signedTreeCoefficient]
      nlinarith only [hprod]
    · have he : evenListLength s.selectedPrefix = true := by simpa using hp.parity_eq
      have hr : ordinaryRosserResidualLower true s.selectedPrefix.length = true := by
        rw [hp.length_eq]; decide
      have hh := hprod2 rfl
      dsimp only [u, O, M] at hh
      rw [hp.head_power, hp.old_power, hp.new_power] at hh
      simp only [changeTerm, actualFrozenFrontierDensityTerm, he, hr, if_true,
        signedTreeCoefficient]
      nlinarith only [hh]
    · have he : evenListLength s.selectedPrefix = false := by
        calc
          _ = decide (Even 3) := hp.parity_eq
          _ = false := by decide
      have hr : ordinaryRosserResidualLower true s.selectedPrefix.length = false := by
        rw [hp.length_eq]; decide
      simp only [changeTerm, actualFrozenFrontierDensityTerm, he, hr, Bool.false_eq_true,
        if_false, signedTreeCoefficient]
      nlinarith only [hprod]
  rw [frontierChange_eq_changed_sum]
  change E * ((changedHistories R bank b N t enum k).map (fun H => (H.map weight).prod)).sum ≤ _
  have hsum (L : List (List ℕ))
      (hL : ∀ H ∈ L, H ∈ changedHistories R bank b N t enum k) :
      E * (L.map (fun H => (H.map weight).prod)).sum ≤ (L.map (changeTerm N enum Q)).sum := by
    induction L with
    | nil => simp
    | cons H L ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      exact add_le_add (hterm H (hL H List.mem_cons_self))
        (ih (fun K hK => hL K (List.mem_cons_of_mem H hK)))
  exact hsum _ (fun _ h => h)

/-- A fixed receiver has a positive actual signed row density uniformly in
all finite banks, original labels, and buffers in the stated interval. -/
theorem exists_original_U5_selected_row_lower (R : PairRange) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      ∀ {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ), 0 ≤ b → b ≤ 1/1000 →
        ∀ t ∈ pairSupport N,
          c * singularSeries N / Real.log (N : ℝ) ≤ fullDensity N (selectedPolicy R bank b false N t) := by
  obtain ⟨c, hc, Nr, hNr, hroot⟩ := exists_ordinary_root_row_lower
  obtain ⟨C, hC, Nm, _, hmass⟩ := eventually_original_U5_changedMass_le R
  let eta := c / (6 * C)
  have heta : 0 < eta := div_pos hc (mul_pos (by norm_num) hC)
  obtain ⟨Ne, _, hpay⟩ := exists_original_U5_frontier_payment R eta heta
  refine ⟨c / 2, half_pos hc, max Nr (max Nm Ne), hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven mesh bank b hb₀ hb t ht
  have hr : Nr ≤ N := (le_max_left _ _).trans hN
  have hm : Nm ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have he : Ne ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := hNr.trans hr
  have hNr' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let S := singularSeries N / Real.log (N : ℝ)
  have hE : -eta * singularSeries N / Real.log (N : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le)
      (singularSeries_pos N).le) (Real.log_pos hNr').le
  have bound (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3) :
      -eta * S * C ≤ frontierChange R bank b N t (Nat.ceil (cutoff N)) k := by
    have ha := hpay N he hEven bank b hb₀ hb t ht (Nat.ceil (cutoff N)) k hk₁ hk₃
    have hbnd := mul_le_mul_of_nonpos_left (hmass N hm bank b ht (Nat.ceil (cutoff N)) k hk₁) hE
    have hall := hbnd.trans ha
    simpa only [S, mul_div_assoc] using hall
  have h1 := bound 1 (by norm_num) (by norm_num)
  have h2 := bound 2 (by norm_num) (by norm_num)
  have h3 := bound 3 (by norm_num) (by norm_num)
  have hbase := hroot N hr hEven t ht b hb₀ hb
  rw [original_U5_fullDensity_eq_three_frontiers R bank b hb hN2 ht]
  change c / 2 * singularSeries N / Real.log (N : ℝ) ≤ ordinaryRootDensity b N t + _ + _ + _
  have heq : 6 * eta * C = c := by dsimp only [eta]; field_simp [hC.ne']
  have herror : 3 * (eta * S * C) = c / 2 * S := by
    calc
      _ = (6 * eta * C) / 2 * S := by ring
      _ = _ := by rw [heq]
  change c * singularSeries N / Real.log (N : ℝ) ≤ ordinaryRootDensity b N t at hbase
  dsimp only [S] at h1 h2 h3 herror
  simp only [div_eq_mul_inv] at h1 h2 h3 hbase herror ⊢
  nlinarith only [h1, h2, h3, hbase, herror]

/-- Positive signed main density on the complete original marked pair
carrier. The receiver is fixed before the single large-target threshold. -/
theorem exists_original_U5_selected_pair_lower (R : PairRange) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      ∀ {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ), 0 ≤ b → b ≤ 1/1000 →
        c * singularSeries N / Real.log (N : ℝ) ≤
          ∑ t ∈ pairSupport N, fullDensity N (selectedPolicy R bank b false N t) /
            (Nat.totient (t.1 * t.2) : ℝ) := by
  obtain ⟨c, hc, Nr, hNr, hrow⟩ := exists_original_U5_selected_row_lower R
  obtain ⟨H, hH, Nm, _, hmass⟩ := exists_pairSupport_harmonic_lower
  refine ⟨c * H, mul_pos hc hH, max Nr Nm, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven mesh bank b hb₀ hb
  have hr : Nr ≤ N := (le_max_left _ _).trans hN
  have hm : Nm ≤ N := (le_max_right _ _).trans hN
  have hNr' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let A := c * singularSeries N / Real.log (N : ℝ)
  have hA : 0 ≤ A := (div_pos (mul_pos hc (singularSeries_pos N)) (Real.log_pos hNr')).le
  calc
    _ = A * H := by dsimp only [A]; ring
    _ ≤ A * (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass N hm) hA
    _ = ∑ t ∈ pairSupport N, A / (Nat.totient (t.1 * t.2) : ℝ) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun t ht =>
      div_le_div_of_nonneg_right (hrow N hr hEven bank b hb₀ hb t ht) (Nat.cast_nonneg _))

end
end ImbalancedChen.P3OriginalU5SelectedDensityLower
