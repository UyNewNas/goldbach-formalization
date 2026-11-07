import ImbalancedChen.P5ActualIndependentUpperPairProfile
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The current real-b consumer quantifies over every positive physical width
with 2*width <= baseline b kappa - nu*r.  The earlier G/H independent
profile uses a different, mass-selected width.  This file constructs the
literal original pair at EVERY width in the current consumer's domain.
It proves the smooth zero extension and width-dependent ordered Euler
bounds; it assumes neither a profile licence nor a PP estimate.
-/
namespace ImbalancedChen.P4BArbitraryWidthUpperPairProfile
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open P4B P4BOuterRampRoughness P4BActualSmoothCompleteProductWindow
open P5Z.AdmissibleAllRankIntegerGeometricFamily
open P5Z.NativeSelectedFourOrderedEuler P5Z.LicensedOriginalIntegerProfile

def profile (b kappa width : ℝ) (N : ℕ) (p : Fin 2 → ℝ) : ℝ :=
  if 2 ≤ N then
    if p ∈ positivePrimeOrthant then
      smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N) width p
    else 0
  else 0

def integerWeight (b kappa width : ℝ) (N : ℕ) (u : Fin 2 → ℕ) : ℝ :=
  profile b kappa width N (fun i => (u i : ℝ))

/-- The lower original-prime exponent is precisely nu*r, with no new
strict-gap assumption. The two complete-product walls retain their
different scales: N^(1-kappa-width) and exp(width)*N. -/
theorem nonzero_data {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    {p : Fin 2 → ℝ} (hn : profile b kappa width N p ≠ 0) :
    2 ≤ N ∧ p ∈ positivePrimeOrthant ∧
      (∀ i, (N : ℝ) ^ (nu * r) < p i) ∧
      (N : ℝ) ^ (1 - kappa - width) < p 0 * p 1 ∧
      p 0 * p 1 < Real.exp width * (N : ℝ) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hn (by simp [profile, h])
  have hp : p ∈ positivePrimeOrthant := by
    by_contra h
    exact hn (by simp [profile, hN, h])
  have hraw : smoothPrimeVariableProfile b N
      (manuscriptHalfProductCutoff kappa N) width p ≠ 0 := by
    simpa only [profile, if_pos hN, if_pos hp] using hn
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact ⟨hN, hp,
    smoothPrimeVariableProfile_nonzero_above_rpow hb (mul_pos hnu hr)
      hN hwidth hgap hp hraw,
    nonzero_smoothPrimeProfile_complete_product_lower hN hwidth hp hraw,
    smoothPrimeVariableProfile_nonzero_product_lt_exp_mul_N hN1 hwidth hp hraw⟩

theorem eventually_zero_nonpositive {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (N : ℕ) (p : Fin 2 → ℝ) (hnp : ∃ i, p i ≤ 0) :
    profile b kappa width N =ᶠ[𝓝 p] 0 := by
  by_cases hN : 2 ≤ N
  · obtain ⟨i, hi⟩ := hnp
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    let L : ℝ := (N : ℝ) ^ (nu * r)
    have hL : 0 < L := Real.rpow_pos_of_pos hNr _
    have hopen : IsOpen {x : Fin 2 → ℝ | x i < L} :=
      isOpen_lt (continuous_apply i) continuous_const
    filter_upwards [hopen.mem_nhds (hi.trans_lt hL)] with x hx
    by_contra hn
    have hs := (nonzero_data hb hnu hr hwidth hgap hn).2.2.1 i
    exact (not_lt_of_ge hx.le) hs
  · simp only [profile, if_neg hN]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem eventually_raw (b kappa width : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin 2 → ℝ) (hp : p ∈ positivePrimeOrthant) :
    profile b kappa width N =ᶠ[𝓝 p]
      smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N) width := by
  filter_upwards [isOpen_positivePrimeOrthant_forEuler.mem_nhds hp] with x hx
  simp only [profile, if_pos hN, if_pos hx]

/-- The genuine extension across the coordinate axes is smooth because
its nonzero support stays above N^(nu*r), not because of a sharp cutoff. -/
theorem smooth {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) :
    ContDiff ℝ ∞ (profile b kappa width N) := by
  by_cases hN : 2 ≤ N
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ positivePrimeOrthant
    · exact ((contDiffOn_smoothPrimeVariableProfile b N
        (manuscriptHalfProductCutoff kappa N) width).
          contDiffAt (isOpen_positivePrimeOrthant_forEuler.mem_nhds hp)).
        congr_of_eventuallyEq (eventually_raw b kappa width hN p hp)
    · have hnp : ∃ i, p i ≤ 0 := by
        change ¬ ∀ i, 0 < p i at hp
        push_neg at hp
        exact hp
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin 2 → ℝ => (0 : ℝ)) p).
        congr_of_eventuallyEq (eventually_zero_nonpositive hb hnu hr hwidth hgap N p hnp)
  · simp only [profile, if_neg hN]
    exact contDiff_const

theorem bounds (b kappa width : ℝ) (N : ℕ) (p : Fin 2 → ℝ) :
    0 ≤ profile b kappa width N p ∧ profile b kappa width N p ≤ 1 := by
  unfold profile
  split_ifs
  · exact smoothPhysicalProfile_bounds _ _ _ _ _
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem original_caller (b kappa width : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (u : Fin 2 → Fin (N + 1)) (hu : u ∈ Part3.labelledPrimeTuples 2 N) :
    smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width u =
      profile b kappa width N (primeTuplePoint N u) := by
  have hp := primeTuplePoint_mem_positivePrimeOrthant hu
  simp only [profile, if_pos hN, if_pos hp]
  exact smoothPhysicalPairOuterRamp_eq_primeVariableProfile _ _ _ _ _

def licence {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) :
    Licence 2 (integerWeight b kappa width N) where
  ambient := profile b kappa width N
  smooth := smooth hb hnu hr hwidth hgap N
  agrees_on_primes := by intro u hu; rfl

theorem finite_integer_support {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) (N : ℕ) :
    Set.Finite {u : Fin 2 → ℕ | integerWeight b kappa width N u ≠ 0} := by
  let M := Nat.ceil (Real.exp width * (N : ℝ))
  let bank : Finset (Fin 2 → ℕ) := Fintype.piFinset (fun _ => Finset.range (M + 1))
  apply bank.finite_toSet.subset
  intro u hu
  have hs := nonzero_data hb hnu hr hwidth hgap hu
  have hu0n : 0 < u 0 := by exact_mod_cast hs.2.1 0
  have hu1n : 0 < u 1 := by exact_mod_cast hs.2.1 1
  have hu0 : (1 : ℝ) ≤ u 0 := by exact_mod_cast (show 1 ≤ u 0 from hu0n)
  have hu1 : (1 : ℝ) ≤ u 1 := by exact_mod_cast (show 1 ≤ u 1 from hu1n)
  have hprod := hs.2.2.2.2
  have hceil : Real.exp width * (N : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  apply Finset.mem_piFinset.mpr
  intro i
  have hbound : (u i : ℝ) ≤ M := by
    fin_cases i <;> nlinarith
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast hbound))

/-- All legal widths share one eventual cap threshold at fixed b,kappa,
nu,r. This is full real support; no new truncation is added to the source. -/
theorem eventually_full_support_inside_original_cap
    {b kappa nu r : ℝ} (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ) := by
  let widthMax : ℝ := (baseline b kappa - nu * r) / 2
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (nu * r)) atTop atTop :=
    (Real.tendsto_rpow_atTop (mul_pos hnu hr)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (Real.exp widthMax)] with N hscale
  intro width hwidth hgap p hn
  have hwle : width ≤ widthMax := by dsimp only [widthMax]; linarith only [hgap]
  have hexp : Real.exp width ≤ (N : ℝ) ^ (nu * r) :=
    (Real.exp_le_exp.mpr hwle).trans hscale
  have hs := nonzero_data hb hnu hr hwidth hgap hn
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by have hN := hs.1; omega)
  have h0 := hexp.trans_lt (hs.2.2.1 0)
  have h1 := hexp.trans_lt (hs.2.2.1 1)
  have hp0 := hs.2.1 0
  have hp1 := hs.2.1 1
  have hprod := hs.2.2.2.2
  intro i
  fin_cases i <;> by_contra h <;> have hh := le_of_not_gt h <;> nlinarith

/-- The constant precedes every legal width, target and prime point.
The only width loss is the actual q-th derivative factor width^(-q). -/
theorem fixed_order_width_budget (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ N (w : List (Fin 2)) p, w.length = q →
        |eulerWord w (profile b kappa width N) p| ≤ C / width ^ q := by
  obtain ⟨C, hC, hbudget⟩ :=
    exists_compact_realB_prime_EulerWord_budget q (bHi := 1) zero_le_one
  refine ⟨C, hC, ?_⟩
  intro b kappa nu r width hb hbOne hnu hr hwidth hgap N w p hw
  by_cases hN : 2 ≤ N
  · by_cases hp : p ∈ positivePrimeOrthant
    · rw [(P5ActualIndependentUpperPairProfile.eulerWord_eventuallyEq w _ _ p
        (eventually_raw b kappa width hN p hp)).eq_of_nhds,
        P5ActualIndependentUpperPairProfile.actual_ordered_word_dictionary]
      subst q
      exact hbudget b hb.le hbOne width hwidth N hN _ p hp
        (P5ActualIndependentUpperPairProfile.wordArray w)
    · have hnp : ∃ i, p i ≤ 0 := by
        change ¬ ∀ i, 0 < p i at hp
        push_neg at hp
        exact hp
      rw [(eulerWord_eventually_zero w _ p
        (eventually_zero_nonpositive hb hnu hr hwidth hgap N p hnp)).eq_of_nhds,
        abs_zero]
      exact div_nonneg hC (pow_nonneg hwidth.le _)
  · have hz : profile b kappa width N = 0 := by simp [profile, hN]
    rw [(eulerWord_eventually_zero w _ p
      (Filter.Eventually.of_forall (fun x => congrFun hz x))).eq_of_nhds, abs_zero]
    exact div_nonneg hC (pow_nonneg hwidth.le _)

theorem legal_width_le_one {b kappa nu r width : ℝ}
    (hb : 0 < b) (hkappa : 0 < kappa) (hnu : 0 < nu) (hr : 0 < r)
    (hgap : 2 * width ≤ baseline b kappa - nu * r) : width ≤ 1 := by
  have hden : 0 < 1 + b := by linarith only [hb]
  have hbase : baseline b kappa < 1 := by
    unfold baseline
    apply (div_lt_iff₀ hden).2
    have hp := mul_pos hkappa hb
    nlinarith only [hp]
  have hp := mul_pos hnu hr
  linarith only [hgap, hbase, hp]

/-- One common constant covers every order up to q, every legal positive
width and all repeated ordered letters. No constant is claimed uniform
as width tends to zero without the displayed width^(-q) factor. -/
theorem mixed_width_budget (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ N (w : List (Fin 2)) p, w.length ≤ q →
        |eulerWord w (profile b kappa width N) p| ≤ C / width ^ q := by
  choose M hM hbound using (fun d : Fin (q + 1) => fixed_order_width_budget d.val)
  let C : ℝ := ∑ d : Fin (q + 1), M d
  refine ⟨C, Finset.sum_nonneg (fun d _ => hM d), ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap N w p hw
  let i : Fin (q + 1) := ⟨w.length, by omega⟩
  have hm := hbound i b kappa nu r width hb hbOne hnu hr hwidth hgap N w p rfl
  have hs : M i ≤ C := Finset.single_le_sum (fun d _ => hM d) (Finset.mem_univ i)
  have hp : width ^ q ≤ width ^ w.length :=
    pow_le_pow_of_le_one hwidth.le (legal_width_le_one hb hkappa hnu hr hgap) hw
  calc
    _ ≤ M i / width ^ w.length := hm
    _ ≤ M i / width ^ q := div_le_div_of_nonneg_left (hM i) (pow_pos hwidth _) hp
    _ ≤ C / width ^ q := div_le_div_of_nonneg_right hs (pow_nonneg hwidth.le _)

/-- The equality uses the RAW original source. The same signed rho
occurs in its AP term and exact coprime mean. -/
theorem original_signed_source (b kappa width : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 2 N N Q rho
      (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) =
      Part3.primeProductSignedError 2 N N Q rho
        (fun u => integerWeight b kappa width N (fun i => (u i).val)) := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [original_caller b kappa width hN u hu]
  rfl

theorem attachedUpper_signed_source (b kappa nu r epsilon width : ℝ)
    {N : ℕ} (hN : 2 ≤ N) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) =
      Part3.primeProductSignedError 2 N N
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)
        (fun u => integerWeight b kappa width N (fun i => (u i).val)) :=
  original_signed_source b kappa width hN _ _

end
end ImbalancedChen.P4BArbitraryWidthUpperPairProfile
