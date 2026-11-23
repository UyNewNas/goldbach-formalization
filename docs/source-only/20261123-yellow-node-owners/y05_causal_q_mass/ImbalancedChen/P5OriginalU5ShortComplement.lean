import ImbalancedChen.P5OriginalU5AllMarkHBReserves

/-! Short complete moduli in the full original U5 triangle, including the
complement of the previously paid rectangle.  The signed long remainder
retains exactly the nonzero integer coefficients of the same physical sum. -/
namespace ImbalancedChen.P5OriginalU5ShortComplement

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV
open P5OriginalU5AllMarkHBReserves (branches)

abbrev primitive (N : ℕ) (e : ℝ) (P : Policy) (q : ℕ) : ℝ :=
  (integerRho N e P q : ℝ) * finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q

def outsideShort (N : ℕ) (e : ℝ) (P : Policy) : Finset ℕ :=
  (moduli N e P \ paidModuli N e P).filter (fun q => q ≤ shortCap N)

def activeLong (N : ℕ) (e : ℝ) (P : Policy) : Finset ℕ :=
  (moduli N e P \ paidModuli N e P).filter
    (fun q => shortCap N < q ∧ integerRho N e P q ≠ 0)

theorem mem_activeLong {N q : ℕ} {e : ℝ} {P : Policy} :
    q ∈ activeLong N e P ↔
      q ∈ moduli N e P ∧ shortCap N < q ∧ integerRho N e P q ≠ 0 := by
  constructor
  · intro h
    obtain ⟨hmem, hlarge, hne⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_sdiff.mp hmem).1, hlarge, hne⟩
  · rintro ⟨hmem, hlarge, hne⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_sdiff.mpr ⟨hmem, fun h =>
      (not_le_of_gt hlarge) (Finset.mem_filter.mp h).2.1⟩, hlarge, hne⟩

theorem original_complement_exact (N : ℕ) (e : ℝ) (P : Policy) :
    remainingPrimitive N e P =
      (∑ q ∈ outsideShort N e P, primitive N e P q) +
      ∑ q ∈ activeLong N e P, primitive N e P q := by
  unfold remainingPrimitive outsideShort activeLong
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqshort : q ≤ shortCap N
  · simp [primitive, hqshort, not_lt.mpr hqshort]
  · by_cases hz : integerRho N e P q = 0
    · simp [primitive, hz, hqshort]
    · simp [primitive, hz, hqshort, lt_of_not_ge hqshort]

/-- Absolute variation over any subset of the short physical moduli.
The BV constant is common to every selector and subset, before any grouping
by common physical level, owner, selected history or zero weight. -/
theorem eventually_short_variation (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      ∀ S ⊆ moduli N e P, (∀ q ∈ S, q ≤ shortCap N) →
        (∑ q ∈ S, |primitive N e P q|) ≤ C*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C, hC, hBV⟩ := P4BPositiveUpperPrimeBV.eventually_primeError_log_saving p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBV, eventually_ge_atTop (2 : ℕ)] with N hBVN hN
  intro e he he8 P S hS hcap
  have hw := (attachment_gates hN he he8).2.2
  have hd (q : ℕ) (hq : q ∈ S) :=
    P5OriginalU5AllMarkCosts.full_modulus_data hN P hw (hS hq)
  have hI : S ⊆ Finset.Icc 1 (shortCap N) := fun q hq =>
    Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (hd q hq).1, hcap q hq⟩
  have h := hBVN S hI
    (fun q hq => (sieveProduct_squarefree N N).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (hd q hq).1))
    (fun _ => N) (fun _ => N) (fun _ _ => le_rfl)
    (fun q hq => (coprime_of_dvd_sieveProduct (Nat.dvd_of_mem_divisors (hd q hq).1)).symm)
  refine (Finset.sum_le_sum ?_).trans h
  intro q hq
  change |(integerRho N e P q : ℝ) * P4BPositiveUpperPrimeBV.primeError N N q| ≤ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (hd q hq).2.1 (abs_nonneg _)).trans_eq (one_mul _)

/-- Quantitative restoration for every subcarrier of the same U5 integer
coefficient. Both Y06 estimates are uniform before the choice of S. -/
theorem exists_sum_to_branches (t tau : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (htau : t < tau) (K p : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy, ∀ S ⊆ moduli N e P, ∀ zeta : ℝ,
        ‖((∑ q ∈ S, primitive N e P q : ℝ) : ℂ) - branches t tau zeta (p+3) N K e P S‖ ≤
          D*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨D, hD, hs⟩ := P5OriginalU5AllMarkSmoothing.exists_all_mark_smoothing t ht ht1 p
  refine ⟨D+1, by positivity, ?_⟩
  filter_upwards [hs, P5OriginalU5AllMarkHBReserves.eventually_smooth_to_branches
    t tau ht1 htau K p 1 zero_lt_one] with N hsN hbN
  intro hev e he he8 P S hS zeta
  let M := P5OriginalU5AllMarkSmoothing.smoothDiscrepancy t (p+3) N e P S
  have hsm := hsN hev e he he8 P S hS
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq] at hsm
  have hd : ‖((∑ q ∈ S, primitive N e P q : ℝ) : ℂ) - (M : ℂ)‖ ≤
      D*(N : ℝ)/(Real.log (N : ℝ))^p := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hsm
  exact (norm_sub_le_norm_sub_add_norm_sub _ (M : ℂ) _).trans
    ((add_le_add hd (hbN hev e he he8 P S hS (p+3) zeta)).trans_eq (by ring))

/-- Only the long nonzero complete moduli of the original full U5 triangle
remain inside the genuine medium/no-medium HB arithmetic. -/
theorem exists_complement_to_active_long_branches (t tau : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (htau : t < tau) (K p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy, ∀ zeta : ℝ,
        ‖(remainingPrimitive N e P : ℂ) -
          branches t tau zeta (p+3) N K e P (activeLong N e P)‖ ≤
          C*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C, hC, hshort⟩ := eventually_short_variation p
  obtain ⟨D, hD, hs⟩ := exists_sum_to_branches t tau ht ht1 htau K p
  refine ⟨C+D, by positivity, ?_⟩
  filter_upwards [hshort, hs] with N hshortN hsN
  intro hev e he he8 P zeta
  let Q := activeLong N e P
  let L : ℝ := ∑ q ∈ Q, primitive N e P q
  have hQ : Q ⊆ moduli N e P := fun _ h => (mem_activeLong.mp h).1
  have hsmall := hshortN e he he8 P (outsideShort N e P)
    (fun q hq => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).1)
    (fun q hq => (Finset.mem_filter.mp hq).2)
  have hdiff : ‖(remainingPrimitive N e P : ℂ) - (L : ℂ)‖ ≤
      C*(N : ℝ)/(Real.log (N : ℝ))^p := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, original_complement_exact]
    change |(_ + L) - L| ≤ _
    rw [add_sub_cancel_right]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsmall
  exact (norm_sub_le_norm_sub_add_norm_sub _ (L : ℂ) _).trans
    ((add_le_add hdiff (hsN hev e he he8 P Q hQ zeta)).trans_eq (by ring))

/-- The projected density, the same chosen attachment precision and the
original lower count now retain just the real part of the two long HB
branches. The single threshold precedes the policy and medium parameter. -/
theorem exists_original_count_long_branches (t tau : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (htau : t < tau) (K p : ℕ)
    {eta eMax : ℝ} (heta : 0 < eta) (hMax : 0 < eMax) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, 0 < e ∧ e < 1/8 ∧ e < eMax ∧
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → Even N → ∀ P : Policy, ∀ zeta : ℝ,
        fullProjectedMainSum N P - projectionReserve N eta +
          (branches t tau zeta (p+3) N K e P (activeLong N e P)).re -
          C*(N : ℝ)/(Real.log (N : ℝ))^p ≤ currentChenUpsilon5 N := by
  obtain ⟨D,hD,e,he,he8,heMax,M,hM,hcount⟩ :=
    P5OriginalU5AllMarkCosts.exists_original_count_paid p heta hMax
  obtain ⟨C,hC,hbranch⟩ := exists_complement_to_active_long_branches t tau ht ht1 htau K p
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hbranch
  refine ⟨C+D, by positivity, e, he, he8, heMax, max M J, hM.trans (le_max_left _ _), ?_⟩
  intro N hN hev P zeta
  have hc := hcount N ((le_max_left _ _).trans hN) hev P
  have hb := hJ N ((le_max_right _ _).trans hN) hev e he he8 P zeta
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hh
  have hres : (C+D)*(N : ℝ)/(Real.log (N : ℝ))^p =
      C*(N : ℝ)/(Real.log (N : ℝ))^p + D*(N : ℝ)/(Real.log (N : ℝ))^p := by ring
  rw [hres]
  linarith only [hh,hc]

end
end ImbalancedChen.P5OriginalU5ShortComplement
