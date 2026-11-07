import ImbalancedChen.P4BActualCompactSmoothFamily
import ImbalancedChen.P4BPrimeEulerOperatorWords
import ImbalancedChen.P5NativeSelectedFourOrderedEuler

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The source is the EXISTING P4B original independent-prime pair caller.
The physical width is chosen by its production compact arithmetic mass
constructor, before N and all prime variables. The positive-real pullback
is genuinely extended smoothly by zero, and the literal original caller
is recovered on prime tuples. No marked-prefix or residual-divisor rank
is used. This is an actual rank-two subfamily, not full paper coverage.
-/
namespace ImbalancedChen.P5ActualIndependentUpperPairProfile
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open P4B P4BActualCompactSmoothFamily P4BOuterRampRoughness
open P5Z.AdmissibleAllRankIntegerGeometricFamily
open P5Z.NativeSelectedFourOrderedEuler
open P5Z.LicensedOriginalIntegerProfile

structure Parameters where
  b0 : ℝ
  b1 : ℝ
  kappa : ℝ
  kappaZero : ℝ
  theta : ℝ
  precision : ℝ
  widthMax : ℝ
  b0_half : (1/2 : ℝ) < b0
  b_band : b0 ≤ b1
  b1_one : b1 < 1
  kappa_pos : 0 < kappa
  kappa_one : kappa < 1
  trim_gap : kappa < kappaZero
  theta_pos : 0 < theta
  precision_pos : 0 < precision
  widthMax_pos : 0 < widthMax
  rough_gap : theta < baseline b0 kappa

def selected (D : Parameters) :
    ActualCompactSmoothFamily D.b0 D.b1 D.kappa D.kappaZero
      D.theta D.precision D.widthMax :=
  Classical.choice (nonempty_actualCompactSmoothFamily D.b0_half D.b_band D.b1_one
    D.kappa_pos D.kappa_one D.trim_gap D.theta_pos D.precision_pos
    D.widthMax_pos D.rough_gap)

abbrev Band (D : Parameters) := {b : ℝ // D.b0 ≤ b ∧ b ≤ D.b1}

def profile (D : Parameters) (b : Band D) (N : ℕ) (p : Fin 2 → ℝ) : ℝ :=
  if 2 ≤ N then
    if p ∈ positivePrimeOrthant then
      smoothPrimeVariableProfile b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width p
    else 0
  else 0

def integerWeight (D : Parameters) (b : Band D) (N : ℕ) (u : Fin 2 → ℕ) : ℝ :=
  profile D b N (fun i => (u i : ℝ))

theorem profile_nonzero_data (D : Parameters) (b : Band D)
    {N : ℕ} {p : Fin 2 → ℝ} (hn : profile D b N p ≠ 0) :
    2 ≤ N ∧ p ∈ positivePrimeOrthant ∧
      (∀ i, (N : ℝ)^D.theta < p i) ∧
      (N : ℝ)^(1-D.kappaZero) < p 0*p 1 ∧
      p 0*p 1 < Real.exp (selected D).width * (N : ℝ) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hn (by simp [profile, h])
  have hp : p ∈ positivePrimeOrthant := by
    by_contra h
    exact hn (by simp [profile, hN, h])
  have hraw : smoothPrimeVariableProfile b.val N
      (manuscriptHalfProductCutoff D.kappa N) (selected D).width p ≠ 0 := by
    simpa only [profile, if_pos hN, if_pos hp] using hn
  have hlo := (selected D).prime_lower_support b.val b.property.1 b.property.2 N hN p hp hraw
  have hprod := (selected D).product_window b.val b.property.1 b.property.2 N hN p hp hraw
  exact ⟨hN, hp, hlo, hprod.1, hprod.2⟩

theorem profile_eventually_zero_nonpositive (D : Parameters) (b : Band D)
    (N : ℕ) (p : Fin 2 → ℝ) (hnp : ∃ i, p i ≤ 0) :
    profile D b N =ᶠ[𝓝 p] 0 := by
  by_cases hN : 2 ≤ N
  · obtain ⟨i, hi⟩ := hnp
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    let L : ℝ := (N : ℝ)^D.theta
    have hL : 0 < L := Real.rpow_pos_of_pos hNr _
    have hopen : IsOpen {x : Fin 2 → ℝ | x i < L} :=
      isOpen_lt (continuous_apply i) continuous_const
    filter_upwards [hopen.mem_nhds (hi.trans_lt hL)] with x hx
    by_contra hn
    have hs := (profile_nonzero_data D b hn).2.2.1 i
    exact (not_lt_of_ge hx.le) hs
  · simp only [profile, if_neg hN]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem profile_eventually_raw (D : Parameters) (b : Band D) {N : ℕ}
    (hN : 2 ≤ N) (p : Fin 2 → ℝ) (hp : p ∈ positivePrimeOrthant) :
    profile D b N =ᶠ[𝓝 p]
      smoothPrimeVariableProfile b.val N
        (manuscriptHalfProductCutoff D.kappa N) (selected D).width := by
  filter_upwards [isOpen_positivePrimeOrthant_forEuler.mem_nhds hp] with x hx
  simp only [profile, if_pos hN, if_pos hx]

theorem profile_smooth (D : Parameters) (b : Band D) (N : ℕ) :
    ContDiff ℝ ∞ (profile D b N) := by
  by_cases hN : 2 ≤ N
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ positivePrimeOrthant
    · exact ((contDiffOn_smoothPrimeVariableProfile b.val N
        (manuscriptHalfProductCutoff D.kappa N) (selected D).width).
          contDiffAt (isOpen_positivePrimeOrthant_forEuler.mem_nhds hp)).
        congr_of_eventuallyEq (profile_eventually_raw D b hN p hp)
    · have hnp : ∃ i, p i ≤ 0 := by
        change ¬ ∀ i, 0 < p i at hp
        push_neg at hp
        exact hp
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin 2 → ℝ => (0 : ℝ)) p).
        congr_of_eventuallyEq (profile_eventually_zero_nonpositive D b N p hnp)
  · simp only [profile, if_neg hN]
    exact contDiff_const

theorem profile_bounds (D : Parameters) (b : Band D) (N : ℕ) (p : Fin 2 → ℝ) :
    0 ≤ profile D b N p ∧ profile D b N p ≤ 1 := by
  unfold profile
  split_ifs
  · exact smoothPhysicalProfile_bounds _ _ _ _ _
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

-- Independently defined production weight, not a candidate caller.
theorem actual_original_caller (D : Parameters) (b : Band D) {N : ℕ}
    (hN : 2 ≤ N) (u : Fin 2 → Fin (N+1))
    (hu : u ∈ Part3.labelledPrimeTuples 2 N) :
    smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
      (selected D).width u =
      profile D b N (primeTuplePoint N u) := by
  have hp := primeTuplePoint_mem_positivePrimeOrthant hu
  simp only [profile, if_pos hN, if_pos hp]
  exact smoothPhysicalPairOuterRamp_eq_primeVariableProfile _ _ _ _ _

theorem finite_integer_support (D : Parameters) (b : Band D) (N : ℕ) :
    Set.Finite {u : Fin 2 → ℕ | integerWeight D b N u ≠ 0} := by
  let M := Nat.ceil (Real.exp (selected D).width * (N : ℝ))
  let bank : Finset (Fin 2 → ℕ) := Fintype.piFinset (fun _ => Finset.range (M+1))
  apply bank.finite_toSet.subset
  intro u hu
  have hs := profile_nonzero_data D b hu
  have hu0n : 0 < u 0 := by exact_mod_cast hs.2.1 0
  have hu1n : 0 < u 1 := by exact_mod_cast hs.2.1 1
  have hu0 : (1 : ℝ) ≤ u 0 := by exact_mod_cast (show 1 ≤ u 0 from hu0n)
  have hu1 : (1 : ℝ) ≤ u 1 := by exact_mod_cast (show 1 ≤ u 1 from hu1n)
  have hprod := hs.2.2.2.2
  have hceil : Real.exp (selected D).width * (N : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  apply Finset.mem_piFinset.mpr
  intro i
  have hbound : (u i : ℝ) ≤ M := by
    fin_cases i <;> nlinarith
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast hbound))

-- The second genuine original prime slot closes the apparent individual
-- cap collar: eventually the FULL real support already has p_i<N.
-- This is not true for the singleton source, and no Fin truncation is
-- substituted for a support proof here.
theorem nonzero_coordinates_lt_N (D : Parameters) (b : Band D)
    {N : ℕ} (hscale : Real.exp (selected D).width ≤ (N : ℝ)^D.theta)
    {p : Fin 2 → ℝ} (hn : profile D b N p ≠ 0) : ∀ i, p i < (N : ℝ) := by
  have hs := profile_nonzero_data D b hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h0 := hscale.trans_lt (hs.2.2.1 0)
  have h1 := hscale.trans_lt (hs.2.2.1 1)
  have hp0 := hs.2.1 0
  have hp1 := hs.2.1 1
  have hprod := hs.2.2.2.2
  intro i
  fin_cases i <;> by_contra h <;> have hh := le_of_not_gt h <;> nlinarith

theorem eventually_full_support_inside_original_cap (D : Parameters) :
    ∀ᶠ N : ℕ in atTop, ∀ (b : Band D) (p : Fin 2 → ℝ),
      profile D b N p ≠ 0 → ∀ i, p i < (N : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^D.theta) atTop atTop :=
    (Real.tendsto_rpow_atTop D.theta_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (Real.exp (selected D).width)] with N hN
  intro b p hn
  exact nonzero_coordinates_lt_N D b hN hn

def licence (D : Parameters) (b : Band D) (N : ℕ) :
    Licence 2 (integerWeight D b N) where
  ambient := profile D b N
  smooth := profile_smooth D b N
  agrees_on_primes := by intro u hu; rfl

theorem eulerOne_eq_production (i : Fin 2) (f : (Fin 2 → ℝ) → ℝ) :
    eulerOne i f = primeEulerOperator i f := by
  funext p
  apply congrArg (fderiv ℝ f p)
  funext j
  by_cases h : j = i
  · subst j
    simp [primeEulerCoordinateUnit]
  · simp [primeEulerCoordinateUnit, h, Ne.symm h]

def wordArray : (w : List (Fin 2)) → Fin w.length → Fin 2
  | [] => Fin.elim0
  | i::w => Fin.cons i (wordArray w)

theorem actual_ordered_word_dictionary (w : List (Fin 2))
    (f : (Fin 2 → ℝ) → ℝ) :
    eulerWord w f = primeEulerWord w.length (wordArray w) f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change eulerOne i (eulerWord w f) = primeEulerOperator i
      (primeEulerWord w.length (wordArray w) f)
    rw [ih, eulerOne_eq_production]

theorem eulerOne_eventuallyEq (i : Fin 2) (f g : (Fin 2 → ℝ) → ℝ)
    (p : Fin 2 → ℝ) (h : f =ᶠ[𝓝 p] g) :
    eulerOne i f =ᶠ[𝓝 p] eulerOne i g := by
  filter_upwards [h.iteratedFDeriv ℝ 1] with x hx
  have hd : fderiv ℝ f x = fderiv ℝ g x := by
    ext v
    have hv := congrArg (fun L => L (fun _ : Fin 1 => v)) hx
    simpa using hv
  simp only [eulerOne, hd]

theorem eulerWord_eventuallyEq (w : List (Fin 2)) (f g : (Fin 2 → ℝ) → ℝ)
    (p : Fin 2 → ℝ) (h : f =ᶠ[𝓝 p] g) :
    eulerWord w f =ᶠ[𝓝 p] eulerWord w g := by
  induction w with
  | nil => simpa only [eulerWord, List.foldr_nil] using h
  | cons i w ih => simpa only [eulerWord, List.foldr_cons] using
      eulerOne_eventuallyEq i (eulerWord w f) (eulerWord w g) p ih

theorem fixed_order_euler_budget (D : Parameters) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Band D) N (w : List (Fin 2)) p,
      w.length = r → |eulerWord w (profile D b N) p| ≤ C := by
  obtain ⟨C, hC, hb⟩ := (selected D).Euler_budget r
  refine ⟨C, hC, ?_⟩
  intro b N w p hw
  by_cases hN : 2 ≤ N
  · by_cases hp : p ∈ positivePrimeOrthant
    · rw [(eulerWord_eventuallyEq w _ _ p
        (profile_eventually_raw D b hN p hp)).eq_of_nhds,
        actual_ordered_word_dictionary]
      subst r
      exact hb b.val b.property.1 b.property.2 N hN _ p hp (wordArray w)
    · have hnp : ∃ i, p i ≤ 0 := by
        change ¬ ∀ i, 0 < p i at hp
        push_neg at hp
        exact hp
      rw [(eulerWord_eventually_zero w _ p
        (profile_eventually_zero_nonpositive D b N p hnp)).eq_of_nhds, abs_zero]
      exact hC
  · have hz : profile D b N = 0 := by simp [profile, hN]
    rw [(eulerWord_eventually_zero w _ p
      (Filter.Eventually.of_forall (fun x => congrFun hz x))).eq_of_nhds, abs_zero]
    exact hC

theorem mixedEuler (D : Parameters) (order : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (b : Band D) N (w : List (Fin 2)) p,
      w.length ≤ order → |eulerWord w (profile D b N) p| ≤ (C : ℝ) := by
  choose M hM hb using (fun d : Fin (order+1) => fixed_order_euler_budget D d.val)
  let B : ℝ := ∑ d : Fin (order+1), M d
  refine ⟨Nat.ceil B + 1, by omega, ?_⟩
  intro b N w p hw
  let i : Fin (order+1) := ⟨w.length, by omega⟩
  have hm := hb i b N w p rfl
  have hs : M i ≤ B := Finset.single_le_sum (fun d hd => hM d) (Finset.mem_univ i)
  have hc : B ≤ ((Nat.ceil B+1 : ℕ) : ℝ) := by
    have hceil := Nat.le_ceil B
    push_cast
    linarith
  exact hm.trans (hs.trans hc)

end
end ImbalancedChen.P5ActualIndependentUpperPairProfile
