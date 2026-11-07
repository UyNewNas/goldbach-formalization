import ImbalancedChen.FixedEvenRoughCoefficients
import ImbalancedChen.UpperCoefficientPerturbation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An ACTUAL finite signed rounding constructor. The complete carrier is the
divisor set of the actual squarefree rough-prime product. Its canonical
decreasing prime words receive half-open logarithmic labels. A positive
coefficient uses the inner ALL test on its entire label fibre; a negative
coefficient uses the outer ANY test on that fibre. Each test concerns
membership in the whole original retained-history support, including all
ancestor choices together. Gates are not optimized separately.

The output need not be a prefix-closed policy coefficient. It remains a
separately named coefficient, compared with the literal raw lower lambda.
The exact reciprocal-totient rounding loss is exposed, not assumed small.
-/

namespace ImbalancedChen.P2LowerFiniteCellRounding

noncomputable section
open scoped Classical BigOperators

def roughProduct (N cap : ℕ) (w z : ℝ) : ℕ :=
  (roughPrimeUniverse N cap w z).prod

def universe (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (roughProduct N cap w z).divisors

def rawSupport (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  fixedEvenRoughSupport retainEven N cap w z

def raw (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) : ℝ :=
  fixedEvenRoughCoefficient retainEven N cap w z d

def primeLabel (N : ℕ) (tau : ℝ) (p : ℕ) : ℤ :=
  ⌊(Real.log (p:ℝ)/Real.log N)/tau⌋

def label (N : ℕ) (tau : ℝ) (d : ℕ) : List ℤ :=
  d.primeFactorsList.reverse.map (primeLabel N tau)

def cell (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Finset ℕ :=
  (universe N cap w z).filter (fun e=>label N tau e=label N tau d)

def inner (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  cell N cap w z tau d ⊆ rawSupport retainEven N cap w z

def outer (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  (cell N cap w z tau d ∩ rawSupport retainEven N cap w z).Nonempty

def coefficient (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : ℝ :=
  if d∈universe N cap w z then
    if 0≤(ArithmeticFunction.moebius d:ℝ) then
      if inner retainEven N cap w z tau d then (ArithmeticFunction.moebius d:ℝ) else 0
    else if outer retainEven N cap w z tau d then (ArithmeticFunction.moebius d:ℝ) else 0
  else 0

theorem roughProduct_squarefree (N cap : ℕ) (w z : ℝ) :
    Squarefree (roughProduct N cap w z) :=
  list_prod_squarefree_of_nodup_primes (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z) (fun _ hp=>mem_roughPrimeUniverse_prime hp)

theorem universe_squarefree (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d∈universe N cap w z) : Squarefree d :=
  (roughProduct_squarefree N cap w z).of_dvd (Nat.mem_divisors.mp hd).1

theorem universe_rough (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d∈universe N cap w z) : RoughPrimeSupportedAt w d := by
  have hP := roughProduct_squarefree N cap w z
  have hdvd := (Nat.mem_divisors.mp hd).1
  refine ⟨(universe_squarefree N cap w z hd).ne_zero,?_⟩
  intro p hp
  have hpP : p∈(roughProduct N cap w z).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans hdvd,hP.ne_zero⟩
  have heq : (roughProduct N cap w z).primeFactors=
      (roughPrimeUniverse N cap w z).toFinset := by
    have hprod : (∏p∈(roughPrimeUniverse N cap w z).toFinset,p)=
        (roughPrimeUniverse N cap w z).prod := by
      simpa using List.prod_toFinset (fun p : ℕ=>p) (roughPrimeUniverse_nodup N cap w z)
    change (roughPrimeUniverse N cap w z).prod.primeFactors=_
    rw [←hprod]
    exact Nat.primeFactors_prod (fun p hp=>mem_roughPrimeUniverse_prime (List.mem_toFinset.mp hp))
  rw [heq] at hpP
  exact mem_roughPrimeUniverse_lower (List.mem_toFinset.mp hpP)

theorem rawSupport_subset_universe (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : rawSupport retainEven N cap w z ⊆ universe N cap w z := by
  intro d hd
  obtain ⟨leaf,hleaf,hprod⟩ :=
    (mem_firstExitRetainedModuli (evenFirstExitPolicy retainEven)
      (roughPrimeUniverse N cap w z) d).mp hd
  have hsub := mem_firstExitRootLeaves_selected_reverse_sublist
    (evenFirstExitPolicy retainEven) (fun _=>1) (roughPrimeUniverse N cap w z) leaf hleaf
  apply Nat.mem_divisors.mpr
  refine ⟨?_,(roughProduct_squarefree N cap w z).ne_zero⟩
  have hdiv := hsub.prod_dvd_prod
  simpa only [List.prod_reverse,hprod] using hdiv

theorem raw_value (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    raw retainEven N cap w z d=
      if d∈rawSupport retainEven N cap w z then (ArithmeticFunction.moebius d:ℝ) else 0 := by
  unfold raw fixedEvenRoughCoefficient firstExitRetainedCoefficient rawSupport fixedEvenRoughSupport
  split_ifs <;> rfl

theorem self_mem_cell (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : d∈universe N cap w z) : d∈cell N cap w z tau d :=
  Finset.mem_filter.mpr ⟨hd,rfl⟩

/-- Every real logarithmic prime coordinate belongs to its single
half-open bin, including exact grid boundaries on the lower side. -/
theorem primeLabel_halfopen (N : ℕ) {tau : ℝ} (htau : 0<tau) (p : ℕ) :
    (primeLabel N tau p:ℝ)*tau≤Real.log (p:ℝ)/Real.log N ∧
      Real.log (p:ℝ)/Real.log N<((primeLabel N tau p:ℝ)+1)*tau := by
  have hlo := Int.floor_le ((Real.log (p:ℝ)/Real.log N)/tau)
  have hhi := Int.lt_floor_add_one ((Real.log (p:ℝ)/Real.log N)/tau)
  exact ⟨(le_div_iff₀ htau).mp hlo,(div_lt_iff₀ htau).mp hhi⟩

/-- Label fibres are disjoint; the ALL and ANY operations never combine
different histories by independently reselecting their ancestor gates. -/
theorem cells_disjoint (N cap : ℕ) (w z tau : ℝ) {d e : ℕ}
    (h : label N tau d≠label N tau e) :
    Disjoint (cell N cap w z tau d) (cell N cap w z tau e) := by
  apply Finset.disjoint_left.mpr
  intro k hk hd
  exact h ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hd).2)

/-- Coefficientwise lower rounding is DERIVED from the actual finite
ALL/ANY construction; no comparison or final bound is a hypothesis. -/
theorem coefficient_le_raw (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z tau : ℝ) (d : ℕ) : coefficient retainEven N cap w z tau d≤raw retainEven N cap w z d := by
  rw [raw_value]
  by_cases hd : d∈universe N cap w z
  · have hself := self_mem_cell N cap w z tau hd
    by_cases hsign : 0≤(ArithmeticFunction.moebius d:ℝ)
    · by_cases hi : inner retainEven N cap w z tau d
      · have hr := hi hself
        simp only [coefficient,if_pos hd,if_pos hsign,if_pos hi,if_pos hr,le_refl]
      · simp only [coefficient,if_pos hd,if_pos hsign,if_neg hi]
        split_ifs <;> linarith
    · by_cases ho : outer retainEven N cap w z tau d
      · simp only [coefficient,if_pos hd,if_neg hsign,if_pos ho]
        split_ifs <;> linarith
      · have hr : d∉rawSupport retainEven N cap w z := by
          intro hr
          exact ho ⟨d,Finset.mem_inter.mpr ⟨hself,hr⟩⟩
        simp only [coefficient,if_pos hd,if_neg hsign,if_neg ho,if_neg hr,le_refl]
  · have hr : d∉rawSupport retainEven N cap w z :=
      fun hr=>hd (rawSupport_subset_universe retainEven N cap w z hr)
    simp only [coefficient,if_neg hd,if_neg hr,le_refl]

theorem coefficient_abs_le_one (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z tau : ℝ) (d : ℕ) : |coefficient retainEven N cap w z tau d|≤1 := by
  unfold coefficient
  split_ifs <;> try norm_num
  all_goals exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))

def roundingLoss (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  reciprocalTotientDensity (universe N cap w z)
    (fun d=>|coefficient retainEven N cap w z tau d-raw retainEven N cap w z d|)

/-- Exact signed density loss of this output, rather than an unspecified
compiler error. Quantitative gate-strip smallness remains separate. -/
theorem roundingLoss_exact (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) :
    reciprocalTotientDensity (universe N cap w z) (raw retainEven N cap w z)-
      reciprocalTotientDensity (universe N cap w z) (coefficient retainEven N cap w z tau)=
        roundingLoss retainEven N cap w z tau := by
  unfold reciprocalTotientDensity roundingLoss
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [abs_of_nonpos (sub_nonpos.mpr (coefficient_le_raw retainEven N cap w z tau d))]
  ring

end
end ImbalancedChen.P2LowerFiniteCellRounding
