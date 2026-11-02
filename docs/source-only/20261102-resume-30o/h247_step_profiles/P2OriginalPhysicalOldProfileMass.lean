import ImbalancedChen.P2OriginalOldProfilePrimeLimits

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal fresh/repeated prime multipliers and their uniform bounded-test
replacement. No division by Theta or by a profile atom mass occurs.
-/
namespace ImbalancedChen.P2OriginalPhysicalOldProfileMass

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalAffineProfilePassage
open P2OriginalOldProfilePrimeLimits P2OriginalCompactThetaMass
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def trueSingleTest (N : ℕ) (L : ℝ) (d : ℕ) (D : Set (Coord 1)) (f : Coord 1 → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
    localPrimeFactor d (p 0) * D.indicator f (normalizedLog N L p)

def truePairTest (N : ℕ) (L : ℝ) (d : ℕ) (D : Set (Coord 2)) (f : Coord 2 → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
    (localPrimeFactor d (p 0) * localPrimeFactor (d*p 0) (p 1)) *
      D.indicator f (normalizedLog N L p)

theorem indicator_abs_bound {X : Type*} (D : Set X) (f : X → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (x : X) : |D.indicator f x| ≤ C := by
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]
    exact hf x
  · rw [indicator_of_notMem hx,abs_zero]
    exact hC

theorem trueSingleTest_error {N : ℕ} {L C : ℝ} (d : ℕ) (D : Set (Coord 1))
    (f : Coord 1 → ℝ) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C)
    (hA : 4 ≤ (N:ℝ)^(L/10)) :
    |trueSingleTest N L d D f-scaledPrimeSum N L D f| ≤
      ((2*C)/(N:ℝ)^(L/10)) *
        actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  unfold trueSingleTest scaledPrimeSum actualPrimeBoxTestSum actualPrimeBoxMass
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hfloor := (mem_actualPrimeBoxTuples_iff.mp hp 0).2.2.1
  have hw : 0 ≤ 1/((p 0:ℝ)-1) := by
    have hprime : (1:ℝ) < p 0 := by exact_mod_cast (mem_actualPrimeBoxTuples_iff.mp hp 0).1.one_lt
    exact (one_div_pos.mpr (by linarith)).le
  simp only [Fin.prod_univ_one,← sub_mul,abs_mul]
  calc
    _ ≤ ((2/(N:ℝ)^(L/10))*(1/((p 0:ℝ)-1)))*C :=
      mul_le_mul (local_error hA hfloor) (indicator_abs_bound D f hC hf _)
        (abs_nonneg _) (mul_nonneg (by positivity) hw)
    _ = _ := by ring

theorem truePairTest_error {N : ℕ} {L C : ℝ} (d : ℕ) (D : Set (Coord 2))
    (f : Coord 2 → ℝ) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C)
    (hA : 4 ≤ (N:ℝ)^(L/10)) :
    |truePairTest N L d D f-scaledPrimeSum N L D f| ≤
      ((6*C)/(N:ℝ)^(L/10)) *
        actualPrimeBoxMass N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5) := by
  unfold truePairTest scaledPrimeSum actualPrimeBoxTestSum actualPrimeBoxMass
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hf0 := (mem_actualPrimeBoxTuples_iff.mp hp 0).2.2.1
  have hf1 := (mem_actualPrimeBoxTuples_iff.mp hp 1).2.2.1
  have hw := actualPrimeBoxWeight_nonneg hp
  simp only [Fin.prod_univ_two] at hw
  simp only [Fin.prod_univ_two,← sub_mul,abs_mul]
  calc
    _ ≤ ((6/(N:ℝ)^(L/10))*((1/((p 0:ℝ)-1))*(1/((p 1:ℝ)-1))))*C :=
      mul_le_mul (pair_local_error hA hf0 hf1) (indicator_abs_bound D f hC hf _)
        (abs_nonneg _) (mul_nonneg (by positivity) hw)
    _ = _ := by ring

theorem table_abs_bound (lower : Bool) (nums : Fin 200 → ℤ) (s : ℝ) :
    |tableFunction lower nums s| ≤ floorBound nums := by
  cases lower
  · simpa only [Real.norm_eq_abs] using norm_upperFloor_le nums s
  · simpa only [Real.norm_eq_abs] using norm_floorStep_le nums s

def singleTest (s0 : ℝ) (lower : Bool) (nums : Fin 200 → ℤ) (x : Coord 1) : ℝ :=
  residualSingle x * tableFunction lower nums (singleRho s0 x)
def pairTest (p : W2Parameters) (k : Fin 4) (nums : Fin 200 → ℤ) (x : Coord 2) : ℝ :=
  residualPair x * tableFunction false nums (pairProfile p k x)

theorem singleTest_bound (s0 : ℝ) (lower : Bool) (nums : Fin 200 → ℤ) (x : Coord 1) :
    |singleTest s0 lower nums x| ≤ 10*floorBound nums := by
  rw [singleTest,abs_mul,abs_of_nonneg (residualSingle_bounds x).1]
  exact mul_le_mul (residualSingle_bounds x).2 (table_abs_bound lower nums _)
    (abs_nonneg _) (by norm_num)

theorem pairTest_bound (p : W2Parameters) (k : Fin 4) (nums : Fin 200 → ℤ) (x : Coord 2) :
    |pairTest p k nums x| ≤ 10*floorBound nums := by
  rw [pairTest,abs_mul,abs_of_nonneg (residualPair_bounds x).1]
  exact mul_le_mul (residualPair_bounds x).2 (table_abs_bound false nums _)
    (abs_nonneg _) (by norm_num)

def trueSingleOldProfile (N : ℕ) (L : ℝ) (d : ℕ) (lo hi s0 : ℝ)
    (lower : Bool) (nums : Fin 200 → ℤ) : ℝ :=
  trueSingleTest N L d (singleHalf lo hi) (singleTest s0 lower nums)
def truePairOldProfile (N : ℕ) (L : ℝ) (d : ℕ) (p : W2Parameters)
    (k : Fin 4) (nums : Fin 200 → ℤ) : ℝ :=
  truePairTest N L d (pairHalf p k) (pairTest p k nums)

/-- All finite arithmetic multipliers, including primes already dividing
the prefix, are removed uniformly BEFORE the prefix is chosen. -/
theorem compact_uniform_true_single_old_profile {Lmin Lmax lo hi s0 epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (hs : 0 < s0)
    (lower : Bool) (nums : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |trueSingleOldProfile N L d lo hi s0 lower nums-
        oldProfileIntegral (singleHalf lo hi) residualSingle (singleRho s0) lower nums| < epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_single_old_profile hmin hmax
    (by positivity : (0:ℝ) < epsilon/2) hlo hhi hs lower nums
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k:=1) hmin hmax
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 20) (floorBound_nonneg nums))
    (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max Tp Te,?_⟩
  intro N hN L hL d
  have hp := hTp N (by omega) L hL
  obtain ⟨hA,he'⟩ := hTe N (by omega) L hL
  have hd := trueSingleTest_error d (singleHalf lo hi) (singleTest s0 lower nums)
    (mul_nonneg (by norm_num) (floorBound_nonneg nums)) (singleTest_bound s0 lower nums) hA
  have ht := abs_sub_le (trueSingleOldProfile N L d lo hi s0 lower nums)
    (oldProfilePrimeSum N L (singleHalf lo hi) residualSingle (singleRho s0) lower nums)
    (oldProfileIntegral (singleHalf lo hi) residualSingle (singleRho s0) lower nums)
  change |trueSingleOldProfile N L d lo hi s0 lower nums-
    oldProfilePrimeSum N L (singleHalf lo hi) residualSingle (singleRho s0) lower nums| ≤ _ at hd
  have heq : 2*(10*floorBound nums)=20*floorBound nums := by ring
  rw [heq] at hd
  linarith

theorem compact_uniform_true_pair_old_profile {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) (nums : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |truePairOldProfile N L d p k nums-
        oldProfileIntegral (pairHalf p k) residualPair (pairProfile p k) false nums| < epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_pair_old_profile hmin hmax
    (by positivity : (0:ℝ) < epsilon/2) hp k nums
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k:=2) hmin hmax
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 60) (floorBound_nonneg nums))
    (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max Tp Te,?_⟩
  intro N hN L hL d
  have hp' := hTp N (by omega) L hL
  obtain ⟨hA,he'⟩ := hTe N (by omega) L hL
  have hd := truePairTest_error d (pairHalf p k) (pairTest p k nums)
    (mul_nonneg (by norm_num) (floorBound_nonneg nums)) (pairTest_bound p k nums) hA
  have ht := abs_sub_le (truePairOldProfile N L d p k nums)
    (oldProfilePrimeSum N L (pairHalf p k) residualPair (pairProfile p k) false nums)
    (oldProfileIntegral (pairHalf p k) residualPair (pairProfile p k) false nums)
  change |truePairOldProfile N L d p k nums-
    oldProfilePrimeSum N L (pairHalf p k) residualPair (pairProfile p k) false nums| ≤ _ at hd
  have heq : 6*(10*floorBound nums)=60*floorBound nums := by ring
  rw [heq] at hd
  linarith

theorem oldProfileIntegral_domain_congr {d : ℕ} {D E : Set (Coord d)}
    (hDE : D =ᵐ[volume] E) (f rho : Coord d → ℝ) (lower : Bool) (nums : Fin 200 → ℤ) :
    oldProfileIntegral D f rho lower nums = oldProfileIntegral E f rho lower nums := by
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply setIntegral_congr_set
  filter_upwards [hDE] with x hx
  exact and_congr_left (fun _ => hx)

theorem single_profile_original_integral {lo hi : ℝ} (hlo : (1/5:ℝ) ≤ lo)
    (hhi : hi ≤ 1/2) (s0 : ℝ) (lower : Bool) (nums : Fin 200 → ℤ) :
    oldProfileIntegral (singleHalf lo hi) residualSingle (singleRho s0) lower nums =
      ∫ u in Ioo lo hi,tableFunction lower nums (s0*(1-u))/(u*(1-u)) := by
  have hDE := sandwich_ae singleForms (singleBounds lo hi) singleForms_ne (singleHalf_sandwich lo hi)
  rw [← single_as_affine] at hDE
  rw [oldProfileIntegral_domain_congr hDE]
  have hm : MeasurableSet (singleDomain lo hi) := by
    rw [single_as_affine]; exact measurableSet_primeAffineGateRegion _ _
  have hfi := (integrableOn_logPrimeBox_test_cube (by norm_num : (0:ℝ) < 1/10)
    residualSingle residualSingle_continuous.continuousOn).mono_set (single_in_cube hlo hhi)
  rw [oldProfileIntegral_eq hm residualSingle (singleRho s0)
    ((measurable_singletonProfile s0).comp (measurable_pi_apply 0)) hfi]
  have he : (∫ x in singleDomain lo hi,
      (residualSingle x * tableFunction lower nums (singleRho s0 x)) * ∏ i,1/x i) =
      ∫ x in singleDomain lo hi,
        tableFunction lower nums (s0*(1-x 0))/(x 0*(1-x 0)) := by
    apply setIntegral_congr_fun hm
    intro x hx
    have hk := single_kernel hhi hx
    dsimp [singleRho,singletonProfile]
    calc
      _ = tableFunction lower nums (s0*(1-x 0)) * (residualSingle x * ∏ i,1/x i) := by ring
      _ = _ := by rw [hk]; ring
  rw [he,single_integral_coordinates]

theorem pair_profile_original_integral {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) (nums : Fin 200 → ℤ) :
    oldProfileIntegral (pairHalf p k) residualPair (pairProfile p k) false nums =
      ∫ x in W2PairDomain p k,tableFunction false nums (pairProfile p k x)/
        (x 0*x 1*(1-x 0-x 1)) := by
  have hDE := sandwich_ae (pairForms k) (pairBounds p k) (pairForms_ne k) (pairHalf_sandwich p k)
  rw [← pair_as_affine] at hDE
  rw [oldProfileIntegral_domain_congr hDE]
  have hm := measurableSet_W2PairDomain p k
  have hfi := (integrableOn_logPrimeBox_test_cube (by norm_num : (0:ℝ) < 1/10)
    residualPair residualPair_continuous.continuousOn).mono_set (pair_in_cube hp k)
  rw [oldProfileIntegral_eq hm residualPair (pairProfile p k) (measurable_pairProfile p k) hfi]
  apply setIntegral_congr_fun hm
  intro x hx
  have hk := pair_kernel hp k hx
  calc
    _ = tableFunction false nums (pairProfile p k x) * (residualPair x * ∏ i,1/x i) := by ring
    _ = _ := by rw [hk]; ring

end
end ImbalancedChen.P2OriginalPhysicalOldProfileMass
