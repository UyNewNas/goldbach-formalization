import ImbalancedChen.Part5OriginalH430OrdinaryPairWalls
import ImbalancedChen.P2OriginalPhysicalOldProfileMass
import ImbalancedChen.CanonicalUpperCancellationP5
import ImbalancedChen.CanonicalLowerCancellationP5

/-! The ordinary lower Rosser function on the original singleton chambers.
All prime integrals use the compact true singular-series factor at the
original target N, and the lower extension through 2 is literal. -/
namespace ImbalancedChen.Part5OriginalH430OrdinarySingletonKernel
noncomputable section
open Real Set MeasureTheory Filter Finset
open P5OriginalActionMassBound P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalPhysicalOldProfileMass
open P2OriginalCompactThetaMass P2OriginalCompactScaledPrimeMass
open P2OriginalPositiveSameQMassLift P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430OrdinaryPairWalls
open scoped Classical BigOperators Interval

def clippedLower (s : ℝ) : ℝ := log (max 1 (min 3 (s-1)))

theorem canonical_lower_log {s : ℝ} (hs : s≤4) :
    P5CanonicalUpperCancellation.lowerBar s = clippedLower s := by
  by_cases h2 : s≤2
  · rw [P5CanonicalUpperCancellation.lowerBar_eq_zero h2,clippedLower,
      max_eq_left (show min 3 (s-1)≤1 by apply (min_le_right _ _).trans; linarith),log_one]
  · have h2' : 2≤s := le_of_lt (lt_of_not_ge h2)
    have h := P5CanonicalLowerCancellation.lowerBar_integral h2'
    change P5CanonicalUpperCancellation.lowerBar s =
      ∫ u in (1:ℝ)..(s-1),P5CanonicalUpperCancellation.upperA u/u at h
    rw [h,clippedLower,min_eq_right (by linarith),max_eq_right (by linarith)]
    calc
      _ = ∫ u in (1:ℝ)..(s-1),1/u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (by linarith)] at hu
        rw [P5CanonicalUpperCancellation.upperA_eq_one (zero_lt_one.trans_le hu.1)
          (by linarith [hu.2])]
      _ = _ := by simpa only [div_one] using
        (integral_one_div_of_pos (by norm_num : (0:ℝ)<1) (by linarith : 0<s-1))

theorem anchor_correction {s : ℝ} (h3 : 3≤s) (h5 : s≤5) :
    P5CanonicalUpperCancellation.upperA s=1+P2SeedOmegaLiteralFunctional.correction s := by
  rw [P5CanonicalUpperCancellation.upperA_integral h3]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith)] at hu
  rw [canonical_lower_log (by linarith [hu.2]),clippedLower,
    min_eq_right (by linarith [hu.2]),max_eq_right (by linarith [hu.1])]

def lowerTest (a : ℝ) (x : Coord 1) : ℝ := residualSingle x * clippedLower (a*(1-x 0))

theorem lowerTest_continuous (a : ℝ) : Continuous (lowerTest a) := by
  unfold lowerTest clippedLower
  apply residualSingle_continuous.mul
  apply Continuous.log
  · fun_prop
  · intro x
    exact (zero_lt_one.trans_le (le_max_left _ _)).ne'

theorem lowerTest_bound (a : ℝ) (x : Coord 1) : |lowerTest a x|≤20 := by
  let c := max (1:ℝ) (min 3 (a*(1-x 0)-1))
  have hc1 : 1≤c := le_max_left _ _
  have hc3 : c≤3 := max_le (by norm_num) (min_le_left _ _)
  have hl0 := log_nonneg hc1
  have hl2 : log c≤2 := (log_le_sub_one_of_pos (zero_lt_one.trans_le hc1)).trans (by linarith)
  have hr := residualSingle_bounds x
  change |residualSingle x * log c|≤20
  rw [abs_of_nonneg (mul_nonneg hr.1 hl0)]
  nlinarith only [mul_le_mul hr.2 hl2 hl0 (by norm_num : (0:ℝ)≤10)]

def ordinaryLowerIntegral (lo hi a : ℝ) : ℝ :=
  ∫ u in Ioo lo hi,P5CanonicalUpperCancellation.lowerBar (a*(1-u))/(u*(1-u))

theorem lowerOnWindow {lo hi a u : ℝ} (hlo : (1/5:ℝ)≤lo) (hhi : hi≤1/2)
    (ha : 0≤a) (ha5 : a≤5) (hu : u∈Ico lo hi) : a*(1-u)≤4 := by
  have h1 : 0≤1-u := by linarith [hu.2]
  have h2 : 1-u≤4/5 := by linarith [hu.1]
  nlinarith only [mul_le_mul ha5 h2 h1 (by norm_num : (0:ℝ)≤5)]

theorem moving_ordinary_lower {Lmin Lmax lo hi a ε : ℝ} (hm : 0<Lmin)
    (hM : Lmin≤Lmax) (hlo : (1/5:ℝ)≤lo) (hhi : hi≤1/2) (ha : 0≤a)
    (ha5 : a≤5) (he : 0<ε) :
    ∃ T : ℕ, ∀ N : ℕ,T≤N → ∀ L∈Icc Lmin Lmax,∀ d : ℕ,
      |trueSingleTest N L d (singleDomain lo hi) (lowerTest a) - ordinaryLowerIntegral lo hi a|<ε := by
  obtain ⟨Tp,hp⟩ := compact_uniform_scaled_affine hm hM (by norm_num : (0:ℝ)≤20)
    (half_pos he) singleForms (singleBounds lo hi) singleForms_ne
    (by rw [←single_as_affine]; exact single_in_cube hlo hhi)
    (lowerTest a) (lowerTest_continuous a) (lowerTest_bound a)
  obtain ⟨Ta,ht⟩ := compact_multiplier_error (k:=1) hm hM (by norm_num : (0:ℝ)≤40) (half_pos he)
  refine ⟨max Tp Ta,?_⟩
  intro N hN L hL d
  have h := hp N ((le_max_left _ _).trans hN) L hL
  rw [←single_as_affine] at h
  obtain ⟨hA,hE⟩ := ht N ((le_max_right _ _).trans hN) L hL
  have hd := trueSingleTest_error d (singleDomain lo hi) (lowerTest a) (by norm_num : (0:ℝ)≤20)
    (lowerTest_bound a) hA
  have hk : (∫x in singleDomain lo hi,lowerTest a x*(∏i,1/x i)) = ordinaryLowerIntegral lo hi a := by
    unfold ordinaryLowerIntegral
    rw [←single_integral_coordinates]
    apply setIntegral_congr_fun
    · rw [single_as_affine]; exact measurableSet_primeAffineGateRegion _ _
    · intro x hx
      rw [canonical_lower_log (lowerOnWindow hlo hhi ha ha5 ⟨hx.1.le,hx.2⟩),lowerTest]
      calc
        _ = clippedLower (a*(1-x 0)) * (residualSingle x*(∏i,1/x i)) := by ring
        _ = _ := by rw [single_kernel hhi hx]; ring
  rw [hk] at h
  have tri := abs_sub_le (trueSingleTest N L d (singleDomain lo hi) (lowerTest a))
    (scaledPrimeSum N L (singleDomain lo hi) (lowerTest a)) (ordinaryLowerIntegral lo hi a)
  norm_num at hd
  linarith only [tri,hd,h,hE]

def weightedLower (N : ℕ) (Q L : ℝ) (d : ℕ) (lo hi a : ℝ) : ℝ :=
  ∑ x∈actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L x ∈ singleHalf lo hi then thetaAtom N Q (d*x 0) *
      P5CanonicalUpperCancellation.lowerBar (a*(1-normalizedLog N L x 0)) else 0

theorem weightedLower_eq {N n p d : ℕ} {root : Root} {t L hi a : ℝ} (r : ℚ)
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hlo : (1/5:ℝ)≤r) (hhi : hi≤1/2)
    (ha : 0≤a) (ha5 : a≤5) (hA : 4≤(N:ℝ)^(L/10))
    (hQ : rootQ N n root t p=(d:ℝ)*(N:ℝ)^L) :
    weightedLower N (rootQ N n root t p) L d r hi a =
      thetaAtom N (rootQ N n root t p) d*trueSingleTest N L d (singleDomain r hi) (lowerTest a) := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  unfold weightedLower trueSingleTest
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  have h0 := mem_actualPrimeBoxTuples_iff.mp hx 0
  have hp2 : 2<x 0 := by
    have hh := hA.trans h0.2.2.1
    exact_mod_cast (show (2:ℝ)<x 0 by linarith)
  have hne := prime_coordinate_ne_rat hN hL hQ x (fun i =>
    ⟨(mem_actualPrimeBoxTuples_iff.mp hx i).1,(mem_actualPrimeBoxTuples_iff.mp hx i).2.1⟩) 0 r
  have he : normalizedLog N L x ∈ singleHalf r hi ↔ normalizedLog N L x ∈ singleDomain r hi := by
    rw [singleHalf_partition]
    simp only [hne,false_and,or_false]
  by_cases hm : normalizedLog N L x ∈ singleHalf r hi
  · have hlog : log (x 0:ℝ)/log (rootQ N n root t p/d)=normalizedLog N L x 0 := by
      rw [hQ]; exact physical_log_ratio hN hd hL x 0
    rw [if_pos hm,indicator_of_mem (he.mp hm),
      thetaAtom_single (by omega) hd h0.1 hp2 (h0.1.coprime_iff_not_dvd.mpr h0.2.1) hR,hlog,
      canonical_lower_log (lowerOnWindow hlo hhi ha ha5 hm),lowerTest,residualSingle,
      max_eq_right (by linarith [hm.2] : (1/10:ℝ)≤1-normalizedLog N L x 0)]
    ring
  · simp only [if_neg hm,indicator_of_notMem (fun h => hm (he.mpr h)),mul_zero]

end
end ImbalancedChen.Part5OriginalH430OrdinarySingletonKernel
