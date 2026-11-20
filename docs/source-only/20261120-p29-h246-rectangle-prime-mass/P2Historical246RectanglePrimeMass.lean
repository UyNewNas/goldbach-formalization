import ImbalancedChen.P2Historical246StrictRectangleIntegral
import ImbalancedChen.P2OriginalPhysicalOldProfileMass

/-! SOURCE ONLY / UNEVALUATED. A target-N-deleted prime-pair test on the
actual H246 row-0 rectangle. The parent multiplier d remains arbitrary,
including repeated factors. No causal prefix coprimality, existence of a
marked source, ceiling payment, or H247 endpoint is asserted here. -/
namespace ImbalancedChen.P2Historical246RectanglePrimeMass
noncomputable section
open Set MeasureTheory Finset Filter
open scoped Classical BigOperators Topology
open P2Historical246StrictRectangleIntegral P2Historical246StrictDebit
open P2Historical246StrictCeilingChildUpper P2OriginalChildPhysicalNormalization
open P2HistoricalLowerBankAncestry P2Historical248Authentication
open P2HistoricalScheduledPointReads P5OriginalActionMassBound
open P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2OriginalBankChildPrimeMass P2OriginalCompactScaledPrimeMass
open P2OriginalCompactThetaMass P2OriginalPhysicalOldProfileMass

/-- Open rational box surrounding the earlier closed positive rectangle. -/
def rectForms : Fin 4 → Coord 2 →L[ℝ] ℝ := ![-coord 0,coord 0,-coord 1,coord 1]
def rectBounds : Fin 4 → ℝ := ![-(2499/10000:ℝ),2501/10000,-(2999/10000:ℝ),3001/10000]
def primeRect : Set (Coord 2) := primeAffineGateRegion rectForms rectBounds

theorem mem_primeRect {x : Coord 2} : x ∈ primeRect ↔
    (2499/10000:ℝ) < x 0 ∧ x 0 < 2501/10000 ∧
      (2999/10000:ℝ) < x 1 ∧ x 1 < 3001/10000 := by
  simp [primeRect,primeAffineGateRegion,rectForms,rectBounds,coord,Fin.forall_fin_succ]

theorem rectForms_ne (i : Fin 4) : rectForms i ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Coord 2 →L[ℝ] ℝ => A (fun _ => 1)) h
  fin_cases i <;> norm_num [rectForms,coord] at hh

theorem cutRect_subset_primeRect : cutRect ⊆ primeRect := by
  intro x hx
  exact mem_primeRect.mpr (cutRect_coordinate_bounds hx)

theorem primeRect_geometry {x : Coord 2} (hx : x ∈ primeRect) :
    x ∈ W2PairDomain (originalW2At 0) 0 ∧ x 0 < 2/7 ∧ 2/7 < x 1 := by
  obtain ⟨h0,h1,h2,h3⟩ := mem_primeRect.mp hx
  have hw0 : (249/1000:ℝ) < x 0 := by linarith
  have hw1 : x 0 < (251/1000:ℝ) := by linarith
  have hw2 : (299/1000:ℝ) < x 1 := by linarith
  have hw3 : x 1 < (301/1000:ℝ) := by linarith
  have hh := first_original_row_ceiling_cuts_open_rectangle hw0 hw1 hw2 hw3
  have hxid : ![x 0,x 1] = x := by funext i; fin_cases i <;> rfl
  rwa [hxid] at hh

theorem primeRect_in_cube : primeRect ⊆ cube 2 := by
  intro x hx
  obtain ⟨h0,h1,h2,h3⟩ := mem_primeRect.mp hx
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i <;> constructor <;> linarith

theorem primeRect_in_ambient : primeRect ⊆ pairAmbient := by
  intro x hx
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem 0)
  exact (W2PairDomain_geometry hg 0 (primeRect_geometry hx).1).1

/-- All prime-box points see the same original old-table cell. -/
theorem primeRect_table_constant {x : Coord 2} (hx : x ∈ primeRect) :
    tableFunction false (outputAt 246 true) (pairProfile (originalW2At 0) 0 x) = h52 := by
  obtain ⟨h0,h1,h2,h3⟩ := mem_primeRect.mp hx
  have hcell := first_row_profile_in_cell52 h0 h1 h2 h3
  have hxid : ![x 0,x 1] = x := by funext i; fin_cases i <;> rfl
  rw [hxid] at hcell
  let rho := pairProfile (originalW2At 0) 0 x
  let atom : FloorAtom := Sum.inl (52 : Fin 200)
  have hmem : rho ∈ upperAtomSet atom := by
    change (((1:ℝ) ≤ rho ∧ rho ≤ 5) ∧
      (floorGrid 52 < rho ∧ rho < floorGrid 53))
    norm_num [floorGrid]
    constructor <;> constructor <;> linarith [hcell.1,hcell.2]
  rw [tableFunction_upper]
  unfold upperFloor
  calc
    _ = (upperAtomSet atom).indicator (fun _ => floorAtomValue (outputAt 246 true) atom) rho := by
      apply Finset.sum_eq_single atom
      · intro c _ hca
        exact indicator_of_notMem (fun hc => hca (P5Z.U11H248.upperAtom_unique hc hmem)) _
      · intro h
        exact (h (Finset.mem_univ atom)).elim
    _ = _ := by simp [hmem,atom,floorAtomValue,h52]

def rectTest (x : Coord 2) : ℝ := residualPair x * h52

theorem rectTest_bound (x : Coord 2) : |rectTest x| ≤ 10*h52 := by
  rw [rectTest,abs_mul,abs_of_nonneg (residualPair_bounds x).1,abs_of_pos h52_positive]
  exact mul_le_mul_of_nonneg_right (residualPair_bounds x).2 h52_positive.le

/-- Prime-test normalization agrees with the real original kernel. -/
theorem rectTest_density {x : Coord 2} (hx : x ∈ primeRect) :
    rectTest x * (∏ i, 1/x i) = pairKernel x * h52 := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem 0)
  have hk := pair_kernel hg 0 (primeRect_geometry hx).1
  obtain ⟨h0,h1,h2,h3⟩ := mem_primeRect.mp hx
  have hr : (1/5:ℝ) ≤ 1-x 0-x 1 := by linarith
  rw [pairKernel_eq_raw (primeRect_in_ambient hx) hr]
  unfold rectTest
  rw [show residualPair x * h52 * (∏ i, 1/x i) =
    (residualPair x * (∏ i,1/x i))*h52 by ring, hk]

/-- The density on the larger open box retains the closed rectangle's
explicit positive lower bound. -/
theorem primeRect_density_lower : h52/100000000 ≤
    ∫ x in primeRect, rectTest x * (∏ i, 1/x i) := by
  have hi : IntegrableOn (fun x : Point => pairKernel x * h52) pairAmbient :=
    (pairKernel_continuous.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hmono := setIntegral_mono_set (hi.mono_set primeRect_in_ambient)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (pairKernel_nonneg x) h52_positive.le))
    (Filter.Eventually.of_forall cutRect_subset_primeRect)
  have hrect : h52/100000000 ≤ ∫ x in cutRect, pairKernel x*h52 := by
    have heq : (∫ x in cutRect, pairKernel x * tableFunction false (outputAt 246 true)
        (pairProfile (originalW2At 0) 0 x)) = ∫ x in cutRect, pairKernel x*h52 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      rw [cutRect_table_constant hx]
    rw [← heq]
    exact cutRect_old_profile_integral_lower
  have heq : (∫ x in primeRect, rectTest x*(∏ i,1/x i)) =
      ∫ x in primeRect, pairKernel x*h52 := by
    apply setIntegral_congr_fun (measurableSet_primeAffineGateRegion _ _)
    intro x hx
    exact rectTest_density hx
  rw [heq]
  exact hrect.trans hmono

/-- Uniformly for every original target N, compact residual exponent L,
and every actual parent multiplier d, the original fresh/repeated-factor
prime-box test has a positive lower bound. The threshold is chosen before
N, L and d; no division by Theta, no integer replacement of N, and no
parent coprimality or marked-source existence is assumed. -/
theorem rectangle_truePair_uniform_positive {Lmin Lmax : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      h52/200000000 < truePairTest N L d primeRect rectTest := by
  have hp : 0 < h52/400000000 := by positivity
  obtain ⟨Tp,hTp⟩ := compact_uniform_scaled_affine hmin hmax
    (show 0 ≤ 10*h52 by positivity) hp rectForms rectBounds rectForms_ne
    primeRect_in_cube rectTest (residualPair_continuous.mul continuous_const) rectTest_bound
  obtain ⟨Te,hTe⟩ := compact_multiplier_error (k:=2) hmin hmax
    (show 0 ≤ 60*h52 by positivity) hp
  refine ⟨max Tp Te,?_⟩
  intro N hN L hL d
  have ha := hTp N (by omega) L hL
  change |scaledPrimeSum N L primeRect rectTest -
    (∫ x in primeRect, rectTest x*(∏ i,1/x i))| < h52/400000000 at ha
  obtain ⟨hA,he⟩ := hTe N (by omega) L hL
  have hd := truePairTest_error d primeRect rectTest
    (show 0 ≤ 10*h52 by positivity) rectTest_bound hA
  have hc : 6*(10*h52)=60*h52 := by ring
  rw [hc] at hd
  have h1 := (abs_lt.mp ha).1
  have h2 := (abs_le.mp hd).1
  have hl := primeRect_density_lower
  linarith

/-- On that same actual N-deleted box, replacing the constant test by
the H246 row-0 pair test changes no summand. -/
theorem rectangle_truePair_is_original_profile (N : ℕ) (L : ℝ) (d : ℕ) :
    truePairTest N L d primeRect rectTest =
      truePairTest N L d primeRect (pairTest (originalW2At 0) 0 (outputAt 246 true)) := by
  unfold truePairTest
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  by_cases hx : normalizedLog N L p ∈ primeRect
  · rw [indicator_of_mem hx,indicator_of_mem hx]
    simp only [rectTest,pairTest,primeRect_table_constant hx]
  · rw [indicator_of_notMem hx,indicator_of_notMem hx]

/-- The same explicit lower bound for the literal old H246 profile test. -/
theorem rectangle_original_H246_uniform_positive {Lmin Lmax : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      h52/200000000 < truePairTest N L d primeRect
        (pairTest (originalW2At 0) 0 (outputAt 246 true)) := by
  obtain ⟨T,hT⟩ := rectangle_truePair_uniform_positive hmin hmax
  refine ⟨T,?_⟩
  intro N hN L hL d
  rw [← rectangle_truePair_is_original_profile]
  exact hT N hN L hL d

end
end ImbalancedChen.P2Historical246RectanglePrimeMass
