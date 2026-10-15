import ImbalancedChen.CurrentChenPairRosser
import ImbalancedChen.CurrentChenPairDensity
import ImbalancedChen.CurrentChenUpsilon6OrdinarySieveKernel
import ImbalancedChen.ChenPairHarmonicFinite
import ImbalancedChen.ActualPrimePolyhedralTestFunctions
import ImbalancedChen.CurrentChenUpsilon6FiniteMean
import ImbalancedChen.Part3CurrentLowerDistribution
import ImbalancedChen.MovingWeightTransport

/-!
# Ordinary arithmetic on the corrected sixth product domain

The buffer eta is fixed and positive before N tends to infinity. The
arithmetic source is the literal sixth quotient-source count without a
deletion mask. A strict inner selector deletes only nonnegative counts;
the lost horizontal and product walls have zero limiting integral mass.

The prime-pair harmonic supplier is proved from the actual affine-gate
prime-box theorem. A globally clipped residual profile makes its test
continuous on the whole common cube; the clipping is exactly the identity
on the actual sixth rectangle. No arithmetic limit, pointwise sieve,
distribution estimate, or measurability of a deletion mask is assumed.

Source candidate: this new module has not been compiled or kernel-replayed.
It supplies no causal h248 improvement or numerical manuscript constant.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

def currentChenUpsilon6OrdinaryForms : Fin 3 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![(ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ),
    -(ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ),
    (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
      (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)]

def currentChenUpsilon6OrdinaryCaps (eta : ℝ) : Fin 3 → ℝ :=
  ![(19 / 125 : ℝ), -(19 / 125 : ℝ), (833 / 2500 : ℝ) - eta]

theorem currentChenUpsilon6OrdinaryForms_ne_zero :
    ∀ j, currentChenUpsilon6OrdinaryForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (fun _ => 1)) h
  fin_cases j <;> norm_num [currentChenUpsilon6OrdinaryForms] at hh

theorem mem_currentChenUpsilon6OrdinaryAffineRegion (eta : ℝ) (x : Fin 2 → ℝ) :
    x ∈ primeAffineGateRegion currentChenUpsilon6OrdinaryForms
      (currentChenUpsilon6OrdinaryCaps eta) ↔
      x 0 < (19 / 125 : ℝ) ∧ (19 / 125 : ℝ) < x 1 ∧
        x 0 + x 1 < (833 / 2500 : ℝ) - eta := by
  simp [primeAffineGateRegion, currentChenUpsilon6OrdinaryForms,
    currentChenUpsilon6OrdinaryCaps, Fin.forall_fin_succ, neg_lt_neg_iff]

def currentChenUpsilon6OrdinaryStrictDomain (eta : ℝ) : Set (Fin 2 → ℝ) :=
  currentChenUpsilon6LogRectangle ∩
    {x | (19 / 125 : ℝ) < x 1 ∧ x 0 + x 1 < (833 / 2500 : ℝ) - eta}

/-- The three affine gates on one common cube give exactly the strict
inner rectangle and the strict corrected product domain. -/
theorem currentChenUpsilon6Ordinary_cube_gates_eq (eta : ℝ) :
    logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) ∩
        primeAffineGateRegion currentChenUpsilon6OrdinaryForms
          (currentChenUpsilon6OrdinaryCaps eta) =
      currentChenUpsilon6OrdinaryStrictDomain eta := by
  ext x
  rw [Set.mem_inter_iff, mem_currentChenUpsilon6OrdinaryAffineRegion]
  change _ ↔ x ∈ currentChenUpsilon6LogRectangle ∧ _
  rw [mem_currentChenUpsilon6LogRectangle]
  constructor
  · rintro ⟨hx, h0, h1, hp⟩
    have hx0 := mem_logPrimeBox.mp hx 0
    have hx1 := mem_logPrimeBox.mp hx 1
    exact ⟨⟨hx0.1, h0, h1.le, hx1.2⟩, h1, hp⟩
  · rintro ⟨⟨ha, hh, hh', hd⟩, h1, hp⟩
    refine ⟨mem_logPrimeBox.mpr ?_, hh, h1, hp⟩
    intro i
    fin_cases i
    · exact ⟨ha, hh.trans (by norm_num)⟩
    · exact ⟨(by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hh', hd⟩

/-- This set equality holds almost everywhere for any integrand. The
arithmetic selector itself is not modified using a null-wall assertion. -/
theorem integral_currentChenUpsilon6OrdinaryStrictDomain_eq
    (eta : ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ x in currentChenUpsilon6OrdinaryStrictDomain eta, f x) =
      ∫ x in currentChenUpsilon6LogDomain eta, f x := by
  have hhorizontal : ∀ᵐ x : Fin 2 → ℝ ∂volume, x 1 ≠ (19 / 125 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using
      currentChenUpsilon6_coordinateWall_volume_zero 1 (19 / 125)
  have hproduct : ∀ᵐ x : Fin 2 → ℝ ∂volume,
      x 0 + x 1 ≠ (833 / 2500 : ℝ) - eta := by
    rw [ae_iff]
    simpa only [not_not] using
      currentChenUpsilon6_productWall_volume_zero ((833 / 2500 : ℝ) - eta)
  apply setIntegral_congr_set
  filter_upwards [hhorizontal, hproduct] with x hh hp
  apply propext
  change (x ∈ currentChenUpsilon6LogRectangle ∧
    (19 / 125 : ℝ) < x 1 ∧ x 0 + x 1 < (833 / 2500 : ℝ) - eta) ↔
      x ∈ currentChenUpsilon6LogRectangle ∧ x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta
  constructor
  · rintro ⟨hx, _, hg⟩
    exact ⟨hx, hg.le⟩
  · rintro ⟨hx, hg⟩
    have hx1 := (mem_currentChenUpsilon6LogRectangle.mp hx).2.2.1
    exact ⟨hx, (lt_or_eq_of_le hx1).resolve_right (Ne.symm hh),
      (lt_or_eq_of_le hg).resolve_right hp⟩

private theorem sixthOrdinary_product_log_lt_iff {N : ℕ} (hN : 2 ≤ N)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (c : ℝ) :
    ((p * q : ℕ) : ℝ) < (N : ℝ) ^ c ↔
      Real.log (p : ℝ) / Real.log (N : ℝ) +
        Real.log (q : ℝ) / Real.log (N : ℝ) < c := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpow : (N : ℝ) ^
      (Real.log (p : ℝ) / Real.log (N : ℝ) +
        Real.log (q : ℝ) / Real.log (N : ℝ)) = ((p * q : ℕ) : ℝ) := by
    rw [Real.rpow_add (zero_lt_one.trans hNr),
      actualPrimeTupleLog_rpow (by omega) ![p, q]
        (by intro i; fin_cases i <;> assumption) 0,
      actualPrimeTupleLog_rpow (by omega) ![p, q]
        (by intro i; fin_cases i <;> assumption) 1]
    exact (Nat.cast_mul p q).symm
  simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr :
    (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ) +
      Real.log (q : ℝ) / Real.log (N : ℝ)) < (N : ℝ) ^ c ↔ _)

/-- Exact logarithmic description of the strict arithmetic inner selector. -/
theorem mem_currentChenUpsilon6OrdinarySelector_log_iff {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) (t : ℕ × ℕ) :
    t ∈ currentChenUpsilon6OrdinarySelector N eta ↔
      t.1 ∈ chenAdditivePrimeCarrier N ∧ t.2 ∈ chenAdditivePrimeCarrier N ∧
        currentChenUpsilon6LogCoordinates N t ∈ currentChenUpsilon6OrdinaryStrictDomain eta := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hgate (hp : t.1 ∈ chenAdditivePrimeCarrier N)
      (hq : t.2 ∈ chenAdditivePrimeCarrier N) :
      ((N : ℝ) ^ (19 / 125 : ℝ) < (t.2 : ℝ) ∧
        ((t.1 * t.2 : ℕ) : ℝ) < (N : ℝ) ^ ((833 / 2500 : ℝ) - eta)) ↔
      (19 / 125 : ℝ) < currentChenUpsilon6LogCoordinates N t 1 ∧
        currentChenUpsilon6LogCoordinates N t 0 +
          currentChenUpsilon6LogCoordinates N t 1 < (833 / 2500 : ℝ) - eta := by
    have hqpow := actualPrimeTupleLog_rpow (by omega) ![t.1, t.2]
      (by intro i; fin_cases i
          · exact (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
          · exact (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos) 1
    have hband : (N : ℝ) ^ (19 / 125 : ℝ) < (t.2 : ℝ) ↔
        (19 / 125 : ℝ) < Real.log (t.2 : ℝ) / Real.log (N : ℝ) := by
      simpa only [actualPrimeTupleLog, Matrix.cons_val_one] using
        (hqpow ▸ (Real.rpow_lt_rpow_left_iff hNr :
          (N : ℝ) ^ (19 / 125 : ℝ) <
            (N : ℝ) ^ (actualPrimeTupleLog N ![t.1, t.2] 1) ↔ _))
    simpa only [currentChenUpsilon6LogCoordinates, Matrix.cons_val_zero,
      Matrix.cons_val_one, hband] using
        and_congr hband (sixthOrdinary_product_log_lt_iff hN
          (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
          (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos ((833 / 2500 : ℝ) - eta))
  constructor
  · intro ht
    obtain ⟨hret, hstrict⟩ := Finset.mem_filter.mp ht
    obtain ⟨hp, hq, _hfalse, hweak⟩ :=
      (mem_currentChenUpsilon6RetainedSelector_log_iff hNr (fun _ => False) eta t).mp hret
    exact ⟨hp, hq, hweak.1, (hgate hp hq).mp hstrict⟩
  · rintro ⟨hp, hq, hbox, hh, hprod⟩
    refine Finset.mem_filter.mpr ⟨?_, (hgate hp hq).mpr ⟨hh, hprod⟩⟩
    exact (mem_currentChenUpsilon6RetainedSelector_log_iff hNr (fun _ => False) eta t).mpr
      ⟨hp, hq, by trivial, hbox, hprod.le⟩

private theorem sixthOrdinary_tuple_mem_iff {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) (p : Fin 2 → ℕ) :
    (p 0, p 1) ∈ currentChenUpsilon6OrdinarySelector N eta ↔
      p ∈ (actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ))).filter (fun p => actualPrimeTupleLog N p ∈
          primeAffineGateRegion currentChenUpsilon6OrdinaryForms
            (currentChenUpsilon6OrdinaryCaps eta)) := by
  have hN' : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN'
  have hupper : (N : ℝ) ^ (59 / 250 : ℝ) < N := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hNr
      (by norm_num : (59 / 250 : ℝ) < 1)
  have hcoords : currentChenUpsilon6LogCoordinates N (p 0, p 1) =
      actualPrimeTupleLog N p := by
    funext i
    fin_cases i <;> rfl
  rw [mem_currentChenUpsilon6OrdinarySelector_log_iff hN, hcoords]
  constructor
  · rintro ⟨hp, hq, hx⟩
    have hxc : actualPrimeTupleLog N p ∈
        logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) ∩
          primeAffineGateRegion currentChenUpsilon6OrdinaryForms
            (currentChenUpsilon6OrdinaryCaps eta) := by
      rw [currentChenUpsilon6Ordinary_cube_gates_eq eta]
      exact hx
    refine Finset.mem_filter.mpr ⟨?_, hxc.2⟩
    apply (mem_actualPrimeBoxTuples_log_iff hN' _ _ p).mpr
    refine ⟨?_, hxc.1⟩
    intro i
    fin_cases i
    · exact ⟨(mem_chenAdditivePrimeCarrier.mp hp).2.1,
        (mem_chenAdditivePrimeCarrier.mp hp).2.1.coprime_iff_not_dvd.mp
          (mem_chenAdditivePrimeCarrier.mp hp).2.2⟩
    · exact ⟨(mem_chenAdditivePrimeCarrier.mp hq).2.1,
        (mem_chenAdditivePrimeCarrier.mp hq).2.1.coprime_iff_not_dvd.mp
          (mem_chenAdditivePrimeCarrier.mp hq).2.2⟩
  · rintro hp
    obtain ⟨hpbox, hgate⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hpbox
    have hc (i : Fin 2) : p i ∈ chenAdditivePrimeCarrier N := by
      refine mem_chenAdditivePrimeCarrier.mpr ⟨?_, (hi i).1,
        (hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
      exact_mod_cast (hi i).2.2.2.trans hupper
    refine ⟨hc 0, hc 1, ?_⟩
    rw [← currentChenUpsilon6Ordinary_cube_gates_eq eta]
    exact ⟨((mem_actualPrimeBoxTuples_log_iff hN' _ _ p).mp hpbox).2, hgate⟩

/-- Exact harmonic reindexing. Distinctness is paid by the separated real
bands, before using the prime-pair totient product formula. -/
theorem currentChenUpsilon6Ordinary_harmonic_eq_actualPrimeBox
    {N : ℕ} (hN : 2 ≤ N) (eta : ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    (∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
      f (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)) =
      actualPrimeBoxTestSum N (fun _ : Fin 2 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ))
        ((primeAffineGateRegion currentChenUpsilon6OrdinaryForms
          (currentChenUpsilon6OrdinaryCaps eta)).indicator f) := by
  let T := (actualPrimeBoxTuples N (fun _ : Fin 2 => (417 / 5000 : ℝ))
    (fun _ => (59 / 250 : ℝ))).filter (fun p => actualPrimeTupleLog N p ∈
      primeAffineGateRegion currentChenUpsilon6OrdinaryForms
        (currentChenUpsilon6OrdinaryCaps eta))
  calc
    _ = ∑ p ∈ T, (∏ i, 1 / ((p i : ℝ) - 1)) * f (actualPrimeTupleLog N p) := by
      refine Finset.sum_bij (fun t _ => ![t.1, t.2]) ?_ ?_ ?_ ?_
      · intro t ht
        exact (sixthOrdinary_tuple_mem_iff hN eta ![t.1, t.2]).mp ht
      · intro t _ u _ heq
        exact Prod.ext (by simpa using congrFun heq 0) (by simpa using congrFun heq 1)
      · intro p hp
        refine ⟨(p 0, p 1), (sixthOrdinary_tuple_mem_iff hN eta p).mpr hp, ?_⟩
        funext i
        fin_cases i <;> rfl
      · intro t ht
        have htfull := currentChenUpsilon6OrdinarySelector_subset_original N eta ht
        obtain ⟨hc, _, hpH, hHq, _⟩ := Finset.mem_filter.mp htfull
        have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).1).2.1
        have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
        have horder : t.1 < t.2 := by exact_mod_cast hpH.trans_le hHq
        rw [chen_prime_pair_totient_cast hp hq horder.ne]
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
    _ = _ := by
      unfold T actualPrimeBoxTestSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hg : actualPrimeTupleLog N p ∈
          primeAffineGateRegion currentChenUpsilon6OrdinaryForms
            (currentChenUpsilon6OrdinaryCaps eta)
      · rw [if_pos hg, Set.indicator_of_mem hg]
      · rw [if_neg hg, Set.indicator_of_notMem hg, mul_zero]

/-- A genuine fixed-buffer harmonic limit. No arithmetic convergence or
null-boundary statement is a caller-supplied hypothesis. -/
theorem tendsto_currentChenUpsilon6Ordinary_harmonic_test
    (eta : ℝ) (f : (Fin 2 → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi
      (fun _ : Fin 2 => Set.Icc (417 / 5000 : ℝ) (59 / 250)))) :
    Tendsto (fun N : ℕ => ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
      f (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (∫ x in currentChenUpsilon6LogDomain eta, f x * ∏ i, 1 / x i)) := by
  have h := tendsto_actualPrimeBoxTestSum_cube_affineGates
    (by norm_num : (0 : ℝ) < 417 / 5000)
    (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    currentChenUpsilon6OrdinaryForms (currentChenUpsilon6OrdinaryCaps eta)
    currentChenUpsilon6OrdinaryForms_ne_zero f hf
  rw [currentChenUpsilon6Ordinary_cube_gates_eq,
    integral_currentChenUpsilon6OrdinaryStrictDomain_eq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (currentChenUpsilon6Ordinary_harmonic_eq_actualPrimeBox hN eta f).symm

/-- The clipping keeps the global test continuous even where the unused
part of the common cube would cross the logarithmic singularity s=1. -/
def currentChenUpsilon6OrdinaryClippedProfile (s : ℝ) : ℝ :=
  max (4 / 3 : ℝ) (min (16 / 5 : ℝ) s)

def currentChenUpsilon6OrdinaryFactor (s : ℝ) : ℝ :=
  4 * Real.log (s - 1) / (s * (417 / 5000))

def currentChenUpsilon6OrdinaryClippedTest (x : Fin 2 → ℝ) : ℝ :=
  currentChenUpsilon6OrdinaryFactor
    (currentChenUpsilon6OrdinaryClippedProfile (currentChenUpsilon6OrdinaryProfile x))

theorem currentChenUpsilon6OrdinaryClippedProfile_eq {s : ℝ}
    (hs : s ∈ Set.Icc (4 / 3 : ℝ) (16 / 5)) :
    currentChenUpsilon6OrdinaryClippedProfile s = s := by
  rw [currentChenUpsilon6OrdinaryClippedProfile, min_eq_right hs.2, max_eq_right hs.1]

theorem continuous_currentChenUpsilon6OrdinaryClippedTest :
    Continuous currentChenUpsilon6OrdinaryClippedTest := by
  have hp : Continuous currentChenUpsilon6OrdinaryProfile := by
    unfold currentChenUpsilon6OrdinaryProfile
    fun_prop
  have hc : Continuous (fun x : Fin 2 → ℝ => currentChenUpsilon6OrdinaryClippedProfile
      (currentChenUpsilon6OrdinaryProfile x)) :=
    continuous_const.max (continuous_const.min hp)
  have hpos (x : Fin 2 → ℝ) : 1 < currentChenUpsilon6OrdinaryClippedProfile
      (currentChenUpsilon6OrdinaryProfile x) :=
    (by norm_num : (1 : ℝ) < 4 / 3).trans_le (le_max_left _ _)
  unfold currentChenUpsilon6OrdinaryClippedTest currentChenUpsilon6OrdinaryFactor
  apply (continuous_const.mul ((hc.sub continuous_const).log ?_)).div
    (hc.mul continuous_const) ?_
  · intro x
    exact (sub_pos.mpr (hpos x)).ne'
  · intro x
    exact mul_ne_zero (zero_lt_one.trans (hpos x)).ne' (by norm_num)

theorem currentChenUpsilon6OrdinaryClippedTest_eq {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) :
    currentChenUpsilon6OrdinaryClippedTest x =
      currentChenUpsilon6OrdinaryFactor (currentChenUpsilon6OrdinaryProfile x) := by
  obtain ⟨ha, hh, hh', hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
  have hs : currentChenUpsilon6OrdinaryProfile x ∈ Set.Icc (4 / 3 : ℝ) (16 / 5) := by
    unfold currentChenUpsilon6OrdinaryProfile
    constructor <;> norm_num <;> linarith
  rw [currentChenUpsilon6OrdinaryClippedTest,
    currentChenUpsilon6OrdinaryClippedProfile_eq hs]

/-- The exact fixed-buffer coefficient on the corrected original domain. -/
def currentChenUpsilon6OrdinaryIntegral (eta : ℝ) : ℝ :=
  ∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x

private theorem sixthOrdinary_coords_eq_actualLog (N : ℕ) (t : ℕ × ℕ) :
    currentChenUpsilon6LogCoordinates N t = actualPrimeTupleLog N ![t.1, t.2] := by
  funext i
  fin_cases i <;> rfl

private theorem sixthOrdinary_profile_actualLog {N : ℕ} {eta : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6OrdinarySelector N eta) :
    currentChenUpsilon6OrdinaryProfile (actualPrimeTupleLog N ![t.1, t.2]) =
      currentChenPairLogProfile N (t.1 * t.2) := by
  have htfull := currentChenUpsilon6OrdinarySelector_subset_original N eta ht
  have hc := (Finset.mem_filter.mp htfull).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).1).2.1
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  unfold currentChenUpsilon6OrdinaryProfile currentChenPairLogProfile
  rw [chen_prime_log_product_coordinate N hp hq]
  simp only [actualPrimeTupleLog, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The harmonic test contains only the sieve factor. The prime-box
measure supplies the reciprocal-coordinate density exactly once. -/
theorem tendsto_currentChenUpsilon6Ordinary_harmonic_mean (eta : ℝ) :
    Tendsto (fun N : ℕ => ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
      currentChenUpsilon6OrdinaryFactor (currentChenPairLogProfile N (t.1 * t.2)) /
        (Nat.totient (t.1 * t.2) : ℝ)) atTop
      (𝓝 (currentChenUpsilon6OrdinaryIntegral eta)) := by
  have h := tendsto_currentChenUpsilon6Ordinary_harmonic_test eta
    currentChenUpsilon6OrdinaryClippedTest
    continuous_currentChenUpsilon6OrdinaryClippedTest.continuousOn
  have hmeas : MeasurableSet (currentChenUpsilon6LogDomain eta) :=
    measurableSet_currentChenUpsilon6LogRectangle.inter
      ((isClosed_le ((continuous_apply 0).add (continuous_apply 1))
        continuous_const).measurableSet)
  have hi : (∫ x in currentChenUpsilon6LogDomain eta,
      currentChenUpsilon6OrdinaryClippedTest x * ∏ i, 1 / x i) =
        currentChenUpsilon6OrdinaryIntegral eta := by
    apply setIntegral_congr_fun hmeas
    intro x hx
    rw [currentChenUpsilon6OrdinaryClippedTest_eq hx.1]
    unfold currentChenUpsilon6OrdinaryKernel currentChenUpsilon6OrdinaryFactor
    simp only [Fin.prod_univ_two]
    ring
  rw [hi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  apply Finset.sum_congr rfl
  intro t ht
  have hx := ((mem_currentChenUpsilon6OrdinarySelector_log_iff hN eta t).mp ht).2.2.1
  rw [sixthOrdinary_coords_eq_actualLog] at hx
  rw [currentChenUpsilon6OrdinaryClippedTest_eq hx, sixthOrdinary_profile_actualLog ht]

theorem currentChenUpsilon6Ordinary_reciprocalTotient_eventually_bounded (eta : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop,
      (∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
        1 / (Nat.totient (t.1 * t.2) : ℝ)) ≤ M := by
  exact exists_eventually_bounded_mass_of_tendsto
    (tendsto_currentChenUpsilon6Ordinary_harmonic_test eta (fun _ => (1 : ℝ))
      continuousOn_const)

private theorem continuousOn_sixthOrdinaryFactor :
    ContinuousOn currentChenUpsilon6OrdinaryFactor (Set.Icc (4 / 3 : ℝ) (16 / 5)) := by
  unfold currentChenUpsilon6OrdinaryFactor
  apply (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).log ?_)).div
    (continuousOn_id.mul continuousOn_const) ?_
  · intro s hs
    exact (show 0 < s - 1 by linarith [hs.1]).ne'
  · intro s hs
    exact mul_ne_zero (show 0 < s by linarith [hs.1]).ne' (by norm_num)

/-- The moving rounded row coordinate can be transported inside the true
harmonic mass. The full rectangle supplies a fixed compact interval. -/
theorem tendsto_currentChenUpsilon6Ordinary_moving_harmonic (B eta : ℝ) :
    Tendsto (fun N : ℕ => ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
      (1 / (Nat.totient (t.1 * t.2) : ℝ)) * currentChenUpsilon6OrdinaryFactor
        (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2))) atTop
      (𝓝 (currentChenUpsilon6OrdinaryIntegral eta)) := by
  obtain ⟨M, hM, hmass⟩ := currentChenUpsilon6Ordinary_reciprocalTotient_eventually_bounded eta
  let T := fun N : ℕ => currentChenUpsilon6OrdinarySelector N eta
  let w := fun (_N : ℕ) (t : ℕ × ℕ) => 1 / (Nat.totient (t.1 * t.2) : ℝ)
  let x := fun N (t : ℕ × ℕ) => chenQuotientRosserT B (417 / 5000) N (t.1 * t.2)
  let y := fun N (t : ℕ × ℕ) => currentChenPairLogProfile N (t.1 * t.2)
  have hfixed : Tendsto (fun N : ℕ =>
      ∑ t ∈ T N, w N t * currentChenUpsilon6OrdinaryFactor (y N t)) atTop
        (𝓝 (currentChenUpsilon6OrdinaryIntegral eta)) := by
    apply (tendsto_currentChenUpsilon6Ordinary_harmonic_mean eta).congr'
    apply Eventually.of_forall
    intro N
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [w, y]
    ring
  apply tendsto_nonneg_weighted_comp_of_compact T w x y
    (Set.Icc (4 / 3 : ℝ) (16 / 5)) currentChenUpsilon6OrdinaryFactor M
    (currentChenUpsilon6OrdinaryIntegral eta) isCompact_Icc
    continuousOn_sixthOrdinaryFactor hM
    (Eventually.of_forall (fun N t ht => by dsimp [w]; positivity)) hmass ?_ ?_ hfixed
  · filter_upwards [eventually_currentChenUpsilon6_row_interval B,
      eventually_ge_atTop (2 : ℕ)] with N hrow hN
    intro t ht
    have htfull := currentChenUpsilon6OrdinarySelector_subset_original N eta ht
    have hs := hrow t htfull
    have hp := currentChenUpsilon6_profile_mem hN htfull
    exact ⟨⟨hs.1.le, hs.2.le⟩, ⟨by linarith [hp.1], by linarith [hp.2]⟩⟩
  · intro delta hdelta
    filter_upwards [eventually_currentChenUpsilon6_row_profile B delta hdelta] with N hrow
    intro t ht
    exact hrow t (currentChenUpsilon6OrdinarySelector_subset_original N eta ht)

/-- On the fixed positive buffer the actual physical row parameter is
above two, after paying both rounding and logarithmic distribution loss. -/
theorem eventually_currentChenUpsilon6Ordinary_row_density_lower
    (B eta epsilon : ℝ) (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈ currentChenUpsilon6OrdinarySelector N eta,
      currentChenUpsilon6OrdinaryFactor
          (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2)) - epsilon ≤
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
            Real.log (N : ℝ) / singularSeries N := by
  filter_upwards [eventually_currentChen_quotientRosserDensity_lower B epsilon hepsilon,
    eventually_currentChenUpsilon6Retained_physical_gates B eta heta,
    eventually_currentChenUpsilon6_row_interval B] with N hdensity hpositive hinterval
  intro hEven t ht
  have hret := currentChenUpsilon6OrdinarySelector_subset_retained N eta ht
  have hslo := (hpositive (fun _ => False) t hret).2.2
  have hshi := (hinterval t
    (currentChenUpsilon6OrdinarySelector_subset_original N eta ht)).2
  exact hdensity hEven (t.1 * t.2) ⟨hslo.le, hshi.le.trans (by norm_num)⟩

/-- A one-sided normalized density main-sum bound on the genuine fixed
buffer. The analytic lower supplier suffices; no opposite density bound
or actual finite odd-box reconstruction is used. -/
theorem eventually_currentChenUpsilon6Ordinary_normalized_density_lower
    (B eta epsilon : ℝ) (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon6OrdinaryIntegral eta - epsilon ≤
        ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
          (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
            (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
              ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
                Real.log (N : ℝ) / singularSeries N) := by
  obtain ⟨M, hM, hmass⟩ := currentChenUpsilon6Ordinary_reciprocalTotient_eventually_bounded eta
  let T := fun N : ℕ => currentChenUpsilon6OrdinarySelector N eta
  let w := fun (_N : ℕ) (t : ℕ × ℕ) => 1 / (Nat.totient (t.1 * t.2) : ℝ)
  let f := fun N (t : ℕ × ℕ) =>
    actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
      ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
        Real.log (N : ℝ) / singularSeries N
  let g := fun N (t : ℕ × ℕ) => currentChenUpsilon6OrdinaryFactor
    (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2))
  let delta : ℝ := epsilon / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by linarith
  have hdeltap : 0 < delta := div_pos hepsilon hden
  have hcost : delta * M ≤ epsilon / 2 := by
    have h := mul_le_mul_of_nonneg_left (show M ≤ M + 1 by linarith) hdeltap.le
    have hid : delta * (M + 1) = epsilon / 2 := by
      dsimp [delta]
      field_simp [show M + 1 ≠ 0 by linarith]
    linarith only [h, hid]
  have hnear : ∀ᶠ N : ℕ in atTop,
      currentChenUpsilon6OrdinaryIntegral eta - epsilon / 2 <
        ∑ t ∈ T N, w N t * g N t :=
    (tendsto_currentChenUpsilon6Ordinary_moving_harmonic B eta).eventually
      (Ioi_mem_nhds (by linarith : currentChenUpsilon6OrdinaryIntegral eta - epsilon / 2 <
        currentChenUpsilon6OrdinaryIntegral eta))
  filter_upwards [hmass, hnear,
    eventually_currentChenUpsilon6Ordinary_row_density_lower B eta delta heta hdeltap]
    with N hmassN hnearN hrows
  intro hEven
  have hsum : (∑ t ∈ T N, w N t * g N t) - delta * (∑ t ∈ T N, w N t) ≤
      ∑ t ∈ T N, w N t * f N t := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have h := mul_le_mul_of_nonneg_left (hrows hEven t ht)
      (show 0 ≤ w N t by dsimp [w]; positivity)
    change w N t * (g N t - delta) ≤ w N t * f N t at h
    nlinarith only [h]
  have hmasscost := (mul_le_mul_of_nonneg_left hmassN hdeltap.le).trans hcost
  change currentChenUpsilon6OrdinaryIntegral eta - epsilon ≤ ∑ t ∈ T N, w N t * f N t
  linarith only [hsum, hmasscost, hnearN]

/-- At each fixed positive buffer, the actual strict sixth subcount has its
ordinary kernel lower mean. Physical BV support and every error are paid.
This does not assert a causal improvement or a mean for a deletion mask. -/
theorem eventually_currentChenUpsilon6Ordinary_ge_mean
    (eta : ℝ) (heta : 0 < eta) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((currentChenUpsilon6OrdinaryIntegral eta) - epsilon) * singularNormalization N ≤
        currentChenUpsilon6OrdinaryCount N eta := by
  by_cases hI : 0 < (currentChenUpsilon6OrdinaryIntegral eta)
  · obtain ⟨B, _hB, hpaid⟩ := eventually_currentChenUpsilon6Ordinary_ge_density_sum
    let delta : ℝ := min (epsilon / 2) ((currentChenUpsilon6OrdinaryIntegral eta) / 2)
    have hdeltap : 0 < delta := lt_min (half_pos hepsilon) (half_pos hI)
    have hdeltae : delta ≤ epsilon / 2 := min_le_left _ _
    have hdeltaI : delta ≤ (currentChenUpsilon6OrdinaryIntegral eta) / 2 := min_le_right _ _
    have hnear : ∀ᶠ N : ℕ in atTop, Even N →
        (currentChenUpsilon6OrdinaryIntegral eta) - delta <
          ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
            (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
              (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
                ((N : ℝ) ^ (417 / 5000 : ℝ))
                  (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
                    Real.log (N : ℝ) / singularSeries N) := by
      filter_upwards [eventually_currentChenUpsilon6Ordinary_normalized_density_lower
        B eta (delta / 2) heta (half_pos hdeltap)] with N hlower
      intro hEven
      have h := hlower hEven
      linarith only [h, hdeltap]
    filter_upwards [hnear, hpaid eta (epsilon / 2) (half_pos hepsilon),
      eventually_ge_atTop (2 : ℕ)] with N hnearN hpaidN hN
    intro hEven
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
    have hlogp := Real.log_pos hN1
    have hSSp := singularSeries_pos N
    have hH : 0 ≤ singularNormalization N :=
      div_nonneg (mul_nonneg hSSp.le hNp.le) (sq_nonneg _)
    let V : ℝ := ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) /
            (Nat.totient (t.1 * t.2) : ℝ)
    have hvnorm : (currentChenUpsilon6OrdinaryIntegral eta) - delta ≤
        V * Real.log (N : ℝ) / singularSeries N := by
      have h := (hnearN hEven).le
      have heq : (∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
          (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
            (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
              ((N : ℝ) ^ (417 / 5000 : ℝ))
                (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
                  Real.log (N : ℝ) / singularSeries N)) =
            V * Real.log (N : ℝ) / singularSeries N := by
        dsimp [V]
        rw [Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      rwa [heq] at h
    have hv : 0 ≤ V := by
      have hn : 0 < V * Real.log (N : ℝ) / singularSeries N :=
        (show 0 < (currentChenUpsilon6OrdinaryIntegral eta) - delta by linarith).trans_le hvnorm
      have hm := (div_pos_iff_of_pos_right hSSp).mp hn
      exact ((mul_pos_iff_of_pos_right hlogp).mp hm).le
    have hli : (N : ℝ) / Real.log (N : ℝ) ≤ trueLogarithmicIntegral N :=
      MathlibNt.SieveTheory.LiuWeight.div_log_le_liuLogarithmicIntegral
        (by exact_mod_cast hN)
    have hmain : ((currentChenUpsilon6OrdinaryIntegral eta) - delta) *
        singularNormalization N ≤ currentChenUpsilon6OrdinaryDensitySum B N (currentChenUpsilon6OrdinarySelector N eta) := by
      calc
        _ ≤ (V * Real.log (N : ℝ) / singularSeries N) * singularNormalization N :=
          mul_le_mul_of_nonneg_right hvnorm hH
        _ = ((N : ℝ) / Real.log (N : ℝ)) * V := by
          unfold singularNormalization
          field_simp [hSSp.ne', hlogp.ne']
          ring
        _ ≤ trueLogarithmicIntegral N * V := mul_le_mul_of_nonneg_right hli hv
        _ = _ := by
          unfold currentChenUpsilon6OrdinaryDensitySum V
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
    have hfinite := hpaidN hEven
    have hbudget := mul_le_mul_of_nonneg_right hdeltae hH
    nlinarith only [hmain, hfinite, hbudget]
  · apply Eventually.of_forall
    intro N hEven
    have hH : 0 ≤ singularNormalization N :=
      div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
    have hc : (currentChenUpsilon6OrdinaryIntegral eta) - epsilon ≤ 0 := by linarith
    have hnonneg : 0 ≤ currentChenUpsilon6OrdinaryCount N eta := by
      unfold currentChenUpsilon6OrdinaryCount
      exact Finset.sum_nonneg (fun P hP => Nat.cast_nonneg _)
    exact (mul_nonpos_of_nonpos_of_nonneg hc hH).trans hnonneg


/-- The strict inner count is a valid lower bound for the actual unmasked
sixth row; only nonnegative original arithmetic contributions are dropped. -/
theorem eventually_currentChenUpsilon6_false_ge_fixed_buffer_ordinary_mean
    (eta : ℝ) (heta : 0 < eta) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentChenUpsilon6OrdinaryIntegral eta - epsilon) * singularNormalization N ≤
        currentChenUpsilon6 N (fun _ => False) := by
  filter_upwards [eventually_currentChenUpsilon6Ordinary_ge_mean eta heta epsilon hepsilon]
    with N hN
  intro hEven
  exact (hN hEven).trans
    (currentChenUpsilon6OrdinaryCount_le_currentChenUpsilon6_false N eta)

/-- First choose a fixed positive buffer using the proved kernel limit;
then take N sufficiently large for that fixed buffer. No exchange of the
arithmetic limit with the buffer limit or mask estimate is assumed. -/
theorem eventually_currentChenUpsilon6_false_ge_ordinary_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentChenUpsilon6OrdinaryIntegral 0 - epsilon) * singularNormalization N ≤
        currentChenUpsilon6 N (fun _ => False) := by
  have hlimit : Tendsto currentChenUpsilon6OrdinaryIntegral (𝓝[>] (0 : ℝ))
      (𝓝 (currentChenUpsilon6OrdinaryIntegral 0)) :=
    tendsto_integral_currentChenUpsilon6OrdinaryKernel_buffer.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      0 < eta ∧ currentChenUpsilon6OrdinaryIntegral 0 - epsilon / 2 <
        currentChenUpsilon6OrdinaryIntegral eta := by
    filter_upwards [self_mem_nhdsWithin,
      hlimit.eventually (Ioi_mem_nhds
        (by linarith : currentChenUpsilon6OrdinaryIntegral 0 - epsilon / 2 <
          currentChenUpsilon6OrdinaryIntegral 0))] with eta heta hI
    exact ⟨heta, hI⟩
  obtain ⟨eta, heta, hI⟩ := hnear.exists
  filter_upwards [eventually_currentChenUpsilon6_false_ge_fixed_buffer_ordinary_mean
    eta heta (epsilon / 2) (half_pos hepsilon)] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right
    (show currentChenUpsilon6OrdinaryIntegral 0 - epsilon ≤
      currentChenUpsilon6OrdinaryIntegral eta - epsilon / 2 by linarith only [hI]) hH).trans
        (hN hEven)
end

end ImbalancedChen
