import ImbalancedChen.Part5OriginalH430BuchstabInteriorPrimeLimit
import ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment
import ImbalancedChen.P2OriginalPrefixMaskMass
import ImbalancedChen.P2OriginalHalfOpenProfileCarrier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual d*N deletion and all choices of open/closed interval endpoints
are paid in finite prime sums. A singleton is not declared empty because
its limiting Lebesgue mass is zero. The threshold precedes N, the prefix,
the residual, both endpoints, and the endpoint-inclusion choices.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabMaskedIntervals

noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalChildPhysicalNormalization P2OriginalCompactThetaMass
open P2OriginalPrefixMaskMass P2OriginalHalfOpenProfileCarrier
open Part5OriginalH430BuchstabInteriorPrimeLimit
open Part5OriginalH430BuchstabCeilingPayment (localPrimeFactor_le_two_div)

/-- The original target N is not replaced by floor(N^L). -/
def primeCoordinate (N : ℕ) (L : ℝ) (q : ℕ) : ℝ :=
  normalizedLog N L (fun _ : Fin 1 => q) 0

def residualKernel (u : ℝ) : ℝ := 1/max (1/10:ℝ) (1-u)

def enlargedWindow (M N : ℕ) (L : ℝ) : Finset ℕ :=
  primeWindow M ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5))

def unmaskedMass (N : ℕ) (L : ℝ) (d : ℕ) (D : Set ℝ) : ℝ :=
  ∑ q ∈ enlargedWindow N N L,
    localPrimeFactor d q * D.indicator residualKernel (primeCoordinate N L q)

def windowMass (N : ℕ) (L : ℝ) (d : ℕ) (D : Set ℝ) : ℝ :=
  ∑ q ∈ enlargedWindow (d*N) N L,
    localPrimeFactor d q * D.indicator residualKernel (primeCoordinate N L q)

theorem residualKernel_bounds (u : ℝ) : 0 ≤ residualKernel u ∧ residualKernel u ≤ 10 :=
  residualSingle_bounds (fun _ => u)

theorem residualKernel_test_bound (D : Set ℝ) (u : ℝ) :
    |D.indicator residualKernel u| ≤ 10 := by
  by_cases hu : u ∈ D
  · rw [indicator_of_mem hu, abs_of_nonneg (residualKernel_bounds u).1]
    exact (residualKernel_bounds u).2
  · simp only [indicator_of_notMem hu, abs_zero]
    norm_num

theorem enlarged_window_reindex (N : ℕ) (L : ℝ) (F : ℕ → ℝ) :
    (∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5), F (p 0)) =
      ∑ q ∈ enlargedWindow N N L, F q := by
  have hm (p : Fin 1 → ℕ) :
      p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) ↔
        p 0 ∈ enlargedWindow N N L := by
    constructor
    · intro hp
      have h := mem_actualPrimeBoxTuples_iff.mp hp 0
      exact mem_primeWindow.mpr ⟨h.1, h.1.coprime_iff_not_dvd.mpr h.2.1, h.2.2⟩
    · intro hp
      have h := mem_primeWindow.mp hp
      apply mem_actualPrimeBoxTuples_iff.mpr
      intro i
      fin_cases i
      exact ⟨h.1, h.1.coprime_iff_not_dvd.mp h.2.1, h.2.2⟩
  apply Finset.sum_bij (fun p _ => p 0)
  · intro p hp
    exact (hm p).mp hp
  · intro p hp q hq heq
    funext i
    fin_cases i
    exact heq
  · intro q hq
    exact ⟨fun _ => q, (hm _).mpr hq, rfl⟩
  · intro p hp
    rfl

theorem unmasked_open_eq (N : ℕ) (L : ℝ) (d : ℕ) (lo hi : ℝ) :
    unmaskedMass N L d (Ioo lo hi) = trueSingleMass N L d lo hi := by
  unfold unmaskedMass
  rw [← enlarged_window_reindex]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (fun _ : Fin 1 => p 0) = p := by
    funext i
    fin_cases i
    rfl
  simp only [primeCoordinate, he]
  by_cases hx : lo < normalizedLog N L p 0 ∧ normalizedLog N L p 0 < hi
  · simp only [indicator_of_mem (show normalizedLog N L p 0 ∈ Ioo lo hi from hx),
      indicator_of_mem (show normalizedLog N L p ∈ singleDomain lo hi from hx)]
    rfl
  · simp only [indicator_of_notMem (show normalizedLog N L p 0 ∉ Ioo lo hi from hx),
      indicator_of_notMem (show normalizedLog N L p ∉ singleDomain lo hi from hx), mul_zero]

theorem compact_uniform_mask_difference {Lmin epsilon : ℝ}
    (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L : ℝ, Lmin ≤ L →
      ∀ d : ℕ, 0 < d → d ≤ N → ∀ D : Set ℝ,
        |windowMass N L d D-unmaskedMass N L d D| < epsilon := by
  obtain ⟨T,hT⟩ := compact_uniform_prefixMask_difference
    (by positivity : 0 < Lmin/10) (by norm_num : (0:ℝ) ≤ 10) he
  refine ⟨max 2 T, ?_⟩
  intro N hN L hL d hd hdN D
  exact hT N (by omega) d hd hdN _ _
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith))
    (fun q => D.indicator residualKernel (primeCoordinate N L q))
    (fun q hq => residualKernel_test_bound D _)

theorem compact_uniform_masked_openInterval {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ lo ∈ Icc (1/6:ℝ) (1/2), ∀ hi ∈ Icc (1/6:ℝ) (1/2),
      ∀ d : ℕ, 0 < d → d ≤ N →
      |windowMass N L d (Ioo lo hi)-intervalIntegral lo hi| < epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_true_openInterval hmin hmax
    (by positivity : 0 < epsilon/2)
  obtain ⟨Tm,hTm⟩ := compact_uniform_mask_difference hmin
    (by positivity : 0 < epsilon/2)
  refine ⟨max Tp Tm, ?_⟩
  intro N hN L hL lo hlo hi hhi d hd hdN
  have hp := hTp N (by omega) L hL lo hlo hi hhi d
  have hm := hTm N (by omega) L hL.1 d hd hdN (Ioo lo hi)
  rw [unmasked_open_eq] at hm
  have ht := abs_sub_le (windowMass N L d (Ioo lo hi))
    (trueSingleMass N L d lo hi) (intervalIntegral lo hi)
  linarith

theorem primeCoordinate_rpow {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    {q : ℕ} (hq : 0 < q) : (N:ℝ)^(L*primeCoordinate N L q) = q :=
  normalizedLog_rpow hN hL (fun _ : Fin 1 => q) (fun _ => hq) 0

theorem primeCoordinate_injective {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (he : primeCoordinate N L q = primeCoordinate N L r) : q = r := by
  have hpow := congrArg (fun u : ℝ => (N:ℝ)^(L*u)) he
  rw [primeCoordinate_rpow hN hL hq, primeCoordinate_rpow hN hL hr] at hpow
  exact_mod_cast hpow

theorem windowMass_singleton (N : ℕ) (L : ℝ) (d : ℕ) (t : ℝ) :
    windowMass N L d {t} =
      ∑ q ∈ (enlargedWindow (d*N) N L).filter (fun q => primeCoordinate N L q = t),
        localPrimeFactor d q * residualKernel (primeCoordinate N L q) := by
  unfold windowMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases ht : primeCoordinate N L q = t <;> simp [ht]

/-- A moving singleton contains at most one actual prime, not zero primes. -/
theorem singleton_card_le_one {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (d : ℕ) (t : ℝ) :
    ((enlargedWindow (d*N) N L).filter (fun q => primeCoordinate N L q = t)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  obtain ⟨hq,hqt⟩ := Finset.mem_filter.mp hq
  obtain ⟨hr,hrt⟩ := Finset.mem_filter.mp hr
  exact primeCoordinate_injective hN hL (mem_primeWindow.mp hq).1.pos
    (mem_primeWindow.mp hr).1.pos (hqt.trans hrt.symm)

theorem windowMass_nonneg {N : ℕ} {L : ℝ} (d : ℕ) (D : Set ℝ)
    (hA : 4 ≤ (N:ℝ)^(L/10)) : 0 ≤ windowMass N L d D := by
  apply Finset.sum_nonneg
  intro q hq
  have hq4 := hA.trans (mem_primeWindow.mp hq).2.2.1
  exact mul_nonneg (localPrimeFactor_pos (by linarith : (2:ℝ) < q)).le
    (Set.indicator_nonneg (fun u _ => (residualKernel_bounds u).1) _)

theorem singleton_mass_le {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (d : ℕ) (t : ℝ) (hA : 4 ≤ (N:ℝ)^(L/10)) :
    windowMass N L d {t} ≤ 20/(N:ℝ)^(L/10) := by
  let A := (N:ℝ)^(L/10)
  have hA0 : 0 < A := by dsimp [A]; linarith
  have hconst : 0 ≤ 20/A := by positivity
  rw [windowMass_singleton]
  calc
    _ ≤ ∑ _q ∈ (enlargedWindow (d*N) N L).filter
        (fun q => primeCoordinate N L q = t), 20/A := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).1
      have hfloor : A ≤ (q:ℝ) := (mem_primeWindow.mp hq').2.2.1
      have hq4 : (4:ℝ) ≤ q := hA.trans hfloor
      have hp : localPrimeFactor d q ≤ 2/A :=
        (localPrimeFactor_le_two_div hq4).trans
          (div_le_div_of_nonneg_left (by norm_num) hA0 hfloor)
      have hk := residualKernel_bounds (primeCoordinate N L q)
      calc
        _ ≤ (2/A)*10 := mul_le_mul hp hk.2 hk.1 (by positivity)
        _ = _ := by ring
    _ = (((enlargedWindow (d*N) N L).filter
        (fun q => primeCoordinate N L q = t)).card : ℝ) * (20/A) := by simp
    _ ≤ 1*(20/A) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast singleton_card_le_one hN hL d t) hconst
    _ = _ := one_mul _

/-- The same bound covers open, half-open, closed and empty/singleton
endpoint choices. No measurability or asymptotic estimate is a premise. -/
theorem interval_test_sandwich {lo hi : ℝ} {D : Set ℝ}
    (hinner : Ioo lo hi ⊆ D) (houter : D ⊆ Icc lo hi) (u : ℝ) :
    0 ≤ D.indicator residualKernel u-(Ioo lo hi).indicator residualKernel u ∧
    D.indicator residualKernel u-(Ioo lo hi).indicator residualKernel u ≤
      ({lo}:Set ℝ).indicator residualKernel u+({hi}:Set ℝ).indicator residualKernel u := by
  have hk := (residualKernel_bounds u).1
  have helo : 0 ≤ ({lo}:Set ℝ).indicator residualKernel u :=
    Set.indicator_nonneg (fun x _ => (residualKernel_bounds x).1) _
  have hehi : 0 ≤ ({hi}:Set ℝ).indicator residualKernel u :=
    Set.indicator_nonneg (fun x _ => (residualKernel_bounds x).1) _
  by_cases hu : u ∈ Ioo lo hi
  · simp only [indicator_of_mem hu, indicator_of_mem (hinner hu), sub_self]
    exact ⟨le_rfl, add_nonneg helo hehi⟩
  · rw [indicator_of_notMem hu, sub_zero]
    by_cases hD : u ∈ D
    · rw [indicator_of_mem hD]
      have hc := houter hD
      have hend : u = lo ∨ u = hi := by
        by_cases hl : u = lo
        · exact Or.inl hl
        · exact Or.inr (le_antisymm hc.2 (le_of_not_gt
            (fun hh => hu ⟨lt_of_le_of_ne hc.1 (Ne.symm hl), hh⟩)))
      rcases hend with rfl | rfl
      · rw [indicator_of_mem (show lo ∈ ({lo} : Set ℝ) from rfl)]
        exact ⟨hk, le_add_of_nonneg_right hehi⟩
      · rw [indicator_of_mem (show hi ∈ ({hi} : Set ℝ) from rfl)]
        exact ⟨hk, le_add_of_nonneg_left helo⟩
    · rw [indicator_of_notMem hD]
      exact ⟨le_rfl, add_nonneg helo hehi⟩

theorem interval_mass_sandwich {N : ℕ} (hN : 1 < N) {L : ℝ} (hL : 0 < L)
    (d : ℕ) {lo hi : ℝ} {D : Set ℝ}
    (hinner : Ioo lo hi ⊆ D) (houter : D ⊆ Icc lo hi)
    (hA : 4 ≤ (N:ℝ)^(L/10)) :
    |windowMass N L d D-windowMass N L d (Ioo lo hi)| ≤ 40/(N:ℝ)^(L/10) := by
  have hn : 0 ≤ windowMass N L d D-windowMass N L d (Ioo lo hi) := by
    unfold windowMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro q hq
    rw [← mul_sub]
    have hq4 := hA.trans (mem_primeWindow.mp hq).2.2.1
    exact mul_nonneg (localPrimeFactor_pos (by linarith : (2:ℝ) < q)).le
      (interval_test_sandwich hinner houter _).1
  rw [abs_of_nonneg hn]
  calc
    _ ≤ windowMass N L d {lo}+windowMass N L d {hi} := by
      unfold windowMass
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q hq
      rw [← mul_sub, ← mul_add]
      have hq4 := hA.trans (mem_primeWindow.mp hq).2.2.1
      exact mul_le_mul_of_nonneg_left (interval_test_sandwich hinner houter _).2
        (localPrimeFactor_pos (by linarith : (2:ℝ) < q)).le
    _ ≤ 20/(N:ℝ)^(L/10)+20/(N:ℝ)^(L/10) :=
      add_le_add (singleton_mass_le hN hL d lo hA) (singleton_mass_le hN hL d hi hA)
    _ = _ := by ring

/-- A single threshold for every actual endpoint choice. The integral
is over the open interval; endpoint prime atoms have been paid above. -/
theorem compact_uniform_masked_interval {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ lo ∈ Icc (1/6:ℝ) (1/2), ∀ hi ∈ Icc (1/6:ℝ) (1/2),
      ∀ d : ℕ, 0 < d → d ≤ N → ∀ D : Set ℝ,
      Ioo lo hi ⊆ D → D ⊆ Icc lo hi →
      |windowMass N L d D-intervalIntegral lo hi| < epsilon := by
  obtain ⟨Tp,hTp⟩ := compact_uniform_masked_openInterval hmin hmax
    (by positivity : 0 < epsilon/2)
  obtain ⟨Ta,hTa⟩ := compact_multiplier_error (k := 1) hmin hmax
    (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
  have hsmall : Tendsto (fun N : ℕ => 40/(N:ℝ)^(Lmin/10)) atTop (𝓝 0) := by
    have h := (tendsto_nat_log_pow_div_rpow 0 (by positivity : 0 < Lmin/10)).const_mul 40
    simpa only [pow_zero, mul_zero, mul_one_div] using h
  obtain ⟨Te,hTe⟩ := eventually_atTop.mp
    (hsmall.eventually (gt_mem_nhds (by positivity : 0 < epsilon/2)))
  refine ⟨max 2 (max Tp (max Ta Te)), ?_⟩
  intro N hN L hL lo hlo hi hhi d hd hdN D hinner houter
  have hN1 : 1 < N := by omega
  have hL0 := hmin.trans_le hL.1
  have hp := hTp N (by omega) L hL lo hlo hi hhi d hd hdN
  have hA := (hTa N (by omega) L hL).1
  have hs := interval_mass_sandwich hN1 hL0 d hinner houter hA
  have hpow : (N:ℝ)^(Lmin/10) ≤ (N:ℝ)^(L/10) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by linarith [hL.1])
  have hdiv : 40/(N:ℝ)^(L/10) ≤ 40/(N:ℝ)^(Lmin/10) :=
    div_le_div_of_nonneg_left (by norm_num)
      (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _) hpow
  have herror := hs.trans_lt (hdiv.trans_lt (hTe N (by omega)))
  have ht := abs_sub_le (windowMass N L d D)
    (windowMass N L d (Ioo lo hi)) (intervalIntegral lo hi)
  linarith

end
end ImbalancedChen.Part5OriginalH430BuchstabMaskedIntervals
