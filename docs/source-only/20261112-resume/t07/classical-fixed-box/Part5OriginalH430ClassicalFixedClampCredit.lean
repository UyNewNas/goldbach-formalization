import ImbalancedChen.Part5OriginalH430ClassicalFixedClampSeedPrice

/-! The fixed-box normalized price goes back to its actual E_p+S_p budget
on the whole original clamp. The tested geometric multiset is still on
the right; its original same-coefficient positive estimate is separate. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampCredit
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open Part5UpperTables.OriginalU34 (clampStart)
open P2SeedOmegaLiteralFibre (K)
open P2SeedOmegaLiteralFunctional (switchCost)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430ClassicalRootCredits (cubeCredit)
open Part5OriginalH430ClassicalBadPairCredit (otherSeedTerms badPrice)
open Part5OriginalH430SeedThirteenPrimeWords (longPrime)
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight allLarge)
open Part5OriginalH430ClassicalClampLongCredit (original_E_and_S_after_small_switches)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum)
open Part5OriginalH430ClassicalFixedClampMarks
open Part5OriginalH430ClassicalFixedClampSeedPrice
open scoped Classical Topology BigOperators

private theorem untested_nonneg (N : ℕ) (ν κ : ℝ) : 0≤count false 1 N ν κ := by
  apply sum_nonneg
  intro j _
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
    exact sum_nonneg (fun u _ => by simp [testWeight]))

theorem J_nonneg {ν : ℝ} (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) : 0≤J ν := by
  by_contra! h
  have he : 0< -(J ν)/2 := by linarith
  have hb := geometric_raw_J (κ:=1/112) hν hν' le_rfl he
  obtain ⟨N,hN,hp⟩ := (hb.and (eventually_gt_atTop (1:ℕ))).exists
  have hscale : 0≤(log (N:ℝ)/(N:ℝ)) := div_nonneg
    (log_nonneg (by exact_mod_cast hp.le)) (Nat.cast_nonneg _)
  have hu := mul_nonneg hscale (untested_nonneg N ν (1/112))
  linarith only [hu,hN,h]

/-- Literal J form of the original integer-mass hypothesis. -/
theorem actual_untested_upper {ν κ ε : ℝ} (hν : 1/3+7/128≤ν) (hν' : ν≤1/2)
    (hk : κ≤1/112) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,count false 1 N ν κ≤(J ν+ε)*((N:ℝ)/log (N:ℝ)) := by
  filter_upwards [geometric_raw_J hν hν' hk he,eventually_gt_atTop (1:ℕ)] with N hb hN
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hh := mul_le_mul_of_nonneg_right hb (div_nonneg h0.le hlog.le)
  convert hh using 1 <;> field_simp [h0.ne',hlog.ne'] <;> ring

/-- The global theorem's actual K0 times J, and a positive absolute
H_N tolerance, fit the seed's ORIGINAL K/4 and the actual clamp Theta.
The tolerance is chosen before N. -/
theorem paper_upper_price_fits {n : ℕ} {τ ε : ℝ} (ht : 0≤τ) (ht' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (he : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ N : ℕ in atTop,
      ((8452171/1250000)*J (clampLevel n τ)+δ)*singularNormalization N≤
        switchCost*clampMass N n τ+ε*clampMass N n τ := by
  let ν := clampLevel n τ
  let I := intervalMass clampStart (1/3) ν
  obtain ⟨hν,hν'⟩ := frozen_bounds ht ht' hn
  have hJ := J_nonneg hν hν'
  have hI : 0<I := intervalMass_positive (by norm_num [clampStart])
    (by norm_num [clampStart]) (by dsimp [ν]; linarith only [hν])
  have hk := mul_le_mul_of_nonneg_right (by norm_num [K] : (8452171/1250000:ℝ)≤K) hJ
  let δ := ε*I/2
  have hd : 0<δ := half_pos (mul_pos he hI)
  have hlim := ((original_price_common_limit (κ:=1/112) ht ht' hn le_rfl he).2).add
    ((actual_clamp_theta_limit ht ht' hn).const_mul ε)
  have hlt : (8452171/1250000)*J ν+δ<K*J ν+ε*I := by
    dsimp only [δ]
    linarith only [hk,mul_pos he hI]
  refine ⟨δ,hd,?_⟩
  filter_upwards [hlim.eventually (lt_mem_nhds hlt),eventually_singularNormalization_pos] with N hh hS
  change _<switchCost*clampMass N n τ/singularNormalization N+
    ε*(clampMass N n τ/singularNormalization N) at hh
  rw [←mul_div_assoc,←add_div] at hh
  exact ((lt_div_iff₀ hS).mp hh).le

/-- The actual positive count in the directed seed balance is bounded
by the genuine sharp fixed-family tested weight, retaining every Γ mark. -/
theorem original_balance_at_sharp_family {τ κ ε : ℝ} (ht : 0<τ) (ht' : τ≤1/12)
    (hk : 0<κ) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,1/((n:ℝ)+1)≤11/384 →
      5*(clampMass N n τ-∑ p∈clampPrimes N,cubeCredit N n p τ)≤
        (∑ p∈clampPrimes N,let Q:=rootQ N n .U3 τ p
          (otherSeedTerms N p Q-longPrime N Q p)+badPrice N p Q)+
          count true 1 N (clampLevel n τ) κ+ε*clampMass N n τ := by
  filter_upwards [original_E_and_S_after_small_switches ht ht' hk he,eventually_gt_atTop (1:ℕ)]
    with N hpaid hN
  intro hEven n hn
  have hh := hpaid hEven n hn
  let A := fun p => let Q:=rootQ N n .U3 τ p
    (otherSeedTerms N p Q-longPrime N Q p)+badPrice N p Q
  let L := fun p => allLarge true N (rootQ N n .U3 τ p) p (smallProduct N κ)
  have hsum : (∑ p∈clampPrimes N,A p+L p)=
      (∑ p∈clampPrimes N,A p)+∑ p∈clampPrimes N,L p := sum_add_distrib
  change _≤(∑ p∈clampPrimes N,A p+L p)+ε*clampMass N n τ at hh
  rw [hsum] at hh
  have h := original_le_geometry N (clampLevel n τ) κ true
  rw [original_count hN ht.le ht' true κ] at h
  change (∑ p∈clampPrimes N,L p)≤_ at h
  change _≤(∑ p∈clampPrimes N,A p)+count true 1 N (clampLevel n τ) κ+ε*clampMass N n τ
  linarith only [h,hh]

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampCredit
