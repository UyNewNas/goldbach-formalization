import ImbalancedChen.P5OriginalSingletonPrimeSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine k=1 SW for the literal singleton gamma. The only analytic
distribution input is the pinned theorem on primeSWBeta, as already used
by Part3MellinPrimeIntervalSW. Deleting the original primes dividing N
costs O_Phi(log N), not tau(N) times the SW main bound. A positive original
prime exponent pays this loss uniformly. Mellin frequencies cost 1+|t|.
-/

namespace ImbalancedChen.P5Z.OriginalSingletonPrimeSW
noncomputable section
open Classical Finset Filter Set
open scoped BigOperators Topology
open ImbalancedChen ImbalancedChen.Part3
open OriginalSingletonPrimeSource
open PrimeMellinProfileVariation20261026b MellinPrimeIntervalSW20261026b
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem prime_deleted_profile_mass {N : ℕ} (hN : 0 < N)
    (Phi : ℝ → ℝ) {M U u v : ℝ}
    (hM : ∀ y ∈ Icc (1 : ℝ) 2, |Phi y| ≤ M)
    (hM0 : 0 ≤ M) (hU : 1 ≤ U) (hlo : U ≤ u) (hhi : v ≤ 2*U)
    (t : ℝ) :
    (∑ p ∈ primeSWInterval u v with ¬p.Coprime N,
      ‖mellinPrimeCoefficient Phi t U p‖) ≤
        M * (N.primeFactors.card : ℝ) := by
  let S := (primeSWInterval u v).filter (fun p => p.Prime ∧ ¬p.Coprime N)
  have he : (∑ p ∈ primeSWInterval u v with ¬p.Coprime N,
      ‖mellinPrimeCoefficient Phi t U p‖) =
      ∑ p ∈ S, ‖mellinPrimeCoefficient Phi t U p‖ := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hp' : p.Prime <;> by_cases hc : p.Coprime N <;>
      simp [hp',hc,mellinPrimeCoefficient,primeSWBeta]
  have hbound : ∀ p ∈ S, ‖mellinPrimeCoefficient Phi t U p‖ ≤ M := by
    intro p hp
    obtain ⟨hp,hprime,hcop⟩ := Finset.mem_filter.mp hp
    have hu0 : 0 ≤ u := by linarith
    have hpU : U < (p : ℝ) := hlo.trans_lt ((Nat.floor_lt hu0).mp
      (Finset.mem_Ioc.mp hp).1)
    have hv0 : 0 ≤ v := by
      by_contra hv
      have hv' : Nat.floor v = 0 := Nat.floor_of_nonpos (le_of_not_ge hv)
      have := (Finset.mem_Ioc.mp hp).2
      rw [hv'] at this
      have := hprime.two_le
      omega
    have hp2 : (p : ℝ) ≤ 2*U :=
      ((show (p : ℝ) ≤ (Nat.floor v : ℝ) by
        exact_mod_cast (Finset.mem_Ioc.mp hp).2).trans (Nat.floor_le hv0)).trans hhi
    have hUn : 0 < U := by linarith
    have hn : (p : ℝ)/U ∈ Icc (1 : ℝ) 2 :=
      ⟨(le_div_iff₀ hUn).mpr (by linarith),
        (div_le_iff₀ hUn).mpr hp2⟩
    simpa only [mellinPrimeCoefficient,primeSWBeta,if_pos hprime,
      Complex.ofReal_one,mul_one,physicalProfile,profile,norm_mul,phase_norm,
      mul_one,Complex.norm_real,Real.norm_eq_abs] using hM _ hn
  rw [he]
  calc
    _ ≤ ∑ _p ∈ S, M := Finset.sum_le_sum hbound
    _ = M * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ M * (N.primeFactors.card : ℝ) := mul_le_mul_of_nonneg_left
      (by exact_mod_cast primeSW_deleted_card_le (primeSWInterval u v) hN.ne') hM0

/-- Explicit finite source estimate, with the real exclusion cost visible.
No SW hypothesis for the source coefficient occurs. -/
theorem singleton_profile_finite_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ y ∈ Icc (1 : ℝ) 2, |Phi y| ≤ M)
    (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N m : ℕ, 1 < N → ∀ i : Fin (m+1),
      ∀ U : ℝ, 1 ≤ U → ∀ t : ℝ, ∀ q b : ℕ, 0 < q → b.Coprime q →
      ‖auxiliarySWError (source N m i U) (coefficient N m [i] Phi t U) 1 q b‖ ≤
        C*(1+|t|)*U/Real.log (2*U)^B +
          2*M*(Real.log (N : ℝ)/Real.log 2) := by
  obtain ⟨C,hC,hSW⟩ := mellin_prime_interval_SW Phi hPhi B
  refine ⟨C,hC,?_⟩
  intro N m hN i U hU t q b hq hb
  by_cases hs : (source N m i U).Nonempty
  · obtain ⟨hlo,huv,hhi⟩ := source_nonempty_geometry hN i hU hs
    rw [source_error_eq_prime hN i hU hs]
    have hplain := hSW U (clipLo N m i U) (clipHi N m i U)
      hU hlo huv hhi t 1 q b (by norm_num) hq hb
    have hdelete := auxiliarySWError_sub_one_norm_le_bad_mass
      (primeSWInterval (clipLo N m i U) (clipHi N m i U))
      (mellinPrimeCoefficient Phi t U) N q b hq
    have hmass := prime_deleted_profile_mass (show 0 < N by omega)
      Phi hM hM0 hU hlo hhi t
    have hcard := chen_primeFactors_card_le_log (show 0 < N by omega)
    have htotal := norm_add_le
      (auxiliarySWError (primeSWInterval (clipLo N m i U) (clipHi N m i U))
        (mellinPrimeCoefficient Phi t U) N q b -
       auxiliarySWError (primeSWInterval (clipLo N m i U) (clipHi N m i U))
        (mellinPrimeCoefficient Phi t U) 1 q b)
      (auxiliarySWError (primeSWInterval (clipLo N m i U) (clipHi N m i U))
        (mellinPrimeCoefficient Phi t U) 1 q b)
    rw [sub_add_cancel] at htotal
    have hpaid := mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ 2*M)
    have htau : fouvryTau 2 1 = 1 := by simp [fouvryTau_two]
    simp only [htau,Nat.cast_one,mul_one] at hplain
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [auxiliarySWError,Finset.sum_empty,zero_div,sub_zero,norm_zero]
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
    have hlog := Real.log_nonneg hn
    positivity

/-- Power-small payment of precisely the deleted original primes. The
threshold precedes every dyadic U and all arithmetic data. -/
theorem eventually_exclusion_payment (M a : ℝ) (ha : 0 < a) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ U : ℝ, (N : ℝ)^a ≤ 2*U →
      2*M*(Real.log (N : ℝ)/Real.log 2) ≤ U/Real.log (N : ℝ)^A := by
  have hlim : Tendsto (fun N : ℕ =>
      (4*M/Real.log 2)*(Real.log (N : ℝ)^(A+1)/(N : ℝ)^a)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_nat_log_pow_div_rpow (A+1) ha).const_mul
      (4*M/Real.log 2)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)] with N hsmall hlog hN
  intro U hU
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlp : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hpow : 0 < (N : ℝ)^a := Real.rpow_pos_of_pos hNp a
  have hpay : (4*M/Real.log 2)*Real.log (N : ℝ)^(A+1) ≤ (N : ℝ)^a := by
    exact ((div_lt_one hpow).mp (by simpa only [mul_div_assoc] using hsmall)).le
  apply (le_div_iff₀ (pow_pos hlp A)).mpr
  rw [pow_succ] at hpay
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have he : 2*(2*M*(Real.log (N : ℝ)/Real.log 2)*Real.log (N : ℝ)^A) =
      (4*M/Real.log 2)*(Real.log (N : ℝ)^A*Real.log (N : ℝ)) := by ring
  linarith

/-- Original-N normalized prime SW, including arbitrary fixed logarithmic
Mellin bandwidth. This is k=1 for the masked SOURCE, not auxiliary removal
asserted to be SW. Only the actual prime distribution supplier is used. -/
theorem singleton_profile_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {a : ℝ} (ha : 0 < a) (A L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, ∀ i : Fin (m+1),
      ∀ U : ℝ, 1 ≤ U → (N : ℝ)^a ≤ 2*U →
      ∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^L →
      ∀ q b : ℕ, 0 < q → b.Coprime q →
      ‖auxiliarySWError (source N m i U) (coefficient N m [i] Phi t U) 1 q b‖ ≤
        C*U/Real.log (N : ℝ)^A := by
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous.continuousOn
  let M := max M0 1
  have hM0' : 0 ≤ M := le_trans (by norm_num) (le_max_right _ _)
  have hM : ∀ y ∈ Icc (1 : ℝ) 2, |Phi y| ≤ M := by
    intro y hy
    have hh : |Phi y| ≤ M0 := by simpa only [Real.norm_eq_abs] using hM0 y hy
    exact hh.trans (le_max_left _ _)
  obtain ⟨C,hC,hSW⟩ := singleton_profile_finite_SW Phi hPhi M hM0' hM (A+L)
  refine ⟨2*C/a^(A+L)+1,by positivity,?_⟩
  filter_upwards [eventually_exclusion_payment M a ha A,eventually_one_le_nat_log,
    eventually_ge_atTop (2 : ℕ)] with N hpay hlog hN
  intro m i U hU hpower t ht q b hq hb
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlp : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hUp : 0 < U := by linarith
  have hlogU : 0 < Real.log (2*U) := Real.log_pos (by linarith)
  have hcomp : a*Real.log (N : ℝ) ≤ Real.log (2*U) := by
    rw [← Real.log_rpow hNp]
    exact Real.log_le_log (Real.rpow_pos_of_pos hNp a) hpower
  have hden : a^(A+L)*Real.log (N : ℝ)^(A+L) ≤ Real.log (2*U)^(A+L) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg ha.le hlp.le) hcomp _
  have hfreq : 1+|t| ≤ 2*Real.log (N : ℝ)^L := by
    have hh : 1 ≤ Real.log (N : ℝ)^L := one_le_pow₀ hlog
    linarith
  have hraw := hSW N m (by omega) i U hU t q b hq hb
  have hmain : C*(1+|t|)*U/Real.log (2*U)^(A+L) ≤
      (2*C/a^(A+L))*U/Real.log (N : ℝ)^A := by
    calc
      _ ≤ C*(2*Real.log (N : ℝ)^L)*U/Real.log (2*U)^(A+L) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfreq hC.le) hUp.le) (by positivity)
      _ ≤ C*(2*Real.log (N : ℝ)^L)*U/
          (a^(A+L)*Real.log (N : ℝ)^(A+L)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by
        simp only [pow_add]
        field_simp [(pow_pos ha A).ne',(pow_pos ha L).ne',
          (pow_pos hlp A).ne',(pow_pos hlp L).ne']
        <;> ring
  have hcorr := hpay U hpower
  have he : (2*C/a^(A+L)+1)*U/Real.log (N : ℝ)^A =
      (2*C/a^(A+L))*U/Real.log (N : ℝ)^A + U/Real.log (N : ℝ)^A := by ring
  rw [he]
  exact hraw.trans (add_le_add hmain hcorr)

end
end ImbalancedChen.P5Z.OriginalSingletonPrimeSW
