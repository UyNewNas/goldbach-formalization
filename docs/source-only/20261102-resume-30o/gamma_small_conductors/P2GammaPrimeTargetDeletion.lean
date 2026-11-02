import ImbalancedChen.P2GammaPrimeCharacterSW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Target deletion is a bounded number of large distinct prime divisors.
The moving target never appears in a tau multiplier. This file retains
the separate auxiliary k gate in every transformed row.
-/

namespace ImbalancedChen.P2GammaPrimeTargetDeletion
noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open P2GammaPrimeCharacterSW
open Part3.MellinPrimeIntervalSW20261026b
open Part3.PrimeMellinProfileVariation20261026b
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def targetDeleted (T : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n.Coprime T then a n else 0

def targetPrimeSet (S : Finset ℕ) (T : ℕ) : Finset ℕ :=
  S.filter (fun p => p.Prime ∧ p ∣ T)

/-- A finite product proof pays all target prime deletions simultaneously. -/
theorem target_prime_card_log_bound (S : Finset ℕ) {T : ℕ} (hT : 0 < T)
    {M : ℝ} (hM : 1 < M) (hlarge : ∀ p ∈ targetPrimeSet S T, M ≤ (p : ℝ)) :
    ((targetPrimeSet S T).card : ℝ)*Real.log M ≤ Real.log (T : ℝ) := by
  let P := targetPrimeSet S T
  have hsub : P ⊆ T.primeFactors := by
    intro p hp
    obtain ⟨hpS,hprime,hdvd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime,hdvd,hT.ne'⟩
  have hprodDVD : (∏ p ∈ P, p) ∣ T :=
    (Finset.prod_dvd_prod_of_subset P T.primeFactors id hsub).trans
      (Nat.prod_primeFactors_dvd T)
  have hprod : M^P.card ≤ (T : ℝ) := by
    calc
      _ = ∏ _p ∈ P, M := (Finset.prod_const M).symm
      _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod
        (fun p hp => (zero_lt_one.trans hM).le) hlarge
      _ = ((∏ p ∈ P, p : ℕ) : ℝ) := by simp only [Nat.cast_prod]
      _ ≤ (T : ℝ) := by exact_mod_cast Nat.le_of_dvd hT hprodDVD
  have hlog := Real.log_le_log (pow_pos (zero_lt_one.trans hM) P.card) hprod
  simpa only [Real.log_pow,P] using hlog

theorem interval_prime_real_bounds {M u v : ℝ} (hM : 1 ≤ M)
    (hlo : M ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*M)
    {p : ℕ} (hp : p ∈ primeSWInterval u v) :
    M ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*M := by
  obtain ⟨hpLo,hpHi⟩ := Finset.mem_Ioc.mp hp
  have hu0 : 0 ≤ u := by linarith
  have hpReal : u < (p : ℝ) := (Nat.floor_lt hu0).mp hpLo
  have hv0 : 0 ≤ v := by linarith
  exact ⟨hlo.trans hpReal.le,
    ((show (p : ℝ) ≤ (Nat.floor v : ℝ) by exact_mod_cast hpHi).trans
      (Nat.floor_le hv0)).trans hhi⟩

/-- The target may vary with the chart; the constant Ctarget/eta is fixed. -/
theorem target_prime_card_completeScale {eta Ctarget x M u v : ℝ}
    (heta : 0 < eta) (hx : 1 < x) (hpower : x^eta ≤ M)
    (hlo : M ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*M) {T : ℕ} (hT : 0 < T)
    (hTarget : (T : ℝ) ≤ x^Ctarget) :
    ((targetPrimeSet (primeSWInterval u v) T).card : ℝ) ≤ Ctarget/eta := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hxp : 1 < x^eta := Real.one_lt_rpow hx heta
  have hM : 1 < M := hxp.trans_le hpower
  have hlogM : eta*Real.log x ≤ Real.log M := by
    rw [← Real.log_rpow hx0 eta]
    exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hpower
  have hcount := target_prime_card_log_bound (primeSWInterval u v) hT hM
    (fun p hp => (interval_prime_real_bounds hM.le hlo huv hhi
      (Finset.mem_filter.mp hp).1).1)
  have htargetLog : Real.log (T : ℝ) ≤ Ctarget*Real.log x := by
    calc
      _ ≤ Real.log (x^Ctarget) := Real.log_le_log (by exact_mod_cast hT) hTarget
      _ = _ := Real.log_rpow hx0 Ctarget
  have hcount0 : (0 : ℝ) ≤ (targetPrimeSet (primeSWInterval u v) T).card :=
    Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlogM hcount0
  apply (le_div_iff₀ heta).mpr
  apply (mul_le_mul_right hlogx).mp
  nlinarith only [hcount,htargetLog,hmul]

/-- Finite transform deletion, with no analytic estimate as a premise. -/
theorem rowTransform_target_deletion_le (S : Finset ℕ) (a : ℕ → ℂ)
    (T k r : ℕ) (psi : DirichletCharacter ℂ r) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ n ∈ S, ‖a n‖ ≤ H)
    (hprime : ∀ n ∈ S, ¬n.Prime → a n = 0) :
    ‖rowTransform S (targetDeleted T a) k r psi-rowTransform S a k r psi‖ ≤
      H*((targetPrimeSet S T).card : ℝ) := by
  unfold rowTransform
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S,
      ‖(if n.Coprime k then targetDeleted T a n else 0)*psi (n : ZMod r)-
        (if n.Coprime k then a n else 0)*psi (n : ZMod r)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, if n.Prime ∧ n ∣ T then H else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · by_cases hd : n ∣ T
        · have hc : ¬n.Coprime T := fun hc => (hp.coprime_iff_not_dvd.mp hc) hd
          simp only [hp,hd,and_self,if_true,targetDeleted,if_neg hc]
          by_cases hk : n.Coprime k
          · simp only [hk,if_true,zero_mul,zero_sub,norm_neg,norm_mul]
            exact (mul_le_of_le_one_right (norm_nonneg _) (psi.norm_le_one _)).trans
              (hbound n hn)
          · simp only [hk,if_false,zero_mul,sub_self,norm_zero]
            exact hH
        · have hc : n.Coprime T := hp.coprime_iff_not_dvd.mpr hd
          simp only [hp,hd,and_false,if_false,targetDeleted,if_pos hc,sub_self,norm_zero]
      · simp only [hprime n hn hp,targetDeleted,ite_self,zero_mul,sub_self,norm_zero,
          hp,false_and,if_false]
    _ = _ := by rw [← Finset.sum_filter]; simp [targetPrimeSet,mul_comm]

/-- Literal Mellin profile bound, uniform in its frequency and interval. -/
theorem mellin_coefficient_norm_le {Phi : ℝ → ℝ} {H M u v : ℝ}
    (hPhi : ∀ y ∈ Set.Icc (1 : ℝ) 2, |Phi y| ≤ H)
    (hM : 1 ≤ M) (hlo : M ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*M) (t : ℝ)
    {n : ℕ} (hn : n ∈ primeSWInterval u v) :
    ‖mellinPrimeCoefficient Phi t M n‖ ≤ H := by
  have hM0 : 0 < M := by linarith
  obtain ⟨hnlo,hnhi⟩ := interval_prime_real_bounds hM hlo huv hhi hn
  have hnormalized : (n : ℝ)/M ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hM0).mpr (by linarith),(div_le_iff₀ hM0).mpr hnhi⟩
  by_cases hp : n.Prime
  · simpa only [mellinPrimeCoefficient,physicalProfile,profile,norm_mul,phase_norm,
      primeSWBeta,hp,if_true,Complex.ofReal_one,norm_one,mul_one,
      Complex.norm_real,Real.norm_eq_abs] using hPhi _ hnormalized
  · simp [mellinPrimeCoefficient,primeSWBeta,hp]
    exact (abs_nonneg (Phi 1)).trans (hPhi 1 ⟨le_rfl,by norm_num⟩)

/-- A target-deleted actual prime row has the same fixed auxiliary divisor
order one. Constants and the complete-scale threshold precede the target,
subinterval, Mellin mode and both arithmetic moduli. -/
theorem targetDeleted_mellin_prime_character_completeScale
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {eta J A Ctarget : ℝ} (heta : 0 < eta) (hJ : 0 ≤ J)
    (hCtarget : 0 ≤ Ctarget) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M u v : ℝ, x0 ≤ x → x^eta ≤ M →
      1 ≤ M → M ≤ u → u ≤ v → v ≤ 2*M →
      ∀ t : ℝ, |t| ≤ Real.log x^J →
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ x^Ctarget →
      ∀ k r : ℕ, 0 < k → 0 < r → ∀ psi : DirichletCharacter ℂ r,
      psi ≠ 1 →
      ‖rowTransform (primeSWInterval u v)
          (targetDeleted T (mellinPrimeCoefficient Phi t M)) k r psi‖ ≤
        (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A) := by
  obtain ⟨H0,hH0⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous.continuousOn
  let H : ℝ := max H0 1
  have hH : 0 ≤ H := zero_le_one.trans (le_max_right _ _)
  have hProfile (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) : |Phi y| ≤ H :=
    by
      have hh : |Phi y| ≤ H0 := by simpa only [Real.norm_eq_abs] using hH0 y hy
      exact hh.trans (le_max_left _ _)
  obtain ⟨C,hC,x1,hx1,hraw⟩ := mellin_prime_character_completeScale Phi hPhi heta hJ
    (A := A)
  have hpay : ∀ᶠ x : ℝ in atTop, Real.log x^A ≤ x^eta := by
    have hb := (isLittleO_log_rpow_rpow_atTop A heta).bound (by norm_num : (0:ℝ)<1)
    filter_upwards [hb,eventually_ge_atTop (1 : ℝ)] with x hx hxge
    simpa only [Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hxge) A),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hxge) eta)] using hx
  obtain ⟨x2,hx2⟩ := eventually_atTop.mp hpay
  let K : ℝ := H*Ctarget/eta
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hH hCtarget) heta.le
  refine ⟨C+K,add_pos_of_pos_of_nonneg hC hK,max x1 x2,
    hx1.trans_le (le_max_left _ _),?_⟩
  intro x M u v hx hpower hM hlo huv hhi t ht T hT hTarget k r hk hr psi hpsi
  have hxx1 : x1 ≤ x := (le_max_left _ _).trans hx
  have hxgt : 1 < x := hx1.trans_le hxx1
  have hL : 0 < Real.log x := Real.log_pos hxgt
  have hden : 0 < Real.log x^A := Real.rpow_pos_of_pos hL _
  have hrawBound := hraw x M u v hxx1 hpower hM hlo huv hhi t ht k r hk hr psi hpsi
  have hcard := target_prime_card_completeScale heta hxgt hpower hlo huv hhi hT hTarget
  have hdeletion := rowTransform_target_deletion_le (primeSWInterval u v)
    (mellinPrimeCoefficient Phi t M) T k r psi hH
    (fun n hn => mellin_coefficient_norm_le hProfile hM hlo huv hhi t hn)
    (fun n hn hp => by simp [mellinPrimeCoefficient,primeSWBeta,hp])
  have hsmall :
      ‖rowTransform (primeSWInterval u v) (targetDeleted T (mellinPrimeCoefficient Phi t M)) k r psi-
        rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi‖ ≤ K :=
    hdeletion.trans (by dsimp only [K];
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hcard hH)
  have htau : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr
      ⟨1,Nat.mem_divisors.mpr ⟨one_dvd k,hk.ne'⟩⟩
  have hphi : (1 : ℝ) ≤ (r.totient : ℝ) := by
    have hn : 1 ≤ r.totient := Nat.totient_pos.mpr hr
    exact_mod_cast hn
  have hlogPay : Real.log x^A ≤ M :=
    (hx2 x ((le_max_right _ _).trans hx)).trans hpower
  have hunit : 1 ≤ (r.totient : ℝ)*(M*(k.divisors.card : ℝ)/Real.log x^A) := by
    have hM0 : 0 ≤ M := by linarith
    have hprod : Real.log x^A ≤ M*(k.divisors.card : ℝ) :=
      hlogPay.trans (le_mul_of_one_le_right hM0 htau)
    have hquot : 1 ≤ M*(k.divisors.card : ℝ)/Real.log x^A := (one_le_div hden).mpr hprod
    exact hquot.trans (le_mul_of_one_le_left (by positivity) hphi)
  calc
    _ = ‖rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi+
      (rowTransform (primeSWInterval u v) (targetDeleted T (mellinPrimeCoefficient Phi t M)) k r psi-
        rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi)‖ := by
      congr 1
      ring
    _ ≤ ‖rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi‖+
      ‖rowTransform (primeSWInterval u v) (targetDeleted T (mellinPrimeCoefficient Phi t M)) k r psi-
        rowTransform (primeSWInterval u v) (mellinPrimeCoefficient Phi t M) k r psi‖ := norm_add_le _ _
    _ ≤ (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A)+K :=
      add_le_add hrawBound hsmall
    _ ≤ (r.totient : ℝ)*(C*M*(k.divisors.card : ℝ)/Real.log x^A)+
      K*((r.totient : ℝ)*(M*(k.divisors.card : ℝ)/Real.log x^A)) :=
      add_le_add_left (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hK) _
    _ = _ := by ring

end
end ImbalancedChen.P2GammaPrimeTargetDeletion
