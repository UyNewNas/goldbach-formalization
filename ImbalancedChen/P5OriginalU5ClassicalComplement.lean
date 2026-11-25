import ImbalancedChen.P5OriginalU5ShortComplement
import ImbalancedChen.P1Full87SharpClassicalCut

/-! At the precision required by H_N, the entire classical prime BV
range is available for the target-deleted U5 mean. Both the proper
modulus-prime correction and the original signed rho are retained. -/
namespace ImbalancedChen.P5OriginalU5ClassicalComplement

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV
open P5OriginalU5ShortComplement (primitive exists_sum_to_branches)
open P5OriginalU5AllMarkHBReserves (branches)
open P4AOriginalFull87EighthPrimeMeanLedger (primeMass densityTest)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)

def classicalPart (B : ℝ) (N : ℕ) (e : ℝ) (P : Policy) :=
  (moduli N e P \ paidModuli N e P).filter (fun q => q ≤ panModulusCutoff N B)

def beyond (B : ℝ) (N : ℕ) (e : ℝ) (P : Policy) :=
  (moduli N e P).filter (fun q => panModulusCutoff N B < q ∧ integerRho N e P q ≠ 0)

theorem actual_classical_partition {B : ℝ} {N : ℕ} (hcap : shortCap N ≤ panModulusCutoff N B)
    (e : ℝ) (P : Policy) :
    remainingPrimitive N e P = (∑ q ∈ classicalPart B N e P, primitive N e P q) +
      ∑ q ∈ beyond B N e P, primitive N e P q := by
  let T := moduli N e P \ paidModuli N e P
  have heq : beyond B N e P =
      T.filter (fun q => panModulusCutoff N B < q ∧ integerRho N e P q ≠ 0) := by
    ext q
    simp only [beyond,T,Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · rintro ⟨hq,hlive,hne⟩
      exact ⟨⟨hq,fun hold => (not_le_of_gt hlive) ((Finset.mem_filter.mp hold).2.1.trans hcap)⟩,
        hlive,hne⟩
    · rintro ⟨⟨hq,_⟩,hlive,hne⟩
      exact ⟨hq,hlive,hne⟩
  rw [heq]
  unfold remainingPrimitive classicalPart
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hsmall : q ≤ panModulusCutoff N B
  · simp [primitive, hsmall, not_lt.mpr hsmall]
  · by_cases hz : integerRho N e P q = 0 <;> simp [primitive, hsmall, lt_of_not_ge hsmall, hz]

theorem exists_full_classical_payment :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      shortCap N ≤ panModulusCutoff N B ∧
      ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy, ∀ S ⊆ moduli N e P,
      (∀ q ∈ S, q ≤ panModulusCutoff N B) →
        |∑ q ∈ S, primitive N e P q| ≤ C*(N : ℝ)/(Real.log (N : ℝ))^3 := by
  obtain ⟨B,hB,C,hC,hsharp⟩ := P1Full87SharpClassicalCut.exists_pan_sharp_payment
  refine ⟨B,hB,C+1,by positivity,?_⟩
  filter_upwards [hsharp, eventually_ge_atTop (2 : ℕ), eventually_one_le_nat_log,
    eventually_powerLog_le_logAccuracy 16 0 2 3 (by norm_num) 1 zero_lt_one]
    with N hsharpN hN hlog herr
  refine ⟨hsharpN.1, ?_⟩
  intro e he he8 P S hS hcap
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hD : panModulusCutoff N B ≤ N := by
    apply Nat.floor_le_of_le
    refine (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.one_le_rpow hlog hB)).trans ?_
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn
      (by norm_num : (1/2 : ℝ) ≤ 1)
  have hdata (q : ℕ) (hq : q ∈ S) := P5OriginalU5AllMarkCosts.full_modulus_data
    hN P (attachment_gates hN he he8).2.2 (hS hq)
  have hsD : S ⊆ Finset.Icc 1 (panModulusCutoff N B) := fun q hq =>
    Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (hdata q hq).1,hcap q hq⟩
  have hsN : S ⊆ Finset.Icc 1 N := fun q hq =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hsD hq)).1,(hcap q hq).trans hD⟩
  let c : ℕ → ℝ := fun q => (integerRho N e P q : ℝ)
  have hcoef (q : ℕ) (hq : q ∈ S) : |c q| ≤ 1 := (hdata q hq).2.1
  have hsp := hsharpN.2 S hsN hsD
    (fun q hq => coprime_of_dvd_sieveProduct (Nat.dvd_of_mem_divisors (hdata q hq).1)) c hcoef
  have hden := P5PrimeDivisorMean.abs_singleton_PP_sub_total_pi_error_le N N S c hsN
    (fun q hq => (sieveProduct_squarefree N N).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (hdata q hq).1)) hcoef
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq, max_eq_right hn] at hden
  have hdiff : |(∑ q ∈ S, primitive N e P q) - ∑ q ∈ S, c q*sharpPrimeError N q| ≤
      4*(1+Real.log (N : ℝ))^2 := by
    simpa only [primitive,c,sharpPrimeError,primeMass,densityTest,mul_one_div] using hden
  have hlogerr : 4*(1+Real.log (N : ℝ))^2 ≤ 1*(N : ℝ)/(Real.log (N : ℝ))^3 := by
    simp only [Real.rpow_zero, mul_one] at herr
    have hh := (sq_le_sq₀ (by linarith : 0 ≤ 1+Real.log (N : ℝ))
      (by linarith : 0 ≤ 2*Real.log (N : ℝ))).mpr (by linarith)
    nlinarith only [hh,herr]
  have ht := abs_add_le ((∑ q ∈ S, primitive N e P q) - ∑ q ∈ S, c q*sharpPrimeError N q)
    (∑ q ∈ S, c q*sharpPrimeError N q)
  rw [sub_add_cancel] at ht
  exact ht.trans ((add_le_add (hdiff.trans hlogerr) hsp).trans_eq (by ring))

/-- End-to-end classical cutoff in the actual projected U5 count. All
q above the cutoff survive if their original signed integer rho is nonzero. -/
theorem exists_original_count_beyond_classical (t tau : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (htau : t < tau) (K : ℕ)
    {eta eMax : ℝ} (heta : 0 < eta) (hMax : 0 < eMax) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, 0 < e ∧ e < 1/8 ∧ e < eMax ∧
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → Even N → ∀ P : Policy, ∀ zeta : ℝ,
        fullProjectedMainSum N P - projectionReserve N eta +
          (branches t tau zeta 6 N K e P (beyond B N e P)).re -
          C*(N : ℝ)/(Real.log (N : ℝ))^3 ≤ currentChenUpsilon5 N := by
  obtain ⟨B,hB,C,hC,hcut⟩ := exists_full_classical_payment
  obtain ⟨D,hD,e,he,he8,hMax',M,hM,hlower⟩ :=
    P5OriginalU5AllMarkCosts.exists_original_count_paid 3 heta hMax
  obtain ⟨G,hG,hbranches⟩ := exists_sum_to_branches t tau ht ht1 htau K 3
  have hboth := hcut.and hbranches
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hboth
  refine ⟨B,hB,C+D+G,by positivity,e,he,he8,hMax',max M J,hM.trans (le_max_left _ _),?_⟩
  intro N hN hev P zeta
  obtain ⟨hpay,hbranch⟩ := hJ N ((le_max_right _ _).trans hN)
  have hc := hlower N ((le_max_left _ _).trans hN) hev P
  rw [actual_classical_partition hpay.1] at hc
  have hshort := (abs_le.mp (hpay.2 e he he8 P (classicalPart B N e P)
    (fun q hq => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).1)
    (fun q hq => (Finset.mem_filter.mp hq).2))).1
  have hlong := hbranch hev e he he8 P (beyond B N e P) (Finset.filter_subset _ _) zeta
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans hlong)).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hh
  have hscale : (C+D+G)*(N : ℝ)/(Real.log (N : ℝ))^3 =
      C*(N : ℝ)/(Real.log (N : ℝ))^3 + D*(N : ℝ)/(Real.log (N : ℝ))^3 +
      G*(N : ℝ)/(Real.log (N : ℝ))^3 := by ring
  rw [hscale]
  linarith only [hc,hshort,hh]

end
end ImbalancedChen.P5OriginalU5ClassicalComplement
