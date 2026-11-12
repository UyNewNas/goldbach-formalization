import ImbalancedChen.Part5OriginalH430ClassicalSmoothPositiveSieve
import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.P5zMarkedPrimeFamilyCorrections

/-! The whole displayed modulus set divides the actual sieve primorial.
Use its Mertens bound, including displayed zero coefficients. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothPrimorialEnvelope
noncomputable section
open Finset Real
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)
open P4AOriginalFull87RawChronology (cutoff)
open P4BPrimorialDivisorEnvelope (exists_sievePrimorial_divisor_mass_le_log
  prime_divisible_reciprocalTotient_le_divisor_mass)
open scoped Classical BigOperators

theorem prime_divisor_cost :
    ∃ C : ℝ, 0<C ∧ ∀ {N : ℕ}, 2≤N → Even N → ∀ (w : ℝ), w≤cutoff N →
      ∀ {p : ℕ},p.Prime → ∀ {H : ℝ},0<H → H≤(p:ℝ) →
        (∑ d∈moduli N w,if p∣d then 1/(d.totient:ℝ) else 0)≤
          (2/H)*(C*log (N:ℝ)) := by
  obtain ⟨C,hC,hmass⟩ := exists_sievePrimorial_divisor_mass_le_log
  refine ⟨C,hC,?_⟩
  intro N hN heven w hw p hp H hH hpH
  let Z : ℕ := Nat.ceil (cutoff N)
  let M := sieveProduct N Z
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hv : (1:ℝ)<cutoff N := one_lt_rpow hNr (by norm_num : (0:ℝ)<19/96)
  have hZ : 2≤Z := Nat.add_one_le_ceil_iff.mpr hv
  have hzN : cutoff N≤(N:ℝ) := by
    calc
      _ ≤ (N:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (19/96:ℝ)≤1)
      _ = _ := rpow_one _
  have hZN : Z≤N := Nat.ceil_le.mpr hzN
  have hM : M≠0 := (sieveProduct_squarefree N Z).ne_zero
  have hsub : moduli N w⊆M.divisors := fun _ hd => Nat.mem_divisors.mpr
    ⟨compiled_modulus_dvd N w hw hd,hM⟩
  have hprim := prime_divisible_reciprocalTotient_le_divisor_mass M hM (moduli N w) hsub p hp
  have hlog := log_le_log (by exact_mod_cast (show 0<Z by omega)) (by exact_mod_cast hZN)
  have hm := (hmass N Z heven (by exact_mod_cast hZ)).trans (mul_le_mul_of_nonneg_left hlog hC.le)
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hhalf : H/2≤(p:ℝ)-1 := by linarith only [hpH,hp2]
  have hInv : 1/((p:ℝ)-1)≤2/H := by
    calc
      _ ≤ 1/(H/2) := one_div_le_one_div_of_le (half_pos hH) hhalf
      _ = _ := by field_simp [hH.ne']
  exact hprim.trans (mul_le_mul hInv hm (sum_nonneg (fun _ _ => by positivity))
    (div_nonneg (by norm_num) hH.le))

/-- Count every prime slot, with its original multiplicity. The estimate is
uniform in the true retention and beta parameters because the sole amplitude
used here is the original tagged beta unit bound. -/
theorem tuple_divisor_cost {k P : ℕ} (t : Fin k → Fin (P+1))
    (ht : t∈Part3.labelledPrimeTuples k P) (D : Finset ℕ) (ρ : ℕ → ℝ)
    (hrho : ∀d∈D,|ρ d|≤1) {U : ℝ}
    (hslot : ∀i, (∑ d∈D,if (t i).val∣d then 1/(d.totient:ℝ) else 0)≤U) :
    (∑ d∈D,if Nat.Coprime (Part3.labelledProduct t) d then 0 else |ρ d|/(d.totient:ℝ))≤
      (k:ℝ)*U := by
  have hp := (mem_filter.mp ht).2
  have hpoint (d : ℕ) (hd : d∈D) :
      (if Nat.Coprime (Part3.labelledProduct t) d then 0 else |ρ d|/(d.totient:ℝ))≤
        ∑ i : Fin k,if (t i).val∣d then 1/(d.totient:ℝ) else 0 := by
    by_cases hc : Nat.Coprime (Part3.labelledProduct t) d
    · rw [if_pos hc]
      exact sum_nonneg (fun _ _ => by positivity)
    · have hex : ∃ i : Fin k,¬Nat.Coprime (t i).val d := by
        by_contra! hall
        exact hc (Nat.coprime_prod_left_iff.mpr (fun i _ => hall i))
      obtain ⟨i,hi⟩ := hex
      have hdiv : (t i).val∣d := by
        by_contra hno
        exact hi ((hp i).coprime_iff_not_dvd.mpr hno)
      have hone := single_le_sum
        (fun j (_ : j∈(univ : Finset (Fin k))) =>
          show (0:ℝ)≤(if (t j).val∣d then 1/(d.totient:ℝ) else 0) by positivity)
        (mem_univ i)
      rw [if_pos hdiv] at hone
      rw [if_neg hc]
      exact (div_le_div_of_nonneg_right (hrho d hd) (Nat.cast_nonneg _)).trans hone
  have h := sum_le_sum (s:=D) hpoint
  rw [sum_comm] at h
  exact h.trans (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
    sum_le_sum (s:=univ) (fun i _ => hslot i))

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothPrimorialEnvelope

