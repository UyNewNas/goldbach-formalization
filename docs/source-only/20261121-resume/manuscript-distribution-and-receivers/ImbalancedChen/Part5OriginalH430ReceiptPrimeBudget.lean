import ImbalancedChen.Part5OriginalH430ClassicalReceiverSubfamily
import ImbalancedChen.QuotientChenPositiveBound

/-! The ORIGINAL root roughness controls the actual receiver's prime
support.  The cutoff is 417/5000, not the distinct 100/1149 cutoff in
the eleven-term weight.  The generic product lemma is reused. -/
namespace ImbalancedChen.Part5OriginalH430ReceiptPrimeBudget
noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers

theorem original_receipt_primeFactors_le {N p q : ℕ} (hN : 2 ≤ N)
    (hq : q ∈ originalReceiver N p) : q.primeFactors.card ≤ 11 := by
  obtain ⟨hsource,hrough⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqpos,hqN,_⟩ := chenQuotientPrimeSource_data hsource
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0:ℝ) < N := zero_lt_one.trans hNr
  have hpow : ((N:ℝ)^a)^q.primeFactors.card ≤ (N:ℝ) :=
    (chen_pow_primeFactors_card_le hqpos.ne'
      (Real.rpow_nonneg (Nat.cast_nonneg N) a) hrough).trans (by exact_mod_cast hqN)
  by_contra hk
  have h12 : (12:ℝ) ≤ q.primeFactors.card := by
    exact_mod_cast (show 12 ≤ q.primeFactors.card by omega)
  have hexp : (1:ℝ) < a*(q.primeFactors.card:ℝ) := by
    norm_num [a] at ⊢
    linarith only [h12]
  have hstrict : (N:ℝ) < ((N:ℝ)^a)^q.primeFactors.card := by
    calc
      (N:ℝ) = (N:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ < (N:ℝ)^(a*(q.primeFactors.card:ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hNr hexp
      _ = _ := Real.rpow_mul_natCast hNp.le _ _
  exact (not_lt_of_ge hpow) hstrict

end
end ImbalancedChen.Part5OriginalH430ReceiptPrimeBudget
