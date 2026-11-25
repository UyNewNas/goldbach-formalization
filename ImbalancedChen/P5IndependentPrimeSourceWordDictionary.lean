import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound
import ImbalancedChen.PrimeProductsMellinExactMeanInsertion

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
This starts from the independently defined Part3 labelled-prime source.
Its test variables u are NOT physical modulus-prefix or residual-divisor
variables. The dictionary preserves every ordered coordinate and repeated
prime, the same Q/rho, and the exact coprime mean before any estimate.
-/
namespace ImbalancedChen.P5Z.IndependentPrimeSourceWordDictionary
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open ExactOriginalSmoothDyadicPartition ActualLabelledPrimeSmoothCharts
open LicensedOriginalIntegerProfile
open ImbalancedChen.Part3.OriginalProperPowerActualChart

def sourceWord {k cap : ℕ} (u : Fin k → Fin (cap + 1)) : List ℕ :=
  List.ofFn (fun i => (u i).val)

theorem sourceWord_injective (k cap : ℕ) :
    Function.Injective (sourceWord : (Fin k → Fin (cap + 1)) → List ℕ) := by
  intro u v huv
  have hv : (fun i => (u i).val) = (fun i => (v i).val) := List.ofFn_injective huv
  funext i
  exact Fin.ext (congrFun hv i)

theorem sourceWord_prime_mem {k cap : ℕ} {u : Fin k → Fin (cap + 1)}
    (hu : u ∈ Part3.labelledPrimeTuples k cap) : sourceWord u ∈ primeTuples cap k := by
  have hprime : ∀ i, Nat.Prime (u i).val := (Finset.mem_filter.mp hu).2
  apply primeTuples_mem cap k (sourceWord u) (by simp [sourceWord])
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨hprime i, by have := (u i).isLt; omega⟩

/-- The actual two finite carriers are bijective. Product values need
not be injective; no tuple is divided by a factorial or sorted away. -/
theorem prime_words_image (k cap : ℕ) :
    primeTuples cap k = (Part3.labelledPrimeTuples k cap).image sourceWord := by
  ext ps
  constructor
  · intro hps
    obtain ⟨hlen, hprime⟩ := primeTuples_spec cap k hps
    have hvec (i : Fin k) : (wordVector k ps i).Prime ∧ wordVector k ps i ≤ cap := by
      have hi : i.val < ps.length := by omega
      simpa only [wordVector, List.getD_eq_getElem _ _ hi] using
        ⟨(hprime ps[i.val] (List.getElem_mem hi)).1,
          (hprime ps[i.val] (List.getElem_mem hi)).2.2⟩
    let u : Fin k → Fin (cap + 1) := fun i => ⟨wordVector k ps i, by
      have := (hvec i).2
      omega⟩
    have hu : u ∈ Part3.labelledPrimeTuples k cap :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (hvec i).1⟩
    refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
    simpa only [sourceWord, u] using ofFn_wordVector hlen
  · intro hps
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hps
    exact sourceWord_prime_mem hu

@[simp] theorem sourceWord_product {k cap : ℕ} (u : Fin k → Fin (cap + 1)) :
    (sourceWord u).prod = Part3.labelledProduct u := by
  simp only [sourceWord, List.prod_ofFn, Part3.labelledProduct]

def wordKernel (Q : Finset ℕ) (rho : ℕ → ℂ) (T : ℕ) (ps : List ℕ) : ℂ :=
  ∑ q ∈ Q, rho q * MellinInsertion20261028.residueKernel q T ps.prod

theorem residueKernel_real (q T b : ℕ) :
    MellinInsertion20261028.residueKernel q T b =
      (((if Nat.ModEq q b T then (1 : ℝ) else 0) -
        (if b.Coprime q then (1 : ℝ) else 0) / (q.totient : ℝ)) : ℂ) := by
  by_cases hres : b % q = T % q <;> by_cases hcop : b.Coprime q <;>
    simp [MellinInsertion20261028.residueKernel, Nat.ModEq, hres, hcop]

/-- Exact bridge from the ORIGINAL Part3 source, not a newly named
atlas. W is any fixed list test here; smooth licensing is not asserted.
The result applies separately to count and exact mean by their shared
kernel, so neither an AP estimate nor a mean estimate is a premise. -/
theorem original_prime_discrepancy_words (k cap T : ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (W : List ℕ → ℝ) :
    (Part3.primeProductSignedError k cap T Q rho (fun u => W (sourceWord u)) : ℂ) =
      MellinInsertion20261028.exactDiscrepancy (primeTuples cap k) Q
        (fun q => (rho q : ℂ)) List.prod T (fun ps => (W ps : ℂ)) := by
  unfold Part3.primeProductSignedError MellinInsertion20261028.exactDiscrepancy
    MellinInsertion20261028.functional
  rw [prime_words_image, Finset.sum_image]
  · push_cast
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro u hu
    rw [sourceWord_product, residueKernel_real]
    push_cast
    ring
  · intro u hu v hv huv
    exact sourceWord_injective k cap huv

/-- Genuine original geometric weights enter through their own licence.
The same ambient extension is used on every integer replacement word. -/
theorem licensed_original_discrepancy_words {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (cap T : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (Part3.primeProductSignedError k cap T Q rho
      (fun u => Wprime (fun i => (u i).val)) : ℂ) =
      MellinInsertion20261028.exactDiscrepancy (primeTuples cap k) Q
        (fun q => (rho q : ℂ)) List.prod T (fun ps => (listExtension L ps : ℂ)) := by
  rw [← original_prime_discrepancy_words k cap T Q rho (listExtension L)]
  congr 1
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  have hp : ∀ i, Nat.Prime (u i).val := (Finset.mem_filter.mp hu).2
  rw [sourceWord, listExtension_ofFn, integerExtension_eq_on_primes L _ hp]

end
end ImbalancedChen.P5Z.IndependentPrimeSourceWordDictionary
