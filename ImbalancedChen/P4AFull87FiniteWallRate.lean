import ImbalancedChen.P4AFull87OrdinaryAdmissionDeletion

namespace ImbalancedChen.P4AFull87FiniteWallRate
noncomputable section
open scoped Classical BigOperators
open P4AFull87MarkedPrimePayment P4AHeldTaggedCompilerSupport
open P4AUpperTaggedParityCompiler

/-- The fixed catalogue is counted only once. For each member its centre
is allowed to read the entire erased residual divisor and the single
shape index of the ordinary total/cube or primitive native guard. -/
theorem exists_finite_rate {ι : Type*} [Fintype ι] :
    ∃ K E : ℝ, 1 < K ∧ 1 < E ∧ ∀ B : ℝ, 0 ≤ B →
      ∀ (N cap : ℕ), 1 < N → Even N → ∀ omega v tau : ℝ,
      0 < omega → omega ≤ v → v ≤ 1 → 0 ≤ tau → 3 ≤ (N : ℝ)^omega →
      E ≤ omega*Real.log (N : ℝ) → ∀ centres : ι → ℕ → ℕ → ℝ,
      ∀ S : Finset ℕ, (∀ d ∈ S, ∃ i, d ∈ covered N cap (J0 omega) omega v
        ((J0 omega : ℝ)*tau) (centres i)) →
      (B/omega)*(∑ d ∈ S, cost d) ≤
        ((Fintype.card ι:ℝ)*150*B*tau +
         (Fintype.card ι:ℝ)*10*B*K/Real.log (N:ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,hh⟩ := exists_normalized_marked_rate
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog centres S hS
  let C (i : ι) := covered N cap (J0 omega) omega v ((J0 omega : ℝ)*tau) (centres i)
  have nonneg (d : ℕ) : 0 ≤ cost d := by unfold cost; positivity
  have hmass : (∑ d ∈ S, cost d) ≤ ∑ i : ι, ∑ d ∈ C i, cost d := by
    calc
      _ ≤ ∑ d ∈ S, ∑ i : ι, if d ∈ C i then cost d else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨i,hi⟩ := hS d hd
        have hm := Finset.single_le_sum (s := Finset.univ)
          (f := fun j : ι => if d ∈ C j then cost d else 0)
          (fun j _ => by split_ifs <;> simp [nonneg]) (Finset.mem_univ i)
        simpa only [if_pos (show d ∈ C i from hi)] using hm
      _ = ∑ i : ι, ∑ d ∈ S.filter (· ∈ C i), cost d := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_filter]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
        (fun d hd => (Finset.mem_filter.mp hd).2) (fun d _ _ => nonneg d))
  apply (mul_le_mul_of_nonneg_left hmass (div_nonneg hB hw.le)).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _i : ι, (150*B*tau + 10*B*K/Real.log (N:ℝ))/omega^5 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [C,add_zero,show (30:ℝ)*(B)*5=150*B by ring] using
        hh B 0 hB le_rfl N cap hN hEven omega v tau hw hv hv1 ht h3 hlog (centres i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end
end ImbalancedChen.P4AFull87FiniteWallRate
