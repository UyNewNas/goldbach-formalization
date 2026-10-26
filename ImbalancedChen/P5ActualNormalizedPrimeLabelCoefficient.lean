import ImbalancedChen.ActualPrimeDisjointLabelProducts

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal gamma uses the ORIGINAL product of within-label factorials.
Disjoint actual prime labels separate every head/tail product fibre.
No total-slot normalization, squarefree truncation or assumed gamma bound.
-/
namespace ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient
noncomputable section
open scoped Classical BigOperators

/-- Literal labelled prime convolution divided by original M_label. -/
def gamma {ι : Type*} (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (n : ℕ) : ℝ :=
  (actualPrimeTupleCoefficient (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)) n : ℝ) /
    (actualPrimeLabelBlocksFactorial blocks : ℝ)

/-- Raw FULL Cartesian fibres, including prime powers, obey original M. -/
theorem raw_coefficient_le_label_factorial {ι : Type*} (B : ι → Finset ℕ) :
    ∀ blocks : List (ι × ℕ),
      (∀ b ∈ blocks, ∀ p ∈ B b.1, Nat.Prime p) →
      blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1)) →
      ∀ n : ℕ, actualPrimeTupleCoefficient
        (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)) n ≤
          actualPrimeLabelBlocksFactorial blocks := by
  intro blocks
  induction blocks with
  | nil =>
      intro _hp _hd n
      simp only [actualPrimeLabelBlocksWord, List.flatMap_nil, actualPrimeSlotBox,
        actualPrimeLabelBlocksFactorial, List.map_nil, List.prod_nil, actualPrimeTupleCoefficient]
      exact (Finset.card_filter_le _ _).trans (by simp)
  | cons b blocks ih =>
      rcases b with ⟨i,m⟩
      intro hprime hdis n
      obtain ⟨hcross,hdisTail⟩ := List.pairwise_cons.mp hdis
      have hpHead : ∀ p ∈ B i, Nat.Prime p := hprime (i,m) (by simp)
      have hpTail : ∀ b ∈ blocks, ∀ p ∈ B b.1, Nat.Prime p :=
        fun b hb => hprime b (List.mem_cons_of_mem (i,m) hb)
      let T := actualPrimeSlotBox B (List.replicate m i)
      let U := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
      have hTprime : ∀ ps ∈ T, ∀ p ∈ ps, Nat.Prime p :=
        actualPrimeSlotBox_prime B _ (by
          intro j hj p hp
          have hji := (List.mem_replicate.mp hj).2
          subst j
          exact hpHead p hp)
      have hUprime : ∀ ps ∈ U, ∀ p ∈ ps, Nat.Prime p :=
        actualPrimeSlotBox_prime B _ (by
          intro j hj p hp
          obtain ⟨b,hb,rfl⟩ := actualPrimeLabelBlocksWord_mem hj
          exact hpTail b hb p hp)
      have hTin : ∀ ps ∈ T, ∀ p ∈ ps, p ∈ B i := by
        intro ps hps
        exact ((mem_actualPrimeSlotBox_replicate (B i) m ps).mp
          ((actualPrimeSlotBox_replicate_label_eq B i m) ▸ hps)).2
      have hUout : ∀ ps ∈ U, ∀ p ∈ ps, p ∉ B i :=
        actualPrimeSlotBox_forall B _ (fun p => p ∉ B i) (by
          intro j hj p hp
          obtain ⟨b,hb,rfl⟩ := actualPrimeLabelBlocksWord_mem hj
          intro hpi
          exact (Finset.disjoint_left.mp (hcross b hb)) hpi hp)
      let F := (actualPrimeSlotBox B
        (List.replicate m i ++ actualPrimeLabelBlocksWord blocks)).filter (fun ps => ps.prod = n)
      by_cases hne : F.Nonempty
      · obtain ⟨ps,hps⟩ := hne
        obtain ⟨hpsBox,hpsProd⟩ := Finset.mem_filter.mp hps
        obtain ⟨as,has,bs,hbs,rfl⟩ :=
          (actualPrimeSlotBox_mem_append B (List.replicate m i)
            (actualPrimeLabelBlocksWord blocks) ps).mp hpsBox
        let TF := T.filter (fun ps => ps.prod = as.prod)
        let UF := U.filter (fun ps => ps.prod = bs.prod)
        have hsub : F ⊆ (TF.product UF).image (fun x => x.1 ++ x.2) := by
          intro qs hqs
          obtain ⟨hqsBox,hqsProd⟩ := Finset.mem_filter.mp hqs
          obtain ⟨cs,hcs,ds,hds,rfl⟩ :=
            (actualPrimeSlotBox_mem_append B (List.replicate m i)
              (actualPrimeLabelBlocksWord blocks) qs).mp hqsBox
          have hsplit := actualPrimeVector_split_product_eq (B i) as bs cs ds
            (fun p hp => (List.mem_append.mp hp).elim (hTprime as has p) (hUprime bs hbs p))
            (fun p hp => (List.mem_append.mp hp).elim (hTprime cs hcs p) (hUprime ds hds p))
            (hTin as has) (hUout bs hbs) (hTin cs hcs) (hUout ds hds)
            (by simpa only [List.prod_append] using hpsProd.trans hqsProd.symm)
          exact Finset.mem_image.mpr ⟨(cs,ds), Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hcs,hsplit.1.symm⟩,
              Finset.mem_filter.mpr ⟨hds,hsplit.2.symm⟩⟩, rfl⟩
        have hhead : TF.card ≤ m.factorial := by
          change actualPrimeTupleCoefficient T as.prod ≤ m.factorial
          apply actualPrimeTupleCoefficient_le_factorial T m as.prod
          · intro ps hps
            simpa only [List.length_replicate] using actualPrimeSlotBox_length B (List.replicate m i) ps hps
          · exact hTprime
        have htail : UF.card ≤ actualPrimeLabelBlocksFactorial blocks :=
          ih hpTail hdisTail bs.prod
        change F.card ≤ m.factorial * actualPrimeLabelBlocksFactorial blocks
        have hcard : F.card ≤ TF.card * UF.card := by
          calc
            _ ≤ ((TF.product UF).image (fun x => x.1 ++ x.2)).card := Finset.card_le_card hsub
            _ ≤ (TF.product UF).card := Finset.card_image_le
            _ = _ := Finset.card_product TF UF
        exact hcard.trans (Nat.mul_le_mul hhead htail)
      · change F.card ≤ m.factorial * actualPrimeLabelBlocksFactorial blocks
        rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
        exact Nat.zero_le _

/-- Actual original label-normalized gamma is in [0,1] at ALL integers. -/
theorem gamma_mem_Icc {ι : Type*} (B : ι → Finset ℕ) (blocks : List (ι × ℕ))
    (hprime : ∀ b ∈ blocks, ∀ p ∈ B b.1, Nat.Prime p)
    (hdis : blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1))) (n : ℕ) :
    gamma B blocks n ∈ Set.Icc (0 : ℝ) 1 := by
  have hM : (0 : ℝ) < actualPrimeLabelBlocksFactorial blocks := by
    exact_mod_cast actualPrimeLabelBlocksFactorial_pos blocks
  unfold gamma
  refine ⟨div_nonneg (Nat.cast_nonneg _) hM.le, (div_le_one hM).mpr ?_⟩
  exact_mod_cast raw_coefficient_le_label_factorial B blocks hprime hdis n

theorem gamma_abs_le_one {ι : Type*} (B : ι → Finset ℕ) (blocks : List (ι × ℕ))
    (hprime : ∀ b ∈ blocks, ∀ p ∈ B b.1, Nat.Prime p)
    (hdis : blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1))) (n : ℕ) :
    |gamma B blocks n| ≤ 1 := by
  have h := gamma_mem_Icc B blocks hprime hdis n
  rw [abs_of_nonneg h.1]
  exact h.2

end
end ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient
