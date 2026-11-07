import ImbalancedChen.Part3ActualAmplitudeResidueAlias
import ImbalancedChen.Part3PairedAlphaDeletion

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Exact Parseval for the actual all-m amplitude alias and a physical-support
residue-count energy bound. The cutoff is nonnegative and at most one;
its nonzero natural support lies in 1..floor(3M), excluding n=0 even for
small M. Both total mass and each residue count are DERIVED, not supplied.
The final explicit bound is 9*(M/q)*(1+M/q), valid for every M>0 and q>0.
-/
namespace ImbalancedChen.Part3.ActualCompletedLeftAlias20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open scoped BigOperators

private theorem energy_neg_reindex (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    energy q (fun r => f (-r))=energy q f := by
  unfold energy
  refine Finset.sum_bij (fun r _ => -r) ?_ ?_ ?_ ?_
  · intro r _
    exact Finset.mem_univ _
  · intro r _ s _ heq
    exact neg_injective heq
  · intro s _
    exact ⟨-s,Finset.mem_univ _,neg_neg s⟩
  · intro r _
    rfl

/-- Exact inverse-DFT Parseval, with its factor 1/q. The physical masses
are real nonnegative residue sums, and no finite m truncation is made. -/
theorem aliasCoefficient_energy (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) :
    energy q (aliasCoefficient q M) =
      (1/(q : ℝ))*∑ b : ZMod q,(physicalResidueMass q M b)^2 := by
  let S : ZMod q → ℂ := fun b => (physicalResidueMass q M b : ℂ)
  have hpoint (r : ZMod q) :
      ‖aliasCoefficient q M r‖^2 =
        (1/(q : ℝ)^2)*‖dft q S (-r)‖^2 := by
    rw [aliasCoefficient_eq_negative_dft q hM r]
    change ‖(1/(q : ℂ))*dft q S (-r)‖^2 = _
    rw [norm_mul,norm_div,norm_one,Complex.norm_natCast,mul_pow,div_pow]
    ring
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  calc
    _ = (1/(q : ℝ)^2)*energy q (fun r => dft q S (-r)) := by
      unfold energy
      simp_rw [hpoint]
      rw [Finset.mul_sum]
    _ = (1/(q : ℝ)^2)*((q : ℝ)*energy q S) := by
      rw [energy_neg_reindex q,dft_energy]
    _ = _ := by
      unfold energy S
      simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
      field_simp [hq.ne']
      <;> ring

/-- The actual positive physical support excludes n=0. This removes an
otherwise false small-scale +1 in the total cutoff mass estimate. -/
theorem cutoff_nonzero_mem_positive {M : ℝ} (hM : 0 < M) {n : ℕ}
    (hn : scaledDyadicCutoff M n ≠ 0) : n ∈ Ioc 0 (Nat.floor (3*M)) := by
  have hs := scaledDyadicCutoff_mem_Icc_of_ne_zero hM hn
  have hnR : (0 : ℝ) < n := (half_pos hM).trans_le hs.1
  have hn0 : 0 < n := by exact_mod_cast hnR
  exact Finset.mem_Ioc.mpr ⟨hn0,Nat.le_floor hs.2⟩

theorem physicalResidueMass_nonneg (q : ℕ) [NeZero q] (M : ℝ) (b : ZMod q) :
    0 ≤ physicalResidueMass q M b := by
  unfold physicalResidueMass
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact scaledDyadicCutoff_nonneg M n
  · exact le_rfl

/-- Real physical mass partition into ALL residue classes. -/
theorem sum_physicalResidueMass (q : ℕ) [NeZero q] (M : ℝ) :
    (∑ b : ZMod q,physicalResidueMass q M b) =
      ∑ n ∈ Physical.naturalSupport M,scaledDyadicCutoff M n := by
  unfold physicalResidueMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp

/-- True compact-cutoff total mass, with no additive error at small M. -/
theorem physicalResidueMass_total_le (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) :
    (∑ b : ZMod q,physicalResidueMass q M b) ≤ 3*M := by
  rw [sum_physicalResidueMass]
  let J := (Physical.naturalSupport M).filter (fun n => scaledDyadicCutoff M n ≠ 0)
  have hsub : J ⊆ Ioc 0 (Nat.floor (3*M)) := by
    intro n hn
    exact cutoff_nonzero_mem_positive hM (Finset.mem_filter.mp hn).2
  calc
    _ = ∑ n ∈ J,scaledDyadicCutoff M n := by
      dsimp only [J]
      simp only [Finset.sum_filter_ne_zero]
    _ ≤ ∑ _n ∈ J,(1 : ℝ) := Finset.sum_le_sum (fun n _ => scaledDyadicCutoff_le_one M n)
    _ = (J.card : ℝ) := by simp
    _ ≤ ((Ioc 0 (Nat.floor (3*M))).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (Nat.floor (3*M) : ℝ) := by simp only [Nat.card_Ioc,Nat.sub_zero]
    _ ≤ _ := Nat.floor_le (by positivity)

/-- Each residue contains at most floor(3M)/q+1 potentially active points.
The actual cutoff values are bounded by one before counting the support. -/
theorem physicalResidueMass_le (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) (b : ZMod q) :
    physicalResidueMass q M b ≤ 3*M/(q : ℝ)+1 := by
  let J := (Physical.naturalSupport M).filter (fun n =>
    scaledDyadicCutoff M n ≠ 0 ∧ (n : ZMod q)=b)
  have hsum : physicalResidueMass q M b ≤ (J.card : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Physical.naturalSupport M,
          if scaledDyadicCutoff M n ≠ 0 ∧ (n : ZMod q)=b then (1 : ℝ) else 0 := by
        unfold physicalResidueMass
        apply Finset.sum_le_sum
        intro n _
        by_cases hz : scaledDyadicCutoff M n=0
        · simp only [hz,ne_eq,not_true_eq_false,false_and,if_false,ite_self,le_refl]
        · by_cases hb : (n : ZMod q)=b
          · simp only [hz,ne_eq,not_false_eq_true,hb,true_and,if_true]
            exact scaledDyadicCutoff_le_one M n
          · simp only [hb,if_false,and_false,le_refl]
      _ = _ := by rw [← Finset.sum_filter];simp only [J,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hsub : J ⊆ (Icc 0 (Nat.floor (3*M))).filter
      (fun n : ℕ => Int.ModEq q ((n : ℤ)*1) (b.val : ℤ)) := by
    intro n hn
    obtain ⟨_,hz,hb⟩ := Finset.mem_filter.mp hn
    have hsupport := Finset.mem_Ioc.mp (cutoff_nonzero_mem_positive hM hz)
    have hmod : Int.ModEq q (n : ℤ) (b.val : ℤ) := by
      apply (ZMod.intCast_eq_intCast_iff (n : ℤ) (b.val : ℤ) q).mp
      simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,hsupport.2⟩,
      by simpa only [mul_one] using hmod⟩
  have hcard : J.card ≤ Nat.floor (3*M)/q+1 :=
    (Finset.card_le_card hsub).trans
      (PairedAlphaDeletion.card_product_modEq_le (Nat.floor (3*M)) q 1 (b.val : ℤ) (Nat.coprime_one_left q))
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  calc
    _ ≤ (J.card : ℝ) := hsum
    _ ≤ ((Nat.floor (3*M)/q+1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (Nat.floor (3*M) : ℝ)/(q : ℝ)+1 := by
      push_cast
      exact add_le_add (Nat.cast_div_le : ((Nat.floor (3*M)/q : ℕ) : ℝ) ≤
        (Nat.floor (3*M) : ℝ)/(q : ℝ)) le_rfl
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right (Nat.floor_le (by positivity : 0 ≤ 3*M)) hq.le) le_rfl

/-- Derived actual ALL-m left-alias energy bound. The explicit constant
9 is valid at every positive scale M, including M<1 and composite q. -/
theorem aliasCoefficient_energy_le (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) :
    energy q (aliasCoefficient q M) ≤ 9*(M/(q : ℝ))*(1+M/(q : ℝ)) := by
  rw [aliasCoefficient_energy q hM]
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hB : 0 ≤ 3*M/(q : ℝ)+1 := by positivity
  calc
    _ ≤ (1/(q : ℝ))*∑ b : ZMod q,(3*M/(q : ℝ)+1)*physicalResidueMass q M b := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hq.le)
      apply Finset.sum_le_sum
      intro b _
      have hb := mul_le_mul_of_nonneg_right (physicalResidueMass_le q hM b)
        (physicalResidueMass_nonneg q M b)
      nlinarith only [hb]
    _ = (1/(q : ℝ))*((3*M/(q : ℝ)+1)*(∑ b : ZMod q,physicalResidueMass q M b)) := by
      rw [Finset.mul_sum]
    _ ≤ (1/(q : ℝ))*((3*M/(q : ℝ)+1)*(3*M)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (physicalResidueMass_total_le q hM) hB)
        (one_div_nonneg.mpr hq.le)
    _ = 3*(M/(q : ℝ))*(1+3*(M/(q : ℝ))) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      have ht : 0 ≤ M/(q : ℝ) := div_nonneg hM.le hq.le
      nlinarith only [ht]

end
end ImbalancedChen.Part3.ActualCompletedLeftAlias20261026b
