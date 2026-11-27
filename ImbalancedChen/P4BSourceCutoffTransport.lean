import ImbalancedChen.FiniteUpperCarrierCore
import ImbalancedChen.CurvedRegionDiscrepancy

/-!
# P4B: exact signed transport between real source cutoffs

SOURCE ONLY / YELLOW / UNCOMPILED.

For `T <= U`, moving the lower cutoff removes exactly `T <= m < U`.
The same physical support `Q` and signed coefficient `rho` are used at both
cutoffs.  Distribution and coprime-correction differences are identified
before taking absolute values.  No estimate for the resulting finite band is
assumed or asserted to be asymptotically small.
-/

namespace ImbalancedChen.P4BSourceCutoffTransport

noncomputable section
open scoped BigOperators

/-- The exact removed band; the lower boundary is closed and the upper
boundary is open, with the original inclusive product cap retained. -/
def cutoffBand (b : ℝ) (N : ℕ) (T U : ℝ) : Finset ℕ := by
  classical
  exact (realHalfProductSource b N T).filter (fun m => (m : ℝ) < U)

@[simp] theorem mem_cutoffBand {b T U : ℝ} {N m : ℕ} :
    m ∈ cutoffBand b N T U ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧ RealOrderedBadReceiver b m ∧ (m : ℝ) < U := by
  classical
  simp only [cutoffBand, Finset.mem_filter, mem_realHalfProductSource, and_assoc]

/-- Raising the lower cutoff can only remove source members. -/
theorem source_subset_of_cutoff_le {b T U : ℝ} {N : ℕ} (hTU : T ≤ U) :
    realHalfProductSource b N U ⊆ realHalfProductSource b N T := by
  intro m hm
  rcases mem_realHalfProductSource.mp hm with ⟨hN, hU, hbad⟩
  exact mem_realHalfProductSource.mpr ⟨hN, hTU.trans hU, hbad⟩

/-- No rounding or endpoint atom is lost in this set difference.  The
identity itself holds even without the ordering hypothesis on the cutoffs. -/
theorem source_sdiff_eq_band (b : ℝ) (N : ℕ) (T U : ℝ) :
    realHalfProductSource b N T \ realHalfProductSource b N U =
      cutoffBand b N T U := by
  classical
  ext m
  constructor
  · intro hm
    rcases Finset.mem_sdiff.mp hm with ⟨hT, hnotU⟩
    rcases mem_realHalfProductSource.mp hT with ⟨hN, hTm, hbad⟩
    refine mem_cutoffBand.mpr ⟨hN, hTm, hbad, ?_⟩
    apply lt_of_not_ge
    intro hU
    exact hnotU (mem_realHalfProductSource.mpr ⟨hN, hU, hbad⟩)
  · intro hm
    rcases mem_cutoffBand.mp hm with ⟨hN, hT, hbad, hU⟩
    refine Finset.mem_sdiff.mpr
      ⟨mem_realHalfProductSource.mpr ⟨hN, hT, hbad⟩, ?_⟩
    intro hmU
    exact (not_lt_of_ge (mem_realHalfProductSource.mp hmU).2.1) hU

/-- The high part of the lower-cutoff source is exactly the higher-cutoff
source. -/
theorem source_filter_upper_eq {b T U : ℝ} {N : ℕ} (hTU : T ≤ U) :
    (realHalfProductSource b N T).filter (fun m : ℕ => U ≤ (m : ℝ)) =
      realHalfProductSource b N U := by
  classical
  ext m
  constructor
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hT, hU⟩
    rcases mem_realHalfProductSource.mp hT with ⟨hN, _, hbad⟩
    exact mem_realHalfProductSource.mpr ⟨hN, hU, hbad⟩
  · intro hm
    exact Finset.mem_filter.mpr
      ⟨source_subset_of_cutoff_le hTU hm, (mem_realHalfProductSource.mp hm).2.1⟩

/-- Exact finite source transport for any real summand, with its sign
preserved. -/
theorem sum_source_eq_upper_add_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (f : ℕ → ℝ) :
    (∑ m ∈ realHalfProductSource b N T, f m) =
      (∑ m ∈ realHalfProductSource b N U, f m) +
        ∑ m ∈ cutoffBand b N T U, f m := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not
    (realHalfProductSource b N T) (fun m => U ≤ (m : ℝ)) f
  rw [source_filter_upper_eq hTU] at h
  simpa only [cutoffBand, not_le] using h.symm

private theorem cast_filter_card_eq_sum (S : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    ((S.filter P).card : ℝ) = ∑ m ∈ S, if P m then (1 : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- The exact difference of any masked source cardinalities. -/
theorem filter_card_sub_eq_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (P : ℕ → Prop) [DecidablePred P] :
    (((realHalfProductSource b N T).filter P).card : ℝ) -
        (((realHalfProductSource b N U).filter P).card : ℝ) =
      (((cutoffBand b N T U).filter P).card : ℝ) := by
  classical
  have h := sum_source_eq_upper_add_band (b := b) (N := N) hTU
    (fun m => if P m then (1 : ℝ) else 0)
  rw [← cast_filter_card_eq_sum (realHalfProductSource b N T) P,
    ← cast_filter_card_eq_sum (realHalfProductSource b N U) P,
    ← cast_filter_card_eq_sum (cutoffBand b N T U) P] at h
  linarith

/-- Exact total source mass removed by the cutoff shift. -/
theorem source_card_sub_eq_band {b T U : ℝ} {N : ℕ} (hTU : T ≤ U) :
    ((realHalfProductSource b N T).card : ℝ) -
        ((realHalfProductSource b N U).card : ℝ) =
      ((cutoffBand b N T U).card : ℝ) := by
  have h := sum_source_eq_upper_add_band (b := b) (N := N) hTU (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  linarith

/-- The congruence mass difference is the actual band congruence mass. -/
theorem congruenceMass_sub_eq_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (d : ℕ) :
    realHalfProductCongruenceMass b N T d -
        realHalfProductCongruenceMass b N U d =
      finiteCongruenceMass (cutoffBand b N T U) (fun _ => 1) N d := by
  classical
  simpa only [realHalfProductCongruenceMass, finiteCongruenceMass,
    Finset.sum_const, nsmul_eq_mul, mul_one] using
    filter_card_sub_eq_band (b := b) (N := N) hTU (fun m => Nat.ModEq d m N)

/-- The coprime mass difference uses the identical band. -/
theorem coprimeMass_sub_eq_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (d : ℕ) :
    realHalfProductCoprimeMass b N T d -
        realHalfProductCoprimeMass b N U d =
      finiteCoprimeMass (cutoffBand b N T U) (fun _ => 1) d := by
  classical
  simpa only [realHalfProductCoprimeMass, finiteCoprimeMass,
    Finset.sum_const, nsmul_eq_mul, mul_one] using
    filter_card_sub_eq_band (b := b) (N := N) hTU (fun m => Nat.Coprime m d)

/-- Signed transport of the actual physical distribution error.  Absolute
values are deliberately absent from this identity. -/
theorem distribution_sub_eq_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalDistributionError b N T Q rho -
        realPhysicalDistributionError b N U Q rho =
      ∑ d ∈ Q, rho d *
        finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d := by
  classical
  unfold realPhysicalDistributionError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [finitePrimitiveDiscrepancy,
    ← congruenceMass_sub_eq_band hTU d, ← coprimeMass_sub_eq_band hTU d]
  ring

/-- The same signed identity displayed as the literal primitive kernel on
`T <= m < U`.  Every modulus retains the original coefficient `rho d`. -/
theorem distribution_sub_eq_band_kernel {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalDistributionError b N T Q rho -
        realPhysicalDistributionError b N U Q rho =
      ∑ d ∈ Q, rho d * ∑ m ∈ cutoffBand b N T U,
        ((if Nat.ModEq d m N then (1 : ℝ) else 0) -
          (if Nat.Coprime m d then (1 : ℝ) else 0) / (Nat.totient d : ℝ)) := by
  classical
  rw [distribution_sub_eq_band hTU Q rho]
  apply Finset.sum_congr rfl
  intro d hd
  rw [finitePrimitiveDiscrepancy_eq_sum]

/-- Exact signed correction transport.  The coprime mass and the total band
cardinality are both kept; no roughness or vanishing correction is assumed. -/
theorem coprimeCorrection_sub_eq_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalCoprimeCorrection b N T Q rho -
        realPhysicalCoprimeCorrection b N U Q rho =
      ∑ d ∈ Q, rho d *
        ((finiteCoprimeMass (cutoffBand b N T U) (fun _ => 1) d -
          ((cutoffBand b N T U).card : ℝ)) / (Nat.totient d : ℝ)) := by
  classical
  unfold realPhysicalCoprimeCorrection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← coprimeMass_sub_eq_band hTU d, ← source_card_sub_eq_band hTU]
  ring

/-- A finite triangle bound after the exact signed distribution transport.
This exposes the one remaining band payment without splitting `rho`. -/
theorem abs_distribution_le_upper_add_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |realPhysicalDistributionError b N T Q rho| ≤
      |realPhysicalDistributionError b N U Q rho| +
        |∑ d ∈ Q, rho d *
          finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d| := by
  have h := distribution_sub_eq_band (b := b) (N := N) hTU Q rho
  have heq : realPhysicalDistributionError b N T Q rho =
      realPhysicalDistributionError b N U Q rho +
        ∑ d ∈ Q, rho d *
          finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d := by
    linarith
  rw [heq]
  exact abs_add_le _ _

/-- The analogous triangle bound for the actual coprime correction. -/
theorem abs_coprimeCorrection_le_upper_add_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |realPhysicalCoprimeCorrection b N T Q rho| ≤
      |realPhysicalCoprimeCorrection b N U Q rho| +
        |∑ d ∈ Q, rho d *
          ((finiteCoprimeMass (cutoffBand b N T U) (fun _ => 1) d -
            ((cutoffBand b N T U).card : ℝ)) / (Nat.totient d : ℝ))| := by
  have h := coprimeCorrection_sub_eq_band (b := b) (N := N) hTU Q rho
  have heq : realPhysicalCoprimeCorrection b N T Q rho =
      realPhysicalCoprimeCorrection b N U Q rho +
        ∑ d ∈ Q, rho d *
          ((finiteCoprimeMass (cutoffBand b N T U) (fun _ => 1) d -
            ((cutoffBand b N T U).card : ℝ)) / (Nat.totient d : ℝ)) := by
    linarith
  rw [heq]
  exact abs_add_le _ _

/-- Optional fully expanded finite triangle payment.  This absolute modulus
sum is a consequence of the preceding signed identities, not their premise. -/
theorem abs_distribution_le_upper_add_sum_abs_band {b T U : ℝ} {N : ℕ}
    (hTU : T ≤ U) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |realPhysicalDistributionError b N T Q rho| ≤
      |realPhysicalDistributionError b N U Q rho| +
        ∑ d ∈ Q, |rho d| *
          |finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d| := by
  have hband :
      |∑ d ∈ Q, rho d *
          finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d| ≤
        ∑ d ∈ Q, |rho d| *
          |finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d| := by
    calc
      _ ≤ ∑ d ∈ Q, |rho d *
          finitePrimitiveDiscrepancy (cutoffBand b N T U) (fun _ => 1) N d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul]
  exact (abs_distribution_le_upper_add_band (b := b) (N := N) hTU Q rho).trans
    (add_le_add_right hband _)

end
end ImbalancedChen.P4BSourceCutoffTransport
