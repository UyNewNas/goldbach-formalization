import ImbalancedChen.P2SeedOmegaActualUnitCountReceiver
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
New arithmetic LOWER support for the actual finite unit20/21 fibres.
The pinned JointTailGeometry already supplies real graph support and its
upper-alpha vanishing; that argument is reused, never re-proved here.
Above the graph upper endpoint the finite physical fibre need NOT vanish.
The exact finite vanishing proved here is BELOW the minimum total prime
exponent, at the SAME actual omega3XPhi and Q/d, before AP estimates.
-/

namespace ImbalancedChen.P2SeedOmegaFiniteUnitLowerSupport
noncomputable section
open Set Finset MeasureTheory Classical
open scoped BigOperators
open Wu2008DoubleSieve
open SecondFunctionalUnitPrimeFibre
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)

theorem prefix20_minimum_sum {R : ℝ} (hR : 1<R)
    {g : Fin 4 → primeSlabPrimes R} (hg : g ∈ HighUnit.primePrefix20 R a2 a3 b) :
    a2+3*a3≤∑ i,coordinate g i := by
  have h := (HighUnit.mem_primePrefix20 hR a2 a3 b g).mp hg
  rw [SecondFunctionalJointTail.sum_four]
  rcases h with ⟨h0,_,h1,h2,h3,_⟩
  linarith only [h0,h1,h2,h3]

theorem prefix21_minimum_sum {R : ℝ} (hR : 1<R)
    {g : Fin 5 → primeSlabPrimes R} (hg : g ∈ HighUnit.primePrefix21 R a3 b) :
    5*a3≤∑ i,coordinate g i := by
  have h := (HighUnit.mem_primePrefix21 hR a3 b g).mp hg
  rw [SecondFunctionalJointTail.sum_five]
  rcases h with ⟨h0,h1,h2,h3,h4,_⟩
  linarith only [h0,h1,h2,h3,h4]

/-- The last specified prime is strictly above the next-to-last one;
therefore even equality at the minimum exponent gives an EMPTY fibre. -/
theorem physical20_empty_below {R alpha : ℝ} (hR : 1<R)
    (ha : alpha≤a2+4*a3) (g : Fin 4 → primeSlabPrimes R)
    (hg : g ∈ HighUnit.primePrefix20 R a2 a3 b) :
    physical (prefixProduct g) (R^alpha) (g (Fin.last 3)).val (R^b)=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨_,hstrict,_,hprod⟩ :=
    (SecondFunctionalUnitFiniteKernel.physical_membership hR g alpha b p).mp hp
  have h := (HighUnit.mem_primePrefix20 hR a2 a3 b g).mp hg
  have hlast : a3≤coordinate g (Fin.last 3) := by
    rcases h with ⟨_,_,h1,h2,h3,_⟩
    change a3≤coordinate g 3
    linarith only [h1,h2,h3]
  have hpmin : R^a3<(p : ℝ) :=
    ((HighUnit.power_le_coordinate hR g (Fin.last 3) a3).mpr hlast).trans_lt hstrict
  have hpref : R^(a2+3*a3)≤prefixProduct g := by
    rw [prefixProduct_power hR]
    exact Real.rpow_le_rpow_of_exponent_le hR.le (prefix20_minimum_sum hR hg)
  have hbound : R^(a2+4*a3)<prefixProduct g*(p : ℝ) := by
    calc
      _ = R^(a2+3*a3)*R^a3 := by
        rw [← Real.rpow_add (by linarith : 0<R)]
        congr 1
        ring
      _ ≤ prefixProduct g*R^a3 := mul_le_mul_of_nonneg_right hpref
        (Real.rpow_nonneg (by linarith) _)
      _ < _ := mul_lt_mul_of_pos_left hpmin (prefixProduct_pos hR g)
  have hupper := Real.rpow_le_rpow_of_exponent_le hR.le ha
  exact (not_lt_of_ge (hprod.trans hupper)) hbound

theorem physical21_empty_below {R alpha : ℝ} (hR : 1<R)
    (ha : alpha≤6*a3) (g : Fin 5 → primeSlabPrimes R)
    (hg : g ∈ HighUnit.primePrefix21 R a3 b) :
    physical (prefixProduct g) (R^alpha) (g (Fin.last 4)).val (R^b)=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨_,hstrict,_,hprod⟩ :=
    (SecondFunctionalUnitFiniteKernel.physical_membership hR g alpha b p).mp hp
  have h := (HighUnit.mem_primePrefix21 hR a3 b g).mp hg
  have hlast : a3≤coordinate g (Fin.last 4) := by
    rcases h with ⟨h0,h1,h2,h3,h4,_⟩
    change a3≤coordinate g 4
    linarith only [h0,h1,h2,h3,h4]
  have hpmin : R^a3<(p : ℝ) :=
    ((HighUnit.power_le_coordinate hR g (Fin.last 4) a3).mpr hlast).trans_lt hstrict
  have hpref : R^(5*a3)≤prefixProduct g := by
    rw [prefixProduct_power hR]
    exact Real.rpow_le_rpow_of_exponent_le hR.le (prefix21_minimum_sum hR hg)
  have hbound : R^(6*a3)<prefixProduct g*(p : ℝ) := by
    calc
      _ = R^(5*a3)*R^a3 := by
        rw [← Real.rpow_add (by linarith : 0<R)]
        congr 1
        ring
      _ ≤ prefixProduct g*R^a3 := mul_le_mul_of_nonneg_right hpref
        (Real.rpow_nonneg (by linarith) _)
      _ < _ := mul_lt_mul_of_pos_left hpmin (prefixProduct_pos hR g)
  have hupper := Real.rpow_le_rpow_of_exponent_le hR.le ha
  exact (not_lt_of_ge (hprod.trans hupper)) hbound

/-- Actual supported divisor and actual logarithmic alpha, not a reset
alpha=2. Every original atom retains its complete list and prime output. -/
theorem atoms20_empty_at_actual_alpha {N d : ℕ} {delta : ℝ}
    (hN : 0<N) (hd : 0<d) (hR : 1<(N : ℝ)^(1/2-delta)/d)
    (ha : omega3XPhi N d delta≤a2+4*a3) :
    HighUnitSource.atoms N d (((N : ℝ)^(1/2-delta)/d)^a0)
      (((N : ℝ)^(1/2-delta)/d)^a1) (((N : ℝ)^(1/2-delta)/d)^a2)
      (((N : ℝ)^(1/2-delta)/d)^a3) (((N : ℝ)^(1/2-delta)/d)^b)
      HighUnitSource.word20=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨y,hy,_⟩ := HighUnitSource.geometry20 hd hR
    (by norm_num [a2]) (by norm_num [b]) x hx
  obtain ⟨hg,hq⟩ := Finset.mem_sigma.mp hy
  have hz := physical20_empty_below hR ha y.1 hg
  rw [HighUnit.boxed_scale_identity hN hd hR] at hz
  rw [hz] at hq
  exact Finset.not_mem_empty y.2 hq

theorem atoms21_empty_at_actual_alpha {N d : ℕ} {delta : ℝ}
    (hN : 0<N) (hd : 0<d) (hR : 1<(N : ℝ)^(1/2-delta)/d)
    (ha : omega3XPhi N d delta≤6*a3) :
    HighUnitSource.atoms N d (((N : ℝ)^(1/2-delta)/d)^a0)
      (((N : ℝ)^(1/2-delta)/d)^a1) (((N : ℝ)^(1/2-delta)/d)^a2)
      (((N : ℝ)^(1/2-delta)/d)^a3) (((N : ℝ)^(1/2-delta)/d)^b)
      HighUnitSource.word21=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨y,hy,_⟩ := HighUnitSource.geometry21 hd hR
    (by norm_num [a3]) (by norm_num [b]) x hx
  obtain ⟨hg,hq⟩ := Finset.mem_sigma.mp hy
  have hz := physical21_empty_below hR ha y.1 hg
  rw [HighUnit.boxed_scale_identity hN hd hR] at hz
  rw [hz] at hq
  exact Finset.not_mem_empty y.2 hq

end
end ImbalancedChen.P2SeedOmegaFiniteUnitLowerSupport
