import ImbalancedChen.P4BPositiveUpperPrimeBV
import ImbalancedChen.P4BPositiveUpperLowRankLocalScale
import ImbalancedChen.P2OriginalGammaUpperLowRankConsumer
import ImbalancedChen.U9SemiprimeSwitchedPrimeAP

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The coefficient is the original positive-upper rho, with both beta signs.
The generic Bezout residue from U9 is used only as elementary arithmetic;
no U9 count, lower W licence, convolution BV or J estimate is transferred.
The exact original Gamma source and its high-rank/unit surfaces survive.
-/
namespace ImbalancedChen.P2OriginalGammaUpperPrimeBVAttachment
noncomputable section
open scoped Classical BigOperators
open Filter
open Wu2008DoubleSieve
open P4BPositiveUpperLowRankClass P4BPositiveUpperPrimeBV
open P2OriginalGammaUpperLowRankConsumer P2OriginalU5ExactNormalizedSource
open P5Z.OriginalHBCompleteProductScale P5Z.HBRightClosedDyadicRoles

def activeLow (retain : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  (actualSmallRoughModuli retain N cap w z).filter
    (fun q => rankRho retain N cap w z L 2 q ≠ 0)

theorem full_carrier_eq_active (retain : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli retain N cap w z,
      rankRho retain N cap w z L 2 q * F q) =
    ∑ q ∈ activeLow retain N cap w z L, rankRho retain N cap w z L 2 q * F q := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnq
  have hzq : rankRho retain N cap w z L 2 q = 0 := by
    by_contra hne
    exact hnq (Finset.mem_filter.mpr ⟨hq,hne⟩)
  rw [hzq,zero_mul]

/-- Primitive moving residue for a COMPLETE fixed complementary integer.
Both discrepancy terms vanish when that integer is a nonunit modulo q. -/
theorem gammaKernel_mul {N q : ℕ} (hq : 0 < q) (hN : N.Coprime q)
    (b p : ℕ) :
    gammaKernel N q (b*p) = if b.Coprime q then
      gammaKernel (U9SemiprimeSwitch.residue N b q) q p else 0 := by
  have hAP := U9SemiprimeSwitch.product_AP_iff (N := N) (m := b) (r := p) hq hN
  by_cases hb : b.Coprime q
  · simp only [gammaKernel,hAP,hb,true_and,Nat.coprime_mul_iff_left,if_true]
  · simp only [gammaKernel,hAP,hb,false_and,Nat.coprime_mul_iff_left,if_false,
      zero_div,sub_zero]

/-- Apply the elementary residue identity to the literal source product,
including quotient label x.2=1.  The marked pair is still b=t.1*t.2. -/
theorem original_label_kernel {N q : ℕ} (hq : 0 < q) (hN : N.Coprime q)
    (t : ℕ × ℕ) (x : P2TwentyOneUnsiftedArithmeticSource.Label) :
    gammaKernel N q (P2TwentyOneUnsiftedArithmeticSource.product (t.1*t.2) x) =
      if (t.1*t.2).Coprime q then
        gammaKernel (U9SemiprimeSwitch.residue N (t.1*t.2) q) q (x.1.prod*x.2)
      else 0 := by
  simpa only [P2TwentyOneUnsiftedArithmeticSource.product,mul_assoc] using
    gammaKernel_mul hq hN (t.1*t.2) (x.1.prod*x.2)

/-- Exact moving-residue dictionary for ALL original mother-list entries.
This is the unchanged Gamma family; no singleton prime is substituted for
the product of the residual word and quotient. -/
theorem original_Gamma_moving_residue {N q : ℕ} (hq : 0 < q)
    (hN : N.Coprime q) (t : ℕ × ℕ) :
    gammaDiscrepancy N t q =
      (secondFunctionalMotherPrefixIndices.map fun i =>
        ((secondFunctionalMotherGammaWords i).map fun cs =>
          ∑ x ∈ P2OriginalU5WholeGroupCapacity.rootLabels N t cs,
            if (t.1*t.2).Coprime q then
              gammaKernel (U9SemiprimeSwitch.residue N (t.1*t.2) q) q (x.1.prod*x.2)
            else 0).sum).sum := by
  unfold gammaDiscrepancy sourceTest
  simp_rw [original_label_kernel hq hN]

/-- Coprimality of the MOVING residue is derived from the actual original
target support.  It is not an independent class assumption. -/
theorem active_moving_residue_primitive (retain : List ℕ → Bool)
    (N cap b : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ activeLow retain N cap w z L) (hb : b.Coprime q) :
    0 < q ∧ (U9SemiprimeSwitch.residue N b q).Coprime q := by
  have hm := (Finset.mem_filter.mp hq).1
  have hsq := actualSmallRoughModuli_squarefree retain N cap w z hm
  have hq0 := Nat.pos_of_ne_zero hsq.ne_zero
  exact ⟨hq0,U9SemiprimeSwitch.residue_coprime N hq0 hb
    (actualSmallRoughModuli_coprime_target retain N cap w z hm).symm⟩

/-- The literal original upper rank-two source receives genuine PRIME BV
for every finite signed prefix profile.  No physical-level or BV licence
is assumed: the full beta level and exponent 19/48 are proved by J.
The common prime cap is N here, and the residue is the original target N. -/
theorem eventually_original_upper_prime_profile (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (nu epsilon : ℝ),
        0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
        ∀ (k : ℕ) (I : Finset (Fin k)) (c : Fin k → ℝ) (Y : Fin k → ℕ),
          (∀ i ∈ I, Y i ≤ N) →
          |∑ q ∈ actualSmallRoughModuli retain N cap ((N : ℝ)^(nu*epsilon^2))
              ((N : ℝ)^(nu*(19/96 : ℝ))),
            rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
              ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q *
              finitePrimitiveDiscrepancy (chenPrimePrefix N) (prefixProfile I c Y) N q| ≤
            (∑ i ∈ I, |c i|)*(C*(N : ℝ)/Real.log (N : ℝ)^A) := by
  obtain ⟨C,hC,hBV⟩ := eventually_profile_log_saving A
  refine ⟨C,hC,?_⟩
  filter_upwards [hBV,eventually_ge_atTop (2 : ℕ)] with N hBVN hN
  intro retain cap nu epsilon hnu hnu1 heps heps1 k I c Y hY
  let w := (N : ℝ)^(nu*epsilon^2)
  let z := (N : ℝ)^(nu*(19/96 : ℝ))
  let L := (N : ℝ)^(nu*epsilon)
  rw [full_carrier_eq_active]
  apply hBVN (activeLow retain N cap w z L) (rankRho retain N cap w z L 2)
  · intro q hq
    have ha := (Finset.mem_filter.mp hq).2
    have hd := attached_rank_two_support (fun _ => retain) (fun _ => cap)
      (mul_nonneg hnu (by norm_num : (0 : ℝ)≤19/96)) (by omega : 1≤N) ha
    have hb := (original_upper_rank_two_below_half (fun _ => retain) (fun _ => cap)
      hnu hnu1 heps (by linarith : epsilon<5/48) (by omega : 1<N) ha).1
    have hb' : (q : ℝ) ≤ (N : ℝ)^(9/20 : ℝ) := hb.le.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
        (by linarith : 19/48+epsilon ≤ (9/20 : ℝ)))
    exact Finset.mem_Icc.mpr ⟨hd.1,Nat.le_floor hb'⟩
  · intro q hq
    exact actualSmallRoughModuli_squarefree retain N cap w z (Finset.mem_filter.mp hq).1
  · intro q hq
    exact rankRho_abs_le_one retain N cap w z L 2 q
  · intro q hq
    exact (actualSmallRoughModuli_coprime_target retain N cap w z
      (Finset.mem_filter.mp hq).1).symm
  · exact hY

/-- Actual complete-scale attachment, allowing any primitive moving
residue (in particular the constructed complement residue above).  One
threshold in N forces the COMPLETE cap X past the classical BV threshold
by the original source trim, uniformly over all tuples and blocks.
This proves a prime-source payment on that scale, not a short-fibre or
convolution estimate for the residual Gamma variable. -/
theorem original_complete_scale_prime_profile (A : ℕ)
    {Csource kappa kappa0 nu epsilon : ℝ}
    (hCsource : 0<Csource) (hkappa : 0<kappa) (hkappa1 : kappa≤1/100)
    (htrim : kappa0<kappa/(4*(1+kappa))) (hnu : 0≤nu) (hnu1 : nu≤1)
    (heps : 0≤epsilon) (heps1 : epsilon≤1/1000) :
    ∃ C : ℝ, 0<C ∧ ∃ N0 : ℕ, 2≤N0 ∧
      ∀ (X N : ℕ), N0≤N →
      ∀ (gs : List OriginalGroupTuple) (p : ℕ) (b d : Block),
      p∈joined gs → Owns b p → Owns d (completeInteger gs/p) →
      (N : ℝ)^(1-kappa0)≤(completeInteger gs : ℝ) →
      (completeInteger gs : ℝ)≤Csource*N → localScale b d≤(X : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (a : ℕ → ℕ),
      (∀ q ∈ activeLow retain N cap ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)), (a q).Coprime q) →
      ∀ (k : ℕ) (I : Finset (Fin k)) (c : Fin k → ℝ) (Y : Fin k → ℕ),
      (∀ i∈I, Y i≤X) →
      |∑ q ∈ actualSmallRoughModuli retain N cap ((N : ℝ)^(nu*epsilon^2))
          ((N : ℝ)^(nu*(19/96 : ℝ))),
        rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
          ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q *
          finitePrimitiveDiscrepancy (chenPrimePrefix X) (prefixProfile I c Y) (a q) q| ≤
        (∑ i∈I, |c i|)*(C*(X : ℝ)/Real.log (X : ℝ)^A) := by
  obtain ⟨C,hC,hBV⟩ := eventually_profile_log_saving A
  obtain ⟨X0,hX0⟩ := Filter.eventually_atTop.mp hBV
  obtain ⟨N0,hN0,hlocal⟩ :=
    P4BPositiveUpperLowRankLocalScale.exists_original_upper_low_rank_local_threshold
      hCsource hkappa hkappa1 htrim hnu hnu1 heps heps1
  have hk0 := manuscript_kappaZero_lt_quarter hkappa htrim
  obtain ⟨N1,hlarge⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (4*(X0 : ℝ))
      (show (0 : ℝ)<1-kappa0 by linarith))
  refine ⟨C,hC,max N0 N1,hN0.trans (le_max_left _ _),?_⟩
  intro X N hN gs p b d hp hb hd ht hs hx retain cap a ha k I c Y hY
  have hNlocal : N0≤N := (le_max_left _ _).trans hN
  have hNlarge : N1≤N := (le_max_right _ _).trans hN
  have hscale := actual_trimmed_complete_scale gs hp hb hd ht hs
  have hlargeN := hlarge N hNlarge
  simp only [Real.rpow_zero,mul_one] at hlargeN
  have hX : X0≤X := by
    have hh : (X0 : ℝ)≤X := by linarith [hscale.1]
    exact_mod_cast hh
  rw [full_carrier_eq_active]
  apply hX0 X hX
  · intro q hq
    have hdq := hlocal N hNlocal gs p b d hp hb hd ht hs retain cap q (Finset.mem_filter.mp hq).2
    have hbound : (q : ℝ)≤(X : ℝ)^(9/20 : ℝ) := hdq.2.2.2.2.2.le.trans
      (Real.rpow_le_rpow (zero_lt_one.trans hdq.1).le hx (by norm_num))
    exact Finset.mem_Icc.mpr ⟨hdq.2.1,Nat.le_floor hbound⟩
  · intro q hq
    exact actualSmallRoughModuli_squarefree _ _ _ _ _ (Finset.mem_filter.mp hq).1
  · intro q hq
    exact rankRho_abs_le_one _ _ _ _ _ _ _ _
  · exact ha
  · exact hY

/-- No Gamma term is declared paid by the prime theorem.  This records
the original full coefficient, high ranks, and outer unit/nonunit terms
in one exact identity, ready for the still-missing convolution supplier. -/
theorem original_Gamma_high_and_unit_retained
    (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    fullError N t nu r epsilon retain cap =
      (∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
        rankRho (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
          ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q * unitTest N t (gammaKernel N q)) +
      (∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
        rankRho (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
          ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q * nonunitTest N t (gammaKernel N q)) +
      highError N t nu r epsilon retain cap := by
  rw [original_Gamma_upper_error_split,original_Gamma_upper_low_error_unit_nonunit]

end
end ImbalancedChen.P2OriginalGammaUpperPrimeBVAttachment
