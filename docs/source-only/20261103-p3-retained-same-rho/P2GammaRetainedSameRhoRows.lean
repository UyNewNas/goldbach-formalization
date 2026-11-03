import ImbalancedChen.P2GammaChosenGridLocalConductor
import ImbalancedChen.P2GammaJointRetainedReduction

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The literal Cartesian row is attached to the existing character rectangle,
then to the unchanged original upper rough-rank-at-most-two coefficient.
This does not assert an enhanced, lower-start or marked coefficient theorem.
-/

namespace ImbalancedChen.P2GammaRetainedSameRhoRows
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaUpperLowRankConsumer P2OriginalGammaDivisorNorm
open P2GammaOriginalCartesianMask P2GammaSmoothLogGrid
open P2GammaRetainedInteriorGeometry P2GammaRetainedCompleteScale
open P2GammaRetainedPhysicalRows P2GammaRetainedActualNorms
open P2GammaSmallConductorIntervalBridge P2GammaExactConductorRegrouping
open P2GammaHeadWindowDictionary P2GammaOriginalScaleTransport
open P2GammaChosenLogGridBudget P2GammaRetainedLowRankLevel
open P2GammaChosenGridLocalConductor P4BPositiveUpperLowRankClass
open P5OriginalU5CausalFinite (pairSupport)
open Wu2008DoubleSieve

/-- An abbreviation for the SAME physical integer coefficient, including beta. -/
def upperRho (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap q : ℕ) : ℝ :=
  rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q

/-- Direct original Cartesian source; it is not defined using a target error. -/
def cartesianRow (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l q : ℕ) : ℂ :=
  ∑ p ∈ headCarrier N t c, ∑ y ∈ rootComplementLabels N t (c::cs),
    (complexWeight δ j p*betaLabel N t H δ j l y)*
      (gammaKernel N q (product (t.1*t.2) y*p) : ℂ)

theorem cartesianRow_eq_zero {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {H δ : ℝ} {j l : ℕ} (hn : ¬ Occupied N t c cs H δ j l) (q : ℕ) :
    cartesianRow N t c cs H δ j l q = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro y hy
  have hz : complexWeight δ j p*betaLabel N t H δ j l y = 0 := by
    by_contra h
    exact hn ⟨p,hp,y,hy,h⟩
  rw [hz,zero_mul]

/-- The original AP-minus-exact-q-coprime mean reaches the SAME rectangle.
No absolute values, multiplicity deletion or residue replacement occurs here. -/
theorem cartesianRow_eq_character {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ) (hM : 1 ≤ lower δ j)
    (ho : Occupied N t c cs H δ j l) {q : ℕ}
    (hq : 0 < q) (hNq : N.Coprime q) :
    cartesianRow N t c cs H δ j l q =
      rectangleCharacterDiscrepancy
        (actualAlpha N t c δ j) (actualBeta N t c cs H δ j l)
        0 0 (Nat.floor (2*lower δ j)) (Nat.floor (2*lower δ l)) q
        ((N : ZMod q)⁻¹) := by
  obtain ⟨hS,hT⟩ := actual_rows_supported ht hδ hwidth j l ho
  calc
    _ = ∑ x ∈ rootLabels N t (c::cs),
        (complexWeight δ j (labelHead x)*
          betaLabel N t H δ j l (labelComplement x))*
            (gammaKernel N q (product (t.1*t.2) x) : ℂ) :=
      (original_retained_row_eq_cartesian ht c cs hδ j l
        (fun m => (gammaKernel N q m : ℂ))).symm
    _ = naturalRectangleDiscrepancy
        (actualPrimeCarrier N t c δ j)
        (retainedComplementSupport N t c cs H δ j l)
        (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q := by
      simpa only [naturalRectangleDiscrepancy,Nat.mul_comm] using
        original_retained_row_eq_actual_rows ht hδ hwidth j l hM ho
          (fun m => (gammaKernel N q m : ℂ))
    _ = _ := naturalRectangleDiscrepancy_eq_character _ _ _ _ _ _ N q hS hT hq hNq

/-- Finite signed attachment. The support, target coprimality, coefficient
height and complete-scale post-loss cap are supplied by the actual rho. -/
theorem signed_row_le_local_conductor {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hN : 2 ≤ N) (ht : t ∈ pairSupport N) {kappa δ nu epsilon : ℝ}
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100)
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1/1000)
    (j l : ℕ) (hM : 1 ≤ lower δ j)
    (ho : Occupied N t c cs (2*(N : ℝ)^(1-kappa)) δ j l)
    (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ) :
    ‖∑ q ∈ Q, (upperRho N nu epsilon retain cap q : ℂ)*
      cartesianRow N t c cs (2*(N : ℝ)^(1-kappa)) δ j l q‖ ≤
      ∑ q ∈ Finset.Icc 1 (localModulusCap (lower δ j*lower δ l)),
        ‖rectangleCharacterDiscrepancy
          (actualAlpha N t c δ j)
          (actualBeta N t c cs (2*(N : ℝ)^(1-kappa)) δ j l)
          0 0 (Nat.floor (2*lower δ j)) (Nat.floor (2*lower δ l)) q
          ((N : ZMod q)⁻¹)‖ := by
  let I := Finset.Icc 1 (localModulusCap (lower δ j*lower δ l))
  let R := fun q => rectangleCharacterDiscrepancy
    (actualAlpha N t c δ j)
    (actualBeta N t c cs (2*(N : ℝ)^(1-kappa)) δ j l)
    0 0 (Nat.floor (2*lower δ j)) (Nat.floor (2*lower δ l)) q
    ((N : ZMod q)⁻¹)
  calc
    _ ≤ ∑ q ∈ Q, ‖(upperRho N nu epsilon retain cap q : ℂ)*
        cartesianRow N t c cs (2*(N : ℝ)^(1-kappa)) δ j l q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, if q ∈ I then ‖R q‖ else 0 := by
      apply Finset.sum_le_sum
      intro q hqQ
      by_cases hr : upperRho N nu epsilon retain cap q = 0
      · simp only [hr,Complex.ofReal_zero,zero_mul,norm_zero]
        split_ifs <;> positivity
      · obtain ⟨hq,hsq,hcop,hrbound,hlt,hcap⟩ :=
          occupied_actual_rank_two_postloss hN ht hk0 hk hδ hwidth
            hnu hnu1 heps heps1 ho retain cap hr
        have hqI : q ∈ I := Finset.mem_Icc.mpr ⟨by omega,hcap⟩
        have hnorm : ‖(upperRho N nu epsilon retain cap q : ℂ)‖ ≤ 1 := by
          simpa only [Complex.norm_real,Real.norm_eq_abs,upperRho] using hrbound
        rw [if_pos hqI,norm_mul,cartesianRow_eq_character ht hδ hwidth j l hM ho hq hcop.symm]
        exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _)
    _ = ∑ q ∈ Q.filter (fun q => q ∈ I), ‖R q‖ := by rw [Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun q hq => (Finset.mem_filter.mp hq).2) (fun q _ _ => norm_nonneg _)

/-- One original-N threshold precedes every actual mother, pair, chart,
finite modulus subfamily, retain/cap policy and allowed nu/epsilon. The
local conductor theorem is INVOKED; no analytic estimate is an input. -/
theorem exists_chosen_signed_rows (A B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ t ∈ pairSupport N, ∀ i ∈ secondFunctionalMotherPrefixIndices,
      ∀ c : ℕ, ∀ cs : List ℕ, (c::cs) ∈ secondFunctionalMotherGammaWords i →
      ∀ j l : ℕ, ∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ),
      ‖∑ q ∈ Q, (upperRho N nu epsilon retain cap q : ℂ)*
        cartesianRow N t c cs (2*(N : ℝ)^(1-kappa))
          (boundaryLogMesh B N) j l q‖ ≤ C*(N : ℝ)/(Real.log (N : ℝ))^A := by
  have hk1 : kappa < 1 := by linarith
  have hbeta : 0 < 1-kappa := by linarith
  obtain ⟨C,hC,N0,hN0,hlocal⟩ :=
    exists_chosen_all_mother_local_conductor (A : ℝ) B hB kappa hk1
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk1
  refine ⟨C/(1-kappa)^A,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop N0,eventually_ge_atTop (Nat.ceil Ts),
    eventually_chosen_mesh_factor_two hB] with N hN hTsN hm
  intro t ht i hi c cs hcs j l nu epsilon hnu hnu1 heps heps1 retain cap Q
  have hN2 : 2 ≤ N := hN0.trans hN
  have hNT : Ts ≤ (N : ℝ) := (Nat.le_ceil Ts).trans (by exact_mod_cast hTsN)
  by_cases ho : Occupied N t c cs (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) j l
  · obtain ⟨hlogx,hM,hV,hMpow,hVpow,hlower,hupper,htarget⟩ :=
      hscale N hNT t ht c cs _ hm.2.1 hm.2.2 j l ho
    have hrow := signed_row_le_local_conductor hN2 ht hk0 hk hm.2.1 hm.2.2
      hnu hnu1 heps heps1 j l hM ho retain cap Q
    have han := hlocal N hN t ht i hi c cs hcs j l ho
      (fun q => (N : ZMod q)⁻¹)
    have hu := local_log_unit_le_original (A : ℝ) (1-kappa) 1 (N : ℝ)
      (lower (boundaryLogMesh B N) j*lower (boundaryLogMesh B N) l)
      (by positivity) hbeta (by norm_num)
      (by exact_mod_cast (show 1 < N by omega)) hlower (by simpa only [one_mul] using hupper)
    have htransport := mul_le_mul_of_nonneg_left hu hC.le
    simp only [Real.rpow_natCast] at han htransport
    exact hrow.trans (han.trans (by convert htransport using 1 <;> ring))
  · have hz : (∑ q ∈ Q, (upperRho N nu epsilon retain cap q : ℂ)*
        cartesianRow N t c cs (2*(N : ℝ)^(1-kappa))
          (boundaryLogMesh B N) j l q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      rw [cartesianRow_eq_zero ho q,mul_zero]
    rw [hz,norm_zero]
    have hlog : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hm.1
    positivity

end
end ImbalancedChen.P2GammaRetainedSameRhoRows
