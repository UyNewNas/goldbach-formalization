import ImbalancedChen.P1OriginalFifthPositiveStratumMass
import ImbalancedChen.P1OriginalFourthMovingPrimeIntervalBound

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A genuinely moving middle-shell bound on the unchanged original rank-four
first-exit fifth carrier. The shell keeps its lower cutoff delta, selected
fifth mesh cell, first-stop gates and third-parent cube gates. Its natural
reciprocal index is floor(a/t5), with no residual-floor multiplicity.

The last two primes are bounded together. Strict original order p4>p5
places p4 above the same moving lower endpoint as p5. The moving inverse
Euler-product theorem bounds that p4 interval by C/t5. A SECOND power of
t5 pays for this loss and leaves the summable last-prime bin estimate.
The prime-interval constant is selected before N, delta, a and the bin.

Only a single-bin quadratic moment is proved here. Summation over occupied
indices and conversion of the actual source envelope to this moment remain
separate obligations; no whole remainder estimate is assumed.
-/

namespace ImbalancedChen.P1OriginalFifthMiddleShellBinMoment

noncomputable section
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthWeightedSourceReduction
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFourthMovingPrimeIntervalBound

abbrev Tuple := Fin 5 → ℕ

def shellCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (N cap : ℕ) (j : Label5 m) : Finset Tuple :=
  (sourceCarrier e chi m omega N cap).filter fun p =>
    delta ≤ actualPrimeTupleLog N p 4 ∧ actualPrimeTupleLog N p 4 < a ∧
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19/96) m j

def owner (a : ℝ) (N : ℕ) (p : Tuple) : ℕ :=
  ⌊a / actualPrimeTupleLog N p 4⌋₊

def shellBin (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (N cap : ℕ) (j : Label5 m) (r : ℕ) : Finset Tuple :=
  (shellCell e chi m omega delta a N cap j).filter fun p => owner a N p = r

def binLo (omega a : ℝ) (r : ℕ) : Fin 5 → ℝ :=
  ![omega,omega,omega,a/((r:ℝ)+1),a/((r:ℝ)+1)]

def binHi (a : ℝ) (r : ℕ) : Fin 5 → ℝ :=
  ![19/96,19/96,19/96,19/96,
    a/(r:ℝ)+a/((r:ℝ)*((r:ℝ)+1))]

def quadraticMoment (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (N cap : ℕ) (j : Label5 m) (r : ℕ) : ℝ :=
  ∑ p ∈ shellBin e chi m omega delta a N cap j r,
    (∏ i, 1/((p i:ℝ)-1)) * (actualPrimeTupleLog N p 4)^2

/-- Elementary ownership bounds at the actual fifth prime. -/
theorem owner_bounds (a t : ℝ) (ht : 0 < t) (hta : t < a) (r : ℕ)
    (hr : ⌊a/t⌋₊ = r) :
    1 ≤ r ∧ a/((r:ℝ)+1) < t ∧ t ≤ a/(r:ℝ) := by
  have ha : 0 < a := ht.trans hta
  have hratio : (1:ℝ) ≤ a/t := (one_le_div ht).mpr hta.le
  have hr1 : 1 ≤ r := by
    rw [← hr]
    exact (Nat.one_le_floor_iff _).mpr hratio
  have hrpos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hfloor : (r:ℝ) ≤ a/t := by
    rw [← hr]
    exact Nat.floor_le (div_nonneg ha.le ht.le)
  have hnext : a/t < (r:ℝ)+1 := by
    simpa only [hr] using Nat.lt_floor_add_one (a/t)
  refine ⟨hr1,?_,?_⟩
  · apply (div_lt_iff₀ (by linarith : (0:ℝ)<(r:ℝ)+1)).mpr
    nlinarith [(div_lt_iff₀ ht).mp hnext]
  · apply (le_div_iff₀ hrpos).mpr
    nlinarith [(le_div_iff₀ ht).mp hfloor]

/-- The actual selected T3 carrier embeds in a box with THREE fixed
rough coordinates and TWO genuinely moving coordinates. -/
theorem shellBin_subset_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ) (ha : 0<a)
    (J5 : Finset (Label5 m)) (N cap : ℕ) (hN : 1<N)
    (hcap : (N:ℝ)^(19/96:ℝ) ≤ (cap:ℝ))
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) (r : ℕ) :
    shellBin e chi m omega delta a N cap j r ⊆
      actualPrimeBoxTuples N (binLo omega a r) (binHi a r) := by
  intro p hp
  obtain ⟨hpS,howner⟩ := Finset.mem_filter.mp hp
  obtain ⟨hcarrier,_hdelta,hta,htcell⟩ := Finset.mem_filter.mp hpS
  have hc : p ∈ candidates (e:ℝ) chi m omega N cap := by
    simpa only [sourceCarrier,candidates] using hcarrier
  have hd := (mem_candidates_iff_log_on_cell (e:ℝ) chi m omega
    N cap hN hcap p j htcell).mp hc
  have hanti := ((mem_jointRegion (e:ℝ) chi m omega j _).mp hd.2).2.1
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hpos (i : Fin 5) : 0 < actualPrimeTupleLog N p i := by
    have hp1 : (1:ℝ)<p i := by exact_mod_cast (hd.1 i).1.one_lt
    exact div_pos (Real.log_pos hp1) (Real.log_pos hn)
  have hcuts := owner_bounds a _ (hpos 4) hta r howner
  have hthird := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi m omega J5 j hj htcell
  have hu (i : Fin 5) : actualPrimeTupleLog N p i < (19/96:ℝ) := by
    have h := (hd.1 i).2.2.2
    rw [← actualPrimeTupleLog_rpow hN p (fun k => (hd.1 k).1.pos) i] at h
    exact (Real.rpow_lt_rpow_left_iff hn).mp h
  have hrpos : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hextra : 0<a/((r:ℝ)*((r:ℝ)+1)) := by positivity
  apply (mem_actualPrimeBoxTuples_log_iff hN (binLo omega a r) (binHi a r) p).mpr
  refine ⟨fun i => ⟨(hd.1 i).1,(hd.1 i).2.1⟩,mem_logPrimeBox.mpr ?_⟩
  intro i
  fin_cases i
  · exact ⟨hthird.trans (hanti (by decide : (0:Fin 5)<2)).le,hu 0⟩
  · exact ⟨hthird.trans (hanti (by decide : (1:Fin 5)<2)).le,hu 1⟩
  · exact ⟨hthird,hu 2⟩
  · exact ⟨hcuts.2.1.le.trans (hanti (by decide : (3:Fin 5)<4)).le,hu 3⟩
  · exact ⟨hcuts.2.1.le,hcuts.2.2.trans_lt (lt_add_of_pos_right _ hextra)⟩

/-- A finite bound for the unweighted fourth-prime interval. Its lower
endpoint may move with the terminal reciprocal index. -/
theorem penultimate_mass_le_linear_index
    (K : ℝ) (hKpos : 0≤K)
    (hK : ∀ (N cap : ℕ), Even N → ∀ w z : ℝ, 2≤w → w≤z →
      (∑ p ∈ roughPrimeFinset N cap w z,1/((p:ℝ)-1)) ≤
        Real.log z/Real.log w*(1+K/Real.log w)-1)
    (N : ℕ) (hN : 1<N) (hEven : Even N)
    (a : ℝ) (ha : 0<a) (haRho : a≤(19/96:ℝ)) (r : ℕ) (hr : 1≤r)
    (hlow : 2≤(N:ℝ)^(a/((r:ℝ)+1))) :
    (a/(r:ℝ))*actualPrimeReciprocalMass N (a/((r:ℝ)+1)) (19/96:ℝ) ≤
      2*((19/96:ℝ)*(1+K/Real.log 2)) := by
  have hr1 : (1:ℝ)≤r := by exact_mod_cast hr
  have hr0 : (0:ℝ)<r := by linarith
  have hrp : (0:ℝ)<(r:ℝ)+1 := by linarith
  have hl : 0<a/((r:ℝ)+1) := div_pos ha hrp
  have hla : a/((r:ℝ)+1) ≤ a := by
    apply (div_le_iff₀ hrp).mpr
    nlinarith
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlogN : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hloglow : Real.log 2 ≤ Real.log ((N:ℝ)^(a/((r:ℝ)+1))) :=
    Real.log_le_log (by norm_num) hlow
  have hcorr : 1+K/Real.log ((N:ℝ)^(a/((r:ℝ)+1))) ≤ 1+K/Real.log 2 := by
    exact add_le_add_left (div_le_div_of_nonneg_left hKpos hlog2 hloglow) 1
  have hbound := actualPrimeReciprocalMass_le_moving_ratio K hK N hEven
    (a/((r:ℝ)+1)) (19/96:ℝ) hlow (hla.trans haRho) hN
  have hratio : Real.log ((N:ℝ)^(19/96:ℝ)) /
      Real.log ((N:ℝ)^(a/((r:ℝ)+1))) = (19/96:ℝ)*((r:ℝ)+1)/a := by
    rw [Real.log_rpow hn,Real.log_rpow hn]
    field_simp [hrp.ne',ha.ne',hlogN.ne']
    ring
  have hmass : actualPrimeReciprocalMass N (a/((r:ℝ)+1)) (19/96:ℝ) ≤
      ((19/96:ℝ)*(1+K/Real.log 2))*((r:ℝ)+1)/a := by
    rw [hratio] at hbound
    have hratio0 : 0≤(19/96:ℝ)*((r:ℝ)+1)/a := by positivity
    have hh := mul_le_mul_of_nonneg_left hcorr hratio0
    nlinarith
  have hC : 0≤(19/96:ℝ)*(1+K/Real.log 2) := by positivity
  calc
    _ ≤ (a/(r:ℝ))*(((19/96:ℝ)*(1+K/Real.log 2))*((r:ℝ)+1)/a) :=
      mul_le_mul_of_nonneg_left hmass (div_nonneg ha.le hr0.le)
    _ = ((19/96:ℝ)*(1+K/Real.log 2))*(((r:ℝ)+1)/(r:ℝ)) := by
      field_simp [ha.ne',hr0.ne']
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply (div_le_iff₀ hr0).mpr
      linarith

/-- True quadratic t5 moment of ONE occupied original shell bin. No
arithmetic pointwise estimate or prime mean is a hypothesis. -/
theorem exists_uniform_original_shell_quadratic_bin_bound :
    ∃ K : ℝ, 1<K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ), 0<a → a≤(19/96:ℝ) →
      ∀ (J5 : Finset (Label5 m)) (N cap : ℕ), 1<N → Even N →
      (N:ℝ)^(19/96:ℝ)≤(cap:ℝ) → ∀ (j : Label5 m),
      j ∈ selectedFifthCells e chi m omega J5 → ∀ (r : ℕ), 1≤r →
      2≤(N:ℝ)^(a/((r:ℝ)+1)) →
      quadraticMoment e chi m omega delta a N cap j r ≤
        (actualPrimeReciprocalMass N omega (19/96:ℝ))^3 *
          (2*((19/96:ℝ)*(1+K/Real.log 2))) *
          (2*a/(r:ℝ)^2+6*K/Real.log (N:ℝ)) := by
  obtain ⟨K,hK,hinterval⟩ := exists_uniform_reciprocal_interval_bound
  refine ⟨K,hK,?_⟩
  intro e chi m omega delta a ha haRho J5 N cap hN hEven hcap j hj r hr hlow
  let M := actualPrimeReciprocalMass N omega (19/96:ℝ)
  let V := actualPrimeReciprocalMass N (a/((r:ℝ)+1)) (19/96:ℝ)
  let W := actualPrimeReciprocalMass N (a/((r:ℝ)+1))
    (a/(r:ℝ)+a/((r:ℝ)*((r:ℝ)+1)))
  have hmass0 (lo hi : ℝ) : 0≤actualPrimeReciprocalMass N lo hi := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1:ℝ)<p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have hM : 0≤M := hmass0 _ _
  have hV : 0≤V := hmass0 _ _
  have hW : 0≤W := hmass0 _ _
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hq : 0≤a/(r:ℝ) := div_nonneg ha.le hr0.le
  have hsub := shellBin_subset_prime_box e chi m omega delta a ha
    J5 N cap hN hcap j hj r
  have hbox : quadraticMoment e chi m omega delta a N cap j r ≤
      (a/(r:ℝ))^2 * actualPrimeBoxMass N (binLo omega a r) (binHi a r) := by
    unfold quadraticMoment
    calc
      _ ≤ ∑ p ∈ shellBin e chi m omega delta a N cap j r,
          (∏ i,1/((p i:ℝ)-1))*(a/(r:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpS,how⟩ := Finset.mem_filter.mp hp
        obtain ⟨hcar,_hd,hta,ht⟩ := Finset.mem_filter.mp hpS
        have hpr := (mem_actualPrimeBoxTuples_iff.mp (hsub hp) 4).1
        have hp1 : (1:ℝ)<p 4 := by exact_mod_cast hpr.one_lt
        have htpos : 0<actualPrimeTupleLog N p 4 :=
          div_pos (Real.log_pos hp1) (Real.log_pos (by exact_mod_cast hN))
        have hb := (owner_bounds a _ htpos hta r how).2.2
        have hsq : (actualPrimeTupleLog N p 4)^2 ≤ (a/(r:ℝ))^2 :=
          pow_le_pow_left₀ htpos.le hb 2
        exact mul_le_mul_of_nonneg_left hsq (actualPrimeBoxWeight_nonneg (hsub hp))
      _ ≤ ∑ p ∈ actualPrimeBoxTuples N (binLo omega a r) (binHi a r),
          (∏ i,1/((p i:ℝ)-1))*(a/(r:ℝ))^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        exact mul_nonneg (actualPrimeBoxWeight_nonneg hp) (sq_nonneg _)
      _ = _ := by simp only [actualPrimeBoxMass,Finset.sum_mul]; ring
  have hfactor : actualPrimeBoxMass N (binLo omega a r) (binHi a r) = M^3*V*W := by
    rw [actualPrimeBoxMass_eq_prod]
    simp [Fin.prod_univ_five,binLo,binHi,M,V,W]
    ring
  rw [hfactor] at hbox
  have hpen := penultimate_mass_le_linear_index K (by linarith) hinterval
    N hN hEven a ha haRho r hr hlow
  have hlast := weighted_last_prime_interval_le_terms K (by linarith) hinterval
    N hN hEven a ha r hr hlow
  calc
    _ ≤ M^3*((a/(r:ℝ))*V)*((a/(r:ℝ))*W) := by convert hbox using 1 <;> ring
    _ ≤ M^3*(2*((19/96:ℝ)*(1+K/Real.log 2)))*((a/(r:ℝ))*W) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpen (pow_nonneg hM 3)) (mul_nonneg hq hW)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlast (by positivity)

end
end ImbalancedChen.P1OriginalFifthMiddleShellBinMoment
