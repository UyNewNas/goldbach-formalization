import ImbalancedChen.Part5OriginalH430ArithmeticParentMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal atom rows for the arithmetic W1/W2 profiles, followed by their
same-Q parent-Theta normalization. Every knot atom remains in the finite
sum. This supplies actual nonnegative coefficients and their row norm;
it does not supply a full-Member source equality, immutable430 bases,
or a common smooth refinement of the 441-generation physical graph.
-/

namespace ImbalancedChen.Part5OriginalH430ArithmeticAtomRows

noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open Part5OriginalH430ArithmeticParentMass
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalBankOldProfilePassage P2OriginalProfileThetaNormalization
open P2OriginalLiteralW1OldProfile P2OriginalPositiveSameQMassLift

/-- Upper atoms and lower atoms are different occurrences. -/
abbrev RowAtom := FloorAtom ⊕ FloorAtom

def oldAtomValue (oldH oldh : Fin 200 → ℤ) : RowAtom → ℝ
  | .inl b => floorAtomValue oldH b
  | .inr b => floorAtomValue oldh b

def pointAtom (theta : ℝ) (lower : Bool) (s : ℝ) (b : FloorAtom) : ℝ :=
  theta * (tableAtomSet lower b).indicator (fun _ => 1) s

def W1ChildAtom (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (b : FloorAtom) : ℝ :=
  profileAtomSum (P2EnhancedActualBuchstabTransfer.childWindow N d Q (W1Target i) (W1Anchor j))
    id (fun p => thetaAtom N Q (d*p)) univ true
    (fun p : ℕ => W1Anchor j*(1-Real.log (p:ℝ)/Real.log (Q/d))) b

def singleChildAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (lo hi s0 : ℝ)
    (b : FloorAtom) : ℝ :=
  profileAtomSum (actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5))
    (normalizedLog N L) (fun p => thetaAtom N Q (d*p 0))
    (singleHalf lo hi) true (singleRho s0) b

def pairChildAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (k : Fin 4)
    (b : FloorAtom) : ℝ :=
  profileAtomSum (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5))
    (normalizedLog N L) (fun q => thetaAtom N Q (d*q 0*q 1))
    (pairHalf p k) false (pairProfile p k) b

/-- Point multiplicities and every good-pair/singleton occurrence are
kept before atomization; alternatives are not summed here. -/
def arithmeticRow (N : ℕ) (Q L : ℝ) (d : ℕ) : Original106Action → RowAtom → ℝ
  | .inl (i,j), .inl b => pointAtom (thetaAtom N Q d) false (W1Anchor j) b
  | .inl (i,j), .inr b => W1ChildAtom N Q d i j b/2
  | .inr j, .inl b =>
      (4*pointAtom (thetaAtom N Q d) false (originalW2At j).s0 b +
        pointAtom (thetaAtom N Q d) false (originalW2At j).phi1 b +
        ∑ k : Fin 4, pairChildAtom N Q L d (originalW2At j) k b)/5
  | .inr j, .inr b =>
      (∑ k : Fin 3, singleChildAtom N Q L d (a0 (originalW2At j))
        (singletonTop (originalW2At j) k) (originalW2At j).s0 b)/5

theorem pointAtom_value (theta : ℝ) (lower : Bool) (s : ℝ) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, pointAtom theta lower s b*floorAtomValue nums b) =
      theta*tableFunction lower nums s := by
  rw [tableFunction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : s ∈ tableAtomSet lower b <;> simp [pointAtom, hb]

theorem W1ChildAtom_value (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10)
    (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, W1ChildAtom N Q d i j b*floorAtomValue nums b) =
      ∑ p ∈ P2EnhancedActualBuchstabTransfer.childWindow N d Q (W1Target i) (W1Anchor j),
        thetaAtom N Q (d*p)*tableFunction true nums
          (W1Anchor j*(1-Real.log (p:ℝ)/Real.log (Q/d))) := by
  have h := profileSum_eq_atoms
    (P2EnhancedActualBuchstabTransfer.childWindow N d Q (W1Target i) (W1Anchor j))
    id (fun p => thetaAtom N Q (d*p)) univ true nums
    (fun p : ℕ => W1Anchor j*(1-Real.log (p:ℝ)/Real.log (Q/d)))
  simpa only [profileSum, W1ChildAtom, indicator_univ, id_eq, mul_comm] using h.symm

theorem singleChildAtom_value (N : ℕ) (Q L : ℝ) (d : ℕ) (lo hi s0 : ℝ)
    (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, singleChildAtom N Q L d lo hi s0 b*floorAtomValue nums b) =
      singleThetaOldProfile N Q L d lo hi s0 true nums := by
  have h := profileSum_eq_atoms
    (actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5))
    (normalizedLog N L) (fun p => thetaAtom N Q (d*p 0))
    (singleHalf lo hi) true nums (singleRho s0)
  calc
    _ = profileSum
        (actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5))
        (normalizedLog N L) (fun p => thetaAtom N Q (d*p 0))
        (singleHalf lo hi) true nums (singleRho s0) := by
      simpa only [singleChildAtom, mul_comm] using h.symm
    _ = _ := by
      unfold profileSum singleThetaOldProfile
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : normalizedLog N L p ∈ singleHalf lo hi <;>
        simp [hp, mul_comm]

theorem pairChildAtom_value (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters)
    (k : Fin 4) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, pairChildAtom N Q L d p k b*floorAtomValue nums b) =
      pairThetaOldProfile N Q L d p k nums := by
  have h := profileSum_eq_atoms
    (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5))
    (normalizedLog N L) (fun q => thetaAtom N Q (d*q 0*q 1))
    (pairHalf p k) false nums (pairProfile p k)
  calc
    _ = profileSum
        (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5))
        (normalizedLog N L) (fun q => thetaAtom N Q (d*q 0*q 1))
        (pairHalf p k) false nums (pairProfile p k) := by
      simpa only [pairChildAtom, mul_comm] using h.symm
    _ = _ := by
      unfold profileSum pairThetaOldProfile
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : normalizedLog N L q ∈ pairHalf p k <;> simp [hq, mul_comm]

/-- Literal coefficient identity, valid for arbitrary old arrays, including
their adjacent minima on every closed knot. -/
theorem arithmeticRow_value (N : ℕ) (Q L : ℝ) (d : ℕ)
    (oldH oldh : Fin 200 → ℤ) (a : Original106Action) :
    (∑ b : RowAtom, arithmeticRow N Q L d a b*oldAtomValue oldH oldh b) =
      arithmeticProfile N Q L d oldH oldh a := by
  rcases a with ⟨i,j⟩ | j
  · simp only [Fintype.sum_sum_type, arithmeticRow, oldAtomValue, arithmeticProfile]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div, pointAtom_value, W1ChildAtom_value]
    rfl
  · have hp : (∑ b : FloorAtom,
        (∑ k : Fin 4, pairChildAtom N Q L d (originalW2At j) k b)*floorAtomValue oldH b) =
        ∑ k : Fin 4, pairThetaOldProfile N Q L d (originalW2At j) k oldH := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [pairChildAtom_value]
    have hs : (∑ b : FloorAtom,
        (∑ k : Fin 3, singleChildAtom N Q L d (a0 (originalW2At j))
          (singletonTop (originalW2At j) k) (originalW2At j).s0 b)*floorAtomValue oldh b) =
        ∑ k : Fin 3, singleThetaOldProfile N Q L d (a0 (originalW2At j))
          (singletonTop (originalW2At j) k) (originalW2At j).s0 true oldh := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [singleChildAtom_value]
    simp only [Fintype.sum_sum_type, arithmeticRow, oldAtomValue, arithmeticProfile]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div, Finset.sum_div]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [pointAtom_value, pointAtom_value, hp, hs]
    unfold W2ThetaOldProfile
    ring

theorem arithmeticRow_sum (N : ℕ) (Q L : ℝ) (d : ℕ) (a : Original106Action) :
    (∑ b : RowAtom, arithmeticRow N Q L d a b) =
      arithmeticProfile N Q L d oneNumerators oneNumerators a := by
  have h := arithmeticRow_value N Q L d oneNumerators oneNumerators a
  have hv (b : RowAtom) : oldAtomValue oneNumerators oneNumerators b = 1 := by
    cases b <;> exact one_floorAtomValue _
  simpa only [hv, mul_one] using h

theorem pointAtom_nonneg {theta : ℝ} (htheta : 0 ≤ theta)
    (lower : Bool) (s : ℝ) (b : FloorAtom) : 0 ≤ pointAtom theta lower s b := by
  unfold pointAtom
  exact mul_nonneg htheta (by by_cases hb : s ∈ tableAtomSet lower b <;> simp [hb])

theorem profileAtomSum_nonneg {ι X : Type*} (T : Finset ι) (x : ι → X)
    (w : ι → ℝ) (D : Set X) (lower : Bool) (rho : X → ℝ) (b : FloorAtom)
    (hw : ∀ a ∈ T, x a ∈ D → 0 ≤ w a) :
    0 ≤ profileAtomSum T x w D lower rho b := by
  apply Finset.sum_nonneg
  intro a ha
  by_cases hx : x a ∈ D ∩ tablePullback lower rho b
  · rw [indicator_of_mem hx]
    exact hw a ha hx.1
  · rw [indicator_of_notMem hx]

theorem single_arithmetic_child_nonneg {N d : ℕ} {Q L : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) {p : Fin 1 → ℕ}
    (hp : p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5))
    (hu : normalizedLog N L p 0 ≤ 1/2) : 0 ≤ thetaAtom N Q (d*p 0) := by
  have hN1 : 1 < N := by omega
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have hp2 : 2 < p 0 := by
    have hh : (4:ℝ) ≤ p 0 := hA.trans hp0.2.2.1
    exact_mod_cast (show (2:ℝ) < p 0 by linarith)
  have hR := sameQ_residual_gt_one hN1 hd hL hQ
  rw [thetaAtom_single (by omega) hd hp0.1 hp2
    (hp0.1.coprime_iff_not_dvd.mpr hp0.2.1) hR]
  apply mul_nonneg (thetaAtom_nonneg hN hd hR)
  have he : Real.log (p 0:ℝ)/Real.log (Q/d) = normalizedLog N L p 0 := by
    rw [hQ]
    exact physical_log_ratio hN1 hd hL p 0
  rw [he]
  exact div_nonneg (localPrimeFactor_pos (by exact_mod_cast hp2)).le (by linarith)

theorem pair_arithmetic_child_nonneg {N d : ℕ} {Q L : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) {q : Fin 2 → ℕ}
    (hq : q ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5))
    (hx : normalizedLog N L q ∈ pairHalf p k) : 0 ≤ thetaAtom N Q (d*q 0*q 1) := by
  have hN1 : 1 < N := by omega
  have hq0 := mem_actualPrimeBoxTuples_iff.mp hq 0
  have hq1 := mem_actualPrimeBoxTuples_iff.mp hq 1
  have hq02 : 2 < q 0 := by
    have hh : (4:ℝ) ≤ q 0 := hA.trans hq0.2.2.1
    exact_mod_cast (show (2:ℝ) < q 0 by linarith)
  have hq12 : 2 < q 1 := by
    have hh : (4:ℝ) ≤ q 1 := hA.trans hq1.2.2.1
    exact_mod_cast (show (2:ℝ) < q 1 by linarith)
  have hR := sameQ_residual_gt_one hN1 hd hL hQ
  rw [thetaAtom_pair (by omega) hd hq0.1 hq1.1 hq02 hq12
    (hq0.1.coprime_iff_not_dvd.mpr hq0.2.1) (hq1.1.coprime_iff_not_dvd.mpr hq1.2.1) hR]
  have he (i : Fin 2) : Real.log (q i:ℝ)/Real.log (Q/d) = normalizedLog N L q i := by
    rw [hQ]
    exact physical_log_ratio hN1 hd hL q i
  rw [he 0, he 1]
  exact mul_nonneg (thetaAtom_nonneg hN hd hR) (div_nonneg
    (mul_nonneg (localPrimeFactor_pos (by exact_mod_cast hq02)).le
      (localPrimeFactor_pos (by exact_mod_cast hq12)).le)
    (le_trans (by norm_num) (pairHalf_geometry hp k hx).2.1))

theorem W1ChildAtom_nonneg {N d : ℕ} {Q L : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (i : Fin 7) (j : Fin 10) (b : FloorAtom) :
    0 ≤ W1ChildAtom N Q d i j b := by
  apply profileAtomSum_nonneg
  intro p hp _
  have hN1 : 1 < N := by omega
  have hNR : (1:ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hlo,hhi,_⟩ := W1_endpoints i j
  have hcut (s : ℝ) : P2EnhancedTwentyOneSameQWeighted.cutoff Q d s =
      (N:ℝ)^(L*(1/s)) := by
    rw [cutoff_eq_physical_power hd hQ]
    congr 1
    ring
  rw [P2EnhancedActualBuchstabTransfer.childWindow, hcut, hcut] at hp
  have hpm := mem_primeWindow.mp hp
  have hpN := (Nat.coprime_mul_iff_right.mp hpm.2.1).2
  have hfloor : (N:ℝ)^(L/10) ≤ (N:ℝ)^(L*(1/W1Anchor j)) :=
    Real.rpow_le_rpow_of_exponent_le hNR.le (by nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hlo)])
  have hp2 : 2 < p := by
    have hh : (4:ℝ) ≤ p := hA.trans (hfloor.trans hpm.2.2.1)
    exact_mod_cast (show (2:ℝ) < p by linarith)
  have hx := (normalizedLog_window hN1 hL (fun _ : Fin 1 => p)
    (fun _ => hpm.1.pos) 0 (1/W1Anchor j) (1/W1Target i)).mpr
      ⟨hpm.2.2.1, hpm.2.2.2⟩
  have hR := sameQ_residual_gt_one hN1 hd hL hQ
  rw [thetaAtom_single (by omega) hd hpm.1 hp2 hpN hR]
  have he : Real.log (p:ℝ)/Real.log (Q/d) = normalizedLog N L (fun _ : Fin 1 => p) 0 := by
    rw [hQ]
    exact physical_log_ratio hN1 hd hL (fun _ : Fin 1 => p) 0
  rw [he]
  exact mul_nonneg (thetaAtom_nonneg hN hd hR)
    (div_nonneg (localPrimeFactor_pos (by exact_mod_cast hp2)).le (by linarith [hx.2]))

theorem arithmeticRow_nonneg {N d : ℕ} {Q L : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (a : Original106Action) (b : RowAtom) :
    0 ≤ arithmeticRow N Q L d a b := by
  have ht := thetaAtom_nonneg hN hd (sameQ_residual_gt_one (by omega) hd hL hQ)
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b => exact pointAtom_nonneg ht false _ b
    | inr b => exact div_nonneg (W1ChildAtom_nonneg hN hd hL hA hQ i j b) (by norm_num)
  · have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    cases b with
    | inl b =>
        apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 5)
        apply add_nonneg (add_nonneg
          (mul_nonneg (by norm_num) (pointAtom_nonneg ht false _ b))
          (pointAtom_nonneg ht false _ b))
        apply Finset.sum_nonneg
        intro k _
        apply profileAtomSum_nonneg
        intro q hq hx
        exact pair_arithmetic_child_nonneg hN hd hL hA hQ hg k hq hx
    | inr b =>
        apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 5)
        apply Finset.sum_nonneg
        intro k _
        apply profileAtomSum_nonneg
        intro p hp hx
        exact single_arithmetic_child_nonneg hN hd hL hA hQ hp
          (hx.2.le.trans (W2_singleton_top hg k))

def parentRow {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ) (a : ι → Original106Action)
    (b : RowAtom) : ℝ := ∑ i ∈ S, sigma i*arithmeticRow N Q (L i) (d i) (a i) b

def normalizedParentRow {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ) (a : ι → Original106Action)
    (b : RowAtom) : ℝ := parentRow N Q S L d sigma a b / parentTheta N Q S d sigma

theorem parentRow_sum {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ) (a : ι → Original106Action) :
    (∑ b : RowAtom, parentRow N Q S L d sigma a b) =
      ∑ i ∈ S, sigma i*arithmeticProfile N Q (L i) (d i) oneNumerators oneNumerators (a i) := by
  simp only [parentRow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, arithmeticRow_sum]

/-- Genuine arithmetic hw/hmass for these 106 carrier rows, including
absolute vanishing before division on a zero-Theta family. This is not
an assertion that all immutable430 history rows have been identified. -/
theorem all106_normalized_parent_rows {Lmin Lmax : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ) (a : ι → Original106Action),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ P2OriginalChildPhysicalNormalization.alpha
        (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      (∀ b, 0 ≤ normalizedParentRow N Q S L d sigma a b) ∧
      (∑ b : RowAtom, normalizedParentRow N Q S L d sigma a b) ≤ 12 ∧
      (parentTheta N Q S d sigma = 0 → ∀ b, parentRow N Q S L d sigma a b = 0) := by
  obtain ⟨Tm,hm⟩ := all106_parentTheta_mass_le_twelve hmin hmax
  obtain ⟨Ta,ha⟩ := P2OriginalCompactThetaMass.compact_multiplier_error (k := 1)
    hmin hmax (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
  refine ⟨max 4 (max Tm Ta), ?_⟩
  intro N hN Q ι S L d sigma a hL hd hQ hsigma halpha
  have hN4 : 4 ≤ N := by omega
  have hR (i) (hi : i ∈ S) : 1 < Q/(d i:ℝ) :=
    sameQ_residual_gt_one (by omega) (hd i hi) (hmin.trans_le (hL i hi).1) (hQ i hi)
  have ht := parentTheta_nonneg hN4 Q S d sigma hd hsigma hR
  have hw (b : RowAtom) : 0 ≤ parentRow N Q S L d sigma a b := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hsigma i hi) (arithmeticRow_nonneg hN4 (hd i hi)
      (hmin.trans_le (hL i hi).1) (ha N (by omega) (L i) (hL i hi)).1
      (hQ i hi) (a i) b)
  have hmass : (∑ b : RowAtom, parentRow N Q S L d sigma a b) ≤
      12*parentTheta N Q S d sigma := by
    rw [parentRow_sum]
    exact hm N (by omega) Q S L d sigma a hL hd hQ hsigma halpha
  refine ⟨fun b => div_nonneg (hw b) ht, ?_, ?_⟩
  · simp only [normalizedParentRow, ← Finset.sum_div]
    by_cases hz : parentTheta N Q S d sigma = 0
    · simp only [hz, div_zero]
      norm_num
    · exact (div_le_iff₀ (lt_of_le_of_ne ht (Ne.symm hz))).mpr hmass
  · intro hz b
    have hs : parentRow N Q S L d sigma a b ≤
        ∑ c : RowAtom, parentRow N Q S L d sigma a c :=
      Finset.single_le_sum (fun c _ => hw c) (Finset.mem_univ b)
    rw [hz, mul_zero] at hmass
    exact le_antisymm (hs.trans hmass) (hw b)

end
end ImbalancedChen.Part5OriginalH430ArithmeticAtomRows
