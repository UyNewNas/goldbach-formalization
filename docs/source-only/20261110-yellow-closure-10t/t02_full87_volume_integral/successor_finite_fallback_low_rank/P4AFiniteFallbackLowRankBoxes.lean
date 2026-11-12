import ImbalancedChen.P4AOriginalFiniteFallbackAtoms
import ImbalancedChen.P4AFallbackCanonicalBanks

/-! SOURCE_ONLY / UNCOMPILED.
The original cropped Cartesian prime slots, INCLUDING repeated labels
and repeated prime values, have a short complete modulus after either
actual beta slope. No representative replaces the full rectangle.
-/
namespace ImbalancedChen.P4AFiniteFallbackLowRankBoxes
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler (universe)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AFallbackCanonicalBanks (bank)
open P5OriginalCommonRefinedConstructor (OriginalData)

def slots (N : ℕ) (omega tau : ℝ) (J : List ℕ) : Finset (List ℕ) :=
  actualPrimeSlotBox (fun j => actualPrimeFineLabelFinset N tau j ∩
    roughPrimeFinset N N ((N : ℝ)^omega) (cutoff N)) J

theorem slots_length {N : ℕ} {omega tau : ℝ} {J ps : List ℕ} (hps : ps∈slots N omega tau J) :
    ps.length=J.length := actualPrimeSlotBox_length _ _ ps hps

/-- The original w and z crops and target deletion are kept in EVERY
slot, including the bins meeting either endpoint. -/
theorem slots_rough {N : ℕ} {omega tau : ℝ} {J ps : List ℕ} (hps : ps∈slots N omega tau J) :
    ∀ p∈ps,p∈roughPrimeFinset N N ((N : ℝ)^omega) (cutoff N) :=
  ((P4AOrderedThirdClippedFactorial.crop _ _ J ps).mp hps).2

theorem slots_prime_bounds {N : ℕ} {omega tau : ℝ} {J ps : List ℕ} (hps : ps∈slots N omega tau J) :
    ∀ p∈ps,p.Prime ∧ ¬p∣N ∧ (N : ℝ)^omega≤p ∧ (p : ℝ)<(N : ℝ)^(19/96 : ℝ) := by
  intro p hp
  exact (mem_roughPrimeFinset.mp (slots_rough hps p hp)).2

/-- Rank zero is the empty product 1; rank one and rank two use the
ENTIRE original interval ceiling, without distinctness assumptions. -/
theorem short_product_le {N : ℕ} (hN : 1≤N) (ps : List ℕ) (hlen : ps.length≤2)
    (hp : ∀ p∈ps,(p : ℝ)≤(N : ℝ)^(19/96 : ℝ)) :
    (ps.prod : ℝ)≤(N : ℝ)^(19/48 : ℝ) := by
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  let Z := (N : ℝ)^(19/96 : ℝ)
  have hZ : 1≤Z := Real.one_le_rpow hn (by norm_num)
  have hZZ : Z*Z=(N : ℝ)^(19/48 : ℝ) := by
    dsimp only [Z]
    rw [←Real.rpow_add (zero_lt_one.trans_le hn)]
    norm_num
  have hprod : (ps.prod : ℝ)≤Z*Z := by
    cases ps with
    | nil => simpa using (mul_le_mul hZ hZ (by norm_num : (0 : ℝ)≤1) (by linarith : 0≤Z))
    | cons p ps =>
      cases ps with
      | nil =>
        have h1 : (p : ℝ)≤Z := hp p (by simp)
        have h2 : Z≤Z*Z := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hZ (by linarith : 0≤Z)
        simpa using h1.trans h2
      | cons q qs =>
        have hzero : qs.length=0 := by
          simp only [List.length_cons] at hlen
          omega
        have hnil : qs=[] := List.length_eq_zero.mp hzero
        subst qs
        have h1 : (p : ℝ)≤Z := hp p (by simp)
        have h2 : (q : ℝ)≤Z := hp q (by simp)
        simpa using mul_le_mul h1 h2 (Nat.cast_nonneg q) (by linarith : 0≤Z)
  exact hprod.trans_eq hZZ

theorem beta_active {N a : ℕ} {w L : ℝ}
    (ha : actualSmallRosserPlus N N w L a≠0 ∨ actualSmallRosserMinus N N w L a≠0) :
    a∈actualSmallRosserSupport N N w ∧ (a : ℝ)<L := by
  rcases ha with ha | ha
  · exact ⟨(actualSmallRosserPlus_active ha).1,(actualSmallRosserPlus_active ha).2.1⟩
  · exact ⟨(actualSmallRosserMinus_active ha).1,(actualSmallRosserMinus_active ha).2.1⟩

/-- This is uniform over the complete beta-expanded factorial rectangle,
not just the moduli on which ALL/ANY has nonzero coefficient. -/
theorem whole_rectangle_beta_bound {N : ℕ} (hN : 1<N) (omega tau ell : ℝ)
    (hell : ell<1/1000) (J : List ℕ) (hJ : J.length≤2) (ps : List ℕ)
    (hps : ps∈slots N omega tau J) (a : ℕ)
    (ha : actualSmallRosserPlus N N ((N : ℝ)^omega) ((N : ℝ)^ell) a≠0 ∨
      actualSmallRosserMinus N N ((N : ℝ)^omega) ((N : ℝ)^ell) a≠0) :
    (a : ℝ)<(N : ℝ)^ell ∧ Nat.Coprime (a*ps.prod) N ∧
      ((a*ps.prod : ℕ) : ℝ)<(N : ℝ)^(2/5 : ℝ) := by
  have hn : (1 : ℝ)<N := by exact_mod_cast hN
  have ha' := beta_active ha
  have hprod := short_product_le (by omega : 1≤N) ps ((slots_length hps).trans_le hJ)
    (fun p hp => (slots_prime_bounds hps p hp).2.2.2.le)
  have hcop : ps.prod.Coprime N := Nat.coprime_list_prod_left_iff.mpr (fun p hp =>
    (slots_prime_bounds hps p hp).1.coprime_iff_not_dvd.mpr (slots_prime_bounds hps p hp).2.1)
  refine ⟨ha'.2,(actualSmallRosserSupport_coprime_target N N _ ha'.1).mul_left hcop,?_⟩
  calc
    ((a*ps.prod : ℕ) : ℝ) = (a : ℝ)*(ps.prod : ℝ) := by norm_cast
    _ ≤ (N : ℝ)^ell*(N : ℝ)^(19/48 : ℝ) :=
      mul_le_mul ha'.2.le hprod (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ)^(ell+19/48) := (Real.rpow_add (zero_lt_one.trans hn) _ _).symm
    _ < _ := (Real.rpow_lt_rpow_left_iff hn).mpr (by linarith)

/-- The original 1/M_J occurs exactly once. Both sides are the existing
actual coefficient, with its original target mask and clipped slots.
The short-box bound above applies to the WHOLE left-hand rectangle. -/
theorem actual_rectangular_factorial (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (hN : 1<N) (tau : ℝ) (ht : 0<tau) (J : List ℕ)
    (hJ : J.Pairwise (· ≥ ·)) (H : ℕ→ℝ) :
    let f := F (bank m) (P4AOriginalFull87HistoryCore.width r) n (P4AOriginalNewFifthUnion.data e q a) omega N
    (P4AOrderedThirdPhysicalAtoms.boxScalar f N N ((N : ℝ)^omega) (cutoff N) tau J/
      (actualPrimeFineWordMultiplicity J : ℝ))*
      (∑ ps∈slots N omega tau J,(ArithmeticFunction.moebius ps.prod : ℝ)*H ps.prod)=
      ∑ d∈((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J).filter List.SortedGT).image List.prod,
        P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N ((N : ℝ)^omega) (cutoff N) tau d*H d := by
  exact P4AOriginalFiniteFallbackAtoms.rectangular_factorial _ omega N hN tau ht J hJ H

end
end ImbalancedChen.P4AFiniteFallbackLowRankBoxes
