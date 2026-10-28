import ImbalancedChen.P5ActualRankLogAtomEuler
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Actual lower/product support and complete fixed-rank Family fields for the
existing real log-box atom, derived from its literal endpoint licence.
The checked endpoint bank is not asserted to enumerate independent-u PP
callers. A caller owner must identify its real independent test and supply
its original licensed endpoint membership; residual-q ranks are not that
identification. No derivative-size conclusion is a premise.
-/
namespace ImbalancedChen.P5Z.LicensedLogAtomFamilySupport
noncomputable section
open Classical Set
open scoped BigOperators
open ActualRankLogAtomEuler
open PresievedRoughGateMeshReserve PresievedRoughSmoothBoxAtoms
open U1011CompactLogIntervalSmoothing
open AdmissibleAllRankIntegerGeometricFamily

/-- The numerical licence is about the original mesh endpoints after their
actual smoothing collar; it is not an assumed Family support conclusion. -/
def EndpointLicence {r n : ℕ} (aStar δ a b : ℝ) (j : Grid r n) : Prop :=
  (∀ i, aStar ≤ logPrimeMeshLo a b n j i - δ) ∧
    (∑ i, (logPrimeMeshHi a b n j i + δ)) ≤ 1

theorem atom_nonzero_upper {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (v : Fin r → ℝ)
    (hv : atom inner δ a b n j v ≠ 0) (i : Fin r) :
    v i < logPrimeMeshHi a b n j i + δ := by
  have hfac : weight inner δ (logPrimeMeshLo a b n j i)
      (logPrimeMeshHi a b n j i) (v i) ≠ 0 := by
    intro hz
    exact hv (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  have hs : 0 ≤ shift inner δ := by cases inner <;> simp [shift, hδ.le]
  have hu := P4B.smoothGateUpperStep_nonzero_support hδ (mul_ne_zero_iff.mp hfac).2
  change -δ < logPrimeMeshHi a b n j i - v i - shift inner δ at hu
  linarith

theorem profile_nonzero_log_bounds {r n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) {N : ℕ} {p : Fin r → ℝ}
    (hp : ActualRankLogAtomEuler.profile inner δ a b n j N p ≠ 0) :
    2 ≤ N ∧ (∀ i, 0 < p i) ∧ ∀ i,
      logPrimeMeshLo a b n j i - δ < Real.log (p i) / Real.log (N : ℝ) ∧
      Real.log (p i) / Real.log (N : ℝ) < logPrimeMeshHi a b n j i + δ := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hp (by simp [ActualRankLogAtomEuler.profile, h])
  have hpos : ∀ i, 0 < p i := by
    by_contra h
    exact hp (by simp [ActualRankLogAtomEuler.profile, hN, h])
  have hatom : atom inner δ a b n j
      (fun i => Real.log (p i) / Real.log (N : ℝ)) ≠ 0 := by
    simpa only [ActualRankLogAtomEuler.profile, if_pos hN, if_pos hpos] using hp
  exact ⟨hN, hpos, fun i => ⟨atom_nonzero_lower hδ inner j _ hatom i,
    atom_nonzero_upper hδ inner j _ hatom i⟩⟩

/-- The lower exponent is the licensed original endpoint minus the same
smoothing collar. The complete product bound follows by summing the actual
log coordinates, not by multiplying a tuplewise artificial cap. -/
theorem licensed_real_support {r n : ℕ} {δ a b aStar : ℝ} (hδ : 0 < δ)
    (inner : Bool) (j : Grid r n) (hj : EndpointLicence aStar δ a b j)
    {N : ℕ} {p : Fin r → ℝ}
    (hp : ActualRankLogAtomEuler.profile inner δ a b n j N p ≠ 0) :
    (∀ i, (N : ℝ) ^ aStar ≤ p i) ∧ (∏ i, p i) ≤ (N : ℝ) := by
  obtain ⟨hN, hpos, hlogbox⟩ := profile_nonzero_log_bounds hδ inner j hp
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNp : 0 < (N : ℝ) := zero_lt_one.trans hNr
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  constructor
  · intro i
    have harg : aStar < Real.log (p i) / Real.log (N : ℝ) :=
      (hj.1 i).trans_lt (hlogbox i).1
    have hl : Real.log (N : ℝ) * aStar < Real.log (p i) := by
      have h := (lt_div_iff₀ hlogN).mp harg
      simpa only [mul_comm] using h
    calc
      (N : ℝ) ^ aStar = Real.exp (Real.log (N : ℝ) * aStar) := Real.rpow_def_of_pos hNp _
      _ ≤ Real.exp (Real.log (p i)) := (Real.exp_lt_exp.mpr hl).le
      _ = p i := Real.exp_log (hpos i)
  · have hcoords (i : Fin r) : Real.log (p i) ≤
        Real.log (N : ℝ) * (logPrimeMeshHi a b n j i + δ) := by
      have h := (div_lt_iff₀ hlogN).mp (hlogbox i).2
      simpa only [mul_comm] using h.le
    have hsum : (∑ i, Real.log (p i)) ≤ Real.log (N : ℝ) := by
      calc
        (∑ i, Real.log (p i)) ≤ ∑ i,
            Real.log (N : ℝ) * (logPrimeMeshHi a b n j i + δ) :=
          Finset.sum_le_sum (fun i hi => hcoords i)
        _ = Real.log (N : ℝ) * ∑ i, (logPrimeMeshHi a b n j i + δ) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ Real.log (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hj.2 hlogN.le
        _ = Real.log (N : ℝ) := mul_one _
    calc
      (∏ i, p i) = ∏ i, Real.exp (Real.log (p i)) :=
        Finset.prod_congr rfl (fun i hi => (Real.exp_log (hpos i)).symm)
      _ = Real.exp (∑ i, Real.log (p i)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (Real.log (N : ℝ)) := Real.exp_le_exp.mpr hsum
      _ = (N : ℝ) := Real.exp_log hNp

def integerBank (r N : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ => Finset.Icc 1 N)

theorem licensed_coordinate_support {r n : ℕ} {δ a b aStar : ℝ}
    (hδ : 0 < δ) (hStar : 0 < aStar) (inner : Bool) (j : Grid r n)
    (hj : EndpointLicence aStar δ a b j) {N : ℕ} {p : Fin r → ℝ}
    (hp : ActualRankLogAtomEuler.profile inner δ a b n j N p ≠ 0) :
    ∀ i, 1 ≤ p i ∧ p i ≤ (N : ℝ) := by
  obtain ⟨hlo, hprod⟩ := licensed_real_support hδ inner j hj hp
  have hN := (profile_nonzero_log_bounds hδ inner j hp).1
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hone (i : Fin r) : (1 : ℝ) ≤ p i :=
    (Real.one_le_rpow hbase hStar.le).trans (hlo i)
  intro i
  refine ⟨hone i, ?_⟩
  have hrest : (1 : ℝ) ≤ ∏ s ∈ (Finset.univ : Finset (Fin r)).erase i, p s :=
    Finset.one_le_prod (fun s hs => hone s)
  calc
    p i = (1 : ℝ) * p i := (one_mul _).symm
    _ ≤ (∏ s ∈ (Finset.univ : Finset (Fin r)).erase i, p s) * p i :=
      mul_le_mul_of_nonneg_right hrest (zero_le_one.trans (hone i))
    _ = ∏ s, p s := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    _ ≤ (N : ℝ) := hprod

theorem licensed_integer_mem_bank {r n : ℕ} {δ a b aStar : ℝ}
    (hδ : 0 < δ) (hStar : 0 < aStar) (inner : Bool) (j : Grid r n)
    (hj : EndpointLicence aStar δ a b j) (N : ℕ) (u : Fin r → ℕ)
    (hu : ActualRankLogAtomEuler.profile inner δ a b n j N (fun i => (u i : ℝ)) ≠ 0) :
    u ∈ integerBank r N := by
  apply Finset.mem_piFinset.mpr
  intro i
  have hs := licensed_coordinate_support hδ hStar inner j hj hu i
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩

theorem licensed_finite_prime_support {r n : ℕ} {δ a b aStar : ℝ}
    (hδ : 0 < δ) (hStar : 0 < aStar) (inner : Bool) (j : Grid r n)
    (hj : EndpointLicence aStar δ a b j) (N : ℕ) :
    Set.Finite {u : Fin r → ℕ | (∀ i, (u i).Prime) ∧
      ActualRankLogAtomEuler.profile inner δ a b n j N (fun i => (u i : ℝ)) ≠ 0} := by
  apply (integerBank r N).finite_toSet.subset
  intro u hu
  exact licensed_integer_mem_bank hδ hStar inner j hj N u hu.2

/-- Exact original endpoint predicate, with no finite decision executed. -/
def checkedEndpointKeys (rMax n : ℕ) (aStar δ a b : ℝ) :
    Finset (AtomKey rMax n) := Finset.univ.filter
      (fun key => EndpointLicence aStar δ a b key.2.2)

theorem checkedEndpointKeys_licence {rMax n : ℕ} {aStar δ a b : ℝ}
    {key : AtomKey rMax n} (hkey : key ∈ checkedEndpointKeys rMax n aStar δ a b) :
    EndpointLicence aStar δ a b key.2.2 := (Finset.mem_filter.mp hkey).2

/-- All fixed-rank Family assertions concern the same REAL profile, not
fields of an arbitrary assumed smooth-test object. -/
structure AtomFamilyFields {r n : ℕ} (aStar δ a b : ℝ) (inner : Bool)
    (j : Grid r n) : Prop where
  exponent_pos : 0 < aStar
  smooth : ∀ N, ContDiff ℝ ∞ (ActualRankLogAtomEuler.profile inner δ a b n j N)
  support : ∀ N p, ActualRankLogAtomEuler.profile inner δ a b n j N p ≠ 0 →
    (∀ i, (N : ℝ) ^ aStar ≤ p i) ∧ (∏ i, p i) ≤ (N : ℝ)
  finitePrimeSupport : ∀ N, Set.Finite {u : Fin r → ℕ | (∀ i, (u i).Prime) ∧
    ActualRankLogAtomEuler.profile inner δ a b n j N (fun i => (u i : ℝ)) ≠ 0}
  mixedEuler : ∀ q : ℕ, ∃ C B : ℕ, 0 < C ∧ ∀ N (w : List (Fin r)) p,
    w.length ≤ q → |eulerWord w (ActualRankLogAtomEuler.profile inner δ a b n j N) p| ≤
      (C : ℝ) * Real.log ((N : ℝ) + 2) ^ B

theorem actual_licensed_atom_family {r n : ℕ} {δ a b aStar : ℝ}
    (hδ : 0 < δ) (hStar : 0 < aStar) (inner : Bool) (j : Grid r n)
    (hj : EndpointLicence aStar δ a b j) : AtomFamilyFields aStar δ a b inner j := by
  constructor
  · exact hStar
  · exact profile_global_smooth hδ inner j
  · intro N p hp
    exact licensed_real_support hδ inner j hj hp
  · exact licensed_finite_prime_support hδ hStar inner j hj
  · intro q
    obtain ⟨C, hC, hb⟩ := atom_mixedEuler hδ inner j q
    refine ⟨C, 0, hC, ?_⟩
    intro N w p hw
    simpa only [pow_zero, mul_one] using hb N w p hw

/-- A common exponent and a common ordered-Euler constant for this checked
finite geometric bank, BEFORE key, N and all independent test points. It
does not identify the bank with missing arithmetic caller/rank data. -/
theorem checked_bank_family_fields {δ a b aStar : ℝ} (hδ : 0 < δ)
    (hStar : 0 < aStar) (rMax n : ℕ) :
    (∀ key ∈ checkedEndpointKeys rMax n aStar δ a b,
      AtomFamilyFields aStar δ a b key.1 key.2.2) ∧
    ∀ q : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ key ∈ checkedEndpointKeys rMax n aStar δ a b,
      ∀ N (w : List (Fin key.2.1.val)) p, w.length ≤ q →
        |eulerWord w (ActualRankLogAtomEuler.profile key.1 δ a b n key.2.2 N) p| ≤ (C : ℝ) := by
  constructor
  · intro key hkey
    exact actual_licensed_atom_family hδ hStar key.1 key.2.2 (checkedEndpointKeys_licence hkey)
  · intro q
    obtain ⟨C, hC, hb⟩ := finite_rank_bank_mixedEuler hδ rMax n q
    exact ⟨C, hC, fun key hkey => hb key⟩

end
end ImbalancedChen.P5Z.LicensedLogAtomFamilySupport
