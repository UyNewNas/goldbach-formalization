import ImbalancedChen.Part5OriginalBuchstabCompactAtoms
import ImbalancedChen.P2OriginalPhysicalOldProfileMass
import ImbalancedChen.P2OriginalPrefixMaskMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual target-N prime sums with the exact singular-series/totient
multiplier. The literal d*N mask of the original Buchstab children is
paid using the existing prefix-mask theorem. Both endpoints of the
ambient prime window and all atom endpoints remain in their original
finite conventions. The arithmetic threshold precedes the moving start,
residual, prefix, direction and atom.
-/
namespace ImbalancedChen.Part5OriginalBuchstabTrueAtomLimits

noncomputable section
open Set Filter MeasureTheory Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalPhysicalOldProfileMass
open P2OriginalCompactThetaMass P2OriginalPrefixMaskMass
open P2OriginalChildPhysicalNormalization
open Part5OriginalBuchstabCompactAtoms P5OriginalActionMassBound
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def primeCoord (N : ℕ) (L : ℝ) (q : ℕ) : Coord 1 :=
  normalizedLog N L (fun _ : Fin 1 => q)

def atomTest (up : Bool) (b : FloorAtom) (c : ℝ) : Coord 1 → ℝ :=
  (atomDomain up b c).indicator residualSingle

def trueAtom (N : ℕ) (L : ℝ) (d : ℕ) (up : Bool) (b : FloorAtom) (c : ℝ) : ℝ :=
  trueSingleTest N L d (atomDomain up b c) residualSingle

def maskedAtom (N : ℕ) (L : ℝ) (d : ℕ) (up : Bool) (b : FloorAtom) (c : ℝ) : ℝ :=
  ∑ q ∈ primeWindow (d*N) ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5)),
    localPrimeFactor d q * atomTest up b c (primeCoord N L q)

theorem atomTest_abs_le (up : Bool) (b : FloorAtom) (c : ℝ) (x : Coord 1) :
    |atomTest up b c x| ≤ 10 :=
  indicator_abs_bound _ _ (by norm_num) (fun y => by
    rw [abs_of_nonneg (residualSingle_bounds y).1]
    exact (residualSingle_bounds y).2) x

/-- Exact one-coordinate enumeration; there is no ordering quotient or
extra factorial, and no positivity of a total marked mass is used. -/
theorem trueSingleTest_eq_window (N : ℕ) (L : ℝ) (d : ℕ)
    (D : Set (Coord 1)) (f : Coord 1 → ℝ) :
    trueSingleTest N L d D f =
      ∑ q ∈ primeWindow N ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5)),
        localPrimeFactor d q * D.indicator f (primeCoord N L q) := by
  unfold trueSingleTest
  refine Finset.sum_bij (fun p _ => p 0) ?_ ?_ ?_ ?_
  · intro p hp
    have h := mem_actualPrimeBoxTuples_iff.mp hp 0
    exact mem_primeWindow.mpr ⟨h.1,h.1.coprime_iff_not_dvd.mpr h.2.1,h.2.2⟩
  · intro p hp q hq he
    funext i
    fin_cases i
    exact he
  · intro q hq
    have h := mem_primeWindow.mp hq
    refine ⟨(fun _ : Fin 1 => q), ?_, rfl⟩
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    exact ⟨h.1,h.1.coprime_iff_not_dvd.mp h.2.1,h.2.2⟩
  · intro p hp
    have he : (fun _ : Fin 1 => p 0) = p := by
      funext i; fin_cases i; rfl
    simp only [primeCoord,he]

theorem trueAtom_eq_window (N : ℕ) (L : ℝ) (d : ℕ)
    (up : Bool) (b : FloorAtom) (c : ℝ) :
    trueAtom N L d up b c =
      ∑ q ∈ primeWindow N ((N:ℝ)^(L/10)) ((N:ℝ)^(3*L/5)),
        localPrimeFactor d q * atomTest up b c (primeCoord N L q) :=
  trueSingleTest_eq_window N L d _ _

/-- True local multipliers are paid uniformly in the entire integer
prefix; their repeated-prime branch is never changed into 1/(p-1). -/
theorem compact_uniform_true_atoms {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ c ∈ Icc (1:ℝ) 6, ∀ d : ℕ, ∀ up : Bool, ∀ b : FloorAtom,
      |trueAtom N L d up b c-normalizedAtomIntegral up b c| < epsilon := by
  obtain ⟨Tp,hp⟩ := compact_uniform_buchstab_atoms hmin hmax
    (by positivity : 0 < epsilon/2)
  obtain ⟨Te,he'⟩ := compact_multiplier_error (k:=1) hmin hmax
    (by norm_num : (0:ℝ) ≤ 20) (by positivity : 0 < epsilon/2)
  refine ⟨max Tp Te, ?_⟩
  intro N hN L hL c hc d up b
  obtain ⟨hA,hm⟩ := he' N (by omega) L hL
  have hh := trueSingleTest_error d (atomDomain up b c) residualSingle
    (by norm_num) (fun x => by
      rw [abs_of_nonneg (residualSingle_bounds x).1]
      exact (residualSingle_bounds x).2) hA
  have ht := abs_sub_le (trueAtom N L d up b c)
    (scaledPrimeSum N L (atomDomain up b c) residualSingle)
    (normalizedAtomIntegral up b c)
  change |trueAtom N L d up b c - _| ≤ _ at hh
  norm_num only at hh
  linarith [hp N (by omega) L hL c hc up b]

/-- The threshold precedes all the geometric and arithmetic parameters.
The genuine prefix bound d<=N remains explicit and is later derived from
parentWindow; it is not inferred from a prime-mass limit. -/
theorem compact_uniform_masked_atoms {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ c ∈ Icc (1:ℝ) 6, ∀ d : ℕ, 0 < d → d ≤ N →
      ∀ up : Bool, ∀ b : FloorAtom,
      |maskedAtom N L d up b c-normalizedAtomIntegral up b c| < epsilon := by
  obtain ⟨Tp,hp⟩ := compact_uniform_true_atoms hmin hmax
    (by positivity : 0 < epsilon/2)
  obtain ⟨Tm,hm⟩ := compact_uniform_prefixMask_difference
    (a:=Lmin/10) (by positivity) (by norm_num : (0:ℝ) ≤ 10)
    (by positivity : 0 < epsilon/2)
  refine ⟨max 2 (max Tp Tm), ?_⟩
  intro N hN L hL c hc d hd hdN up b
  have hf : (N:ℝ)^(Lmin/10) ≤ (N:ℝ)^(L/10) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith [hL.1])
  have he' := hm N (by omega) d hd hdN _ _ hf
    (fun q => atomTest up b c (primeCoord N L q))
    (fun q hq => atomTest_abs_le up b c _)
  rw [← trueAtom_eq_window N L d up b c] at he'
  change |maskedAtom N L d up b c-trueAtom N L d up b c| < epsilon/2 at he'
  have ht := abs_sub_le (maskedAtom N L d up b c) (trueAtom N L d up b c)
    (normalizedAtomIntegral up b c)
  linarith [hp N (by omega) L hL c hc d up b]

/-- Capping a start at 6 preserves its actual interval up to 5 exactly.
In particular a start above 5 is not replaced by the singleton {5}. -/
theorem capped_start_interval (c : ℝ) : Icc (min c 6) (5:ℝ) = Icc c 5 := by
  by_cases hc : c ≤ 6
  · rw [min_eq_left hc]
  · have hc' : 6 < c := lt_of_not_ge hc
    rw [min_eq_right hc'.le, Icc_eq_empty_of_lt (by norm_num : (5:ℝ) < 6),
      Icc_eq_empty_of_lt (by linarith : (5:ℝ) < c)]

theorem capped_atomDomain {up : Bool} {b : FloorAtom} {c : ℝ} (hc : 1 ≤ c) :
    atomDomain up b (min c 6) = atomDomain up b c := by
  ext x
  rw [atomDomain_query (le_min hc (by norm_num)) x,
    atomDomain_query hc x, capped_start_interval]

end
end ImbalancedChen.Part5OriginalBuchstabTrueAtomLimits
