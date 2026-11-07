import ImbalancedChen.P5PresievedRoughSmoothCover
import ImbalancedChen.ActualFrozenSelectedPairAssignment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Continuous ORIGINAL rough upper endpoints supply their own numerical
admissibility and D-well support. The REAL-upper prefer-left greedy then
chooses actual slot lists ONCE for the whole atom. All coordinatewise
smaller natural tuples use those same lists. No prime seed, discrepancy,
factorability premise or supplied D-well predicate enters the constructor.
-/
namespace ImbalancedChen.P5Z.PresievedRoughEndpointAllocation
noncomputable section
open Classical
open scoped BigOperators
open PresievedRoughSlotAffineGates
open MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def endpointWeight {r : ℕ} (N : ℕ) (u : Fin r → ℝ) (i : Fin r) : ℝ := (N : ℝ) ^ u i

theorem endpoint_cube_rpow {r N : ℕ} (hN : 1 < N) (u : Fin r → ℝ) (i : Fin r) :
    (N : ℝ) ^ cube u i =
      (∏ j : Fin r with j.val < i.val, endpointWeight N u j) * (endpointWeight N u i) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have h3 : (N : ℝ) ^ (3 * u i) = ((N : ℝ) ^ u i) ^ 3 := by
    rw [mul_comm (3 : ℝ), Real.rpow_mul hn.le, Real.rpow_natCast]
  unfold endpointWeight
  rw [cube, Real.rpow_add hn, prefix, Real.rpow_sum_of_pos hn, h3]

/-- The original affine odd-prefix tests, rather than an hFullSupport
assumption, certify the continuous endpoint vector for arbitrary rank. -/
theorem endpoints_original_admissible {r N : ℕ} (hN : 1 < N) (u : Fin r → ℝ) (ell : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hanti : Antitone u)
    (hcubes : ∀ i : Fin r, Even i.val → cube u i < ell) :
    Admissible true (endpointWeight N u) ((N : ℝ) ^ ell) (List.finRange r) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    simpa only [endpointWeight, Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hn.le (hu i)
  · intro i j hi hj hij
    have hir : i < r := by simpa using hi
    have hjr : j < r := by simpa using hj
    have he : u ⟨j, hjr⟩ ≤ u ⟨i, hir⟩ := hanti (show (⟨i, hir⟩ : Fin r) ≤ ⟨j, hjr⟩ from hij)
    simpa only [endpointWeight, List.getElem_finRange] using Real.rpow_le_rpow_of_exponent_le hn.le he
  · intro hlen
    have hr : 0 < r := by simpa using hlen
    let i : Fin r := ⟨0, hr⟩
    have hc : 3 * u i < ell := by simpa [cube, prefix, i] using hcubes i (by simp [i])
    have h2 : 2 * u i < ell := by linarith [hu i]
    have hsq : (endpointWeight N u i) ^ 2 = (N : ℝ) ^ (2 * u i) := by
      unfold endpointWeight
      rw [mul_comm (2 : ℝ), Real.rpow_mul hnpos.le, Real.rpow_natCast]
    have hsqrt : endpointWeight N u i < Real.sqrt ((N : ℝ) ^ ell) := by
      apply (Real.lt_sqrt (Real.rpow_nonneg hnpos.le _)).mpr
      rw [hsq]
      exact Real.rpow_lt_rpow_of_exponent_lt hn h2
    simpa only [List.getElem_finRange, i] using hsqrt
  · intro i hi hpar
    have hir : i < r := by simpa using hi
    let j : Fin r := ⟨i, hir⟩
    have hj : Even j.val := Nat.even_iff.mpr hpar
    have hc := Real.rpow_lt_rpow_of_exponent_lt hn (hcubes j hj)
    rw [endpoint_cube_rpow hN u j] at hc
    simpa only [List.map_take, ← List.ofFn_eq_map, List.prod_take_ofFn,
      List.getElem_finRange, j] using hc

theorem endpoints_original_dwell {r N : ℕ} (hN : 1 < N) (u : Fin r → ℝ) (ell : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hanti : Antitone u)
    (hcubes : ∀ i : Fin r, Even i.val → cube u i < ell) :
    PrefixSquareBound (endpointWeight N u) ((N : ℝ) ^ ell) (List.finRange r) :=
  (endpoints_original_admissible hN u ell hu hanti hcubes).prefixSquareBound

/-- This is a deterministic label constructor from the fixed REAL upper
vector. It does not run on a tuple or on its arithmetic coefficient. -/
def endpointGroups {r : ℕ} (N : ℕ) (u : Fin r → ℝ) (A : ℝ) : List (Fin r) × List (Fin r) :=
  actualTwoCapacityGreedy (endpointWeight N u) A (List.finRange r)

theorem endpointGroups_capacity {r N : ℕ} (hN : 1 < N) (u : Fin r → ℝ) (ell A : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hanti : Antitone u)
    (hcubes : ∀ i : Fin r, Even i.val → cube u i < ell)
    (hA : 1 ≤ A) (hAlevel : A ≤ (N : ℝ) ^ ell) :
    let groups := endpointGroups N u A
    BoxPartition groups.1 groups.2 (List.finRange r) ∧
      (groups.1.map (endpointWeight N u)).prod ≤ A ∧
      (groups.2.map (endpointWeight N u)).prod ≤ (N : ℝ) ^ ell / A := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hB : 1 ≤ (N : ℝ) ^ ell / A := (le_div_iff₀ hApos).mpr (by simpa using hAlevel)
  have hfull := endpoints_original_dwell hN u ell hu hanti hcubes
  have hlevel : A * ((N : ℝ) ^ ell / A) = (N : ℝ) ^ ell := by field_simp [hApos.ne']
  rw [← hlevel] at hfull
  exact actualTwoCapacityGreedy_correct (endpointWeight N u) hA hB (List.finRange r) hfull

/-- Every natural tuple below the same real endpoints receives the SAME
computed slot lists, exact full product and both proved capacities. -/
theorem endpointGroups_all_tuples {r N : ℕ} (hN : 1 < N) (u : Fin r → ℝ) (ell A : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hanti : Antitone u)
    (hcubes : ∀ i : Fin r, Even i.val → cube u i < ell)
    (hA : 1 ≤ A) (hAlevel : A ≤ (N : ℝ) ^ ell) :
    let groups := endpointGroups N u A
    ∀ p : Fin r → ℕ, (∀ i, (p i : ℝ) ≤ endpointWeight N u i) →
      (groups.1.map p).prod * (groups.2.map p).prod = (List.ofFn p).prod ∧
      ((groups.1.map p).prod : ℝ) ≤ A ∧
      ((groups.2.map p).prod : ℝ) ≤ (N : ℝ) ^ ell / A := by
  obtain ⟨hpart, hleft, hright⟩ := endpointGroups_capacity hN u ell A hu hanti hcubes hA hAlevel
  intro p hp
  have hbound (l : List (Fin r)) : ((l.map p).prod : ℝ) ≤ (l.map (endpointWeight N u)).prod := by
    rw [← actualNatList_cast_prod]
    simpa only [List.map_map, Function.comp_def] using List.prod_map_le_prod_map₀
      (fun i => (p i : ℝ)) (endpointWeight N u) (fun i hi => Nat.cast_nonneg _) (fun i hi => hp i)
  have heq := (hpart.perm.map p).prod_eq
  refine ⟨?_, (hbound _).trans hleft, (hbound _).trans hright⟩
  simpa only [List.map_append, List.prod_append, ← List.ofFn_eq_map] using heq

end
end ImbalancedChen.P5Z.PresievedRoughEndpointAllocation
