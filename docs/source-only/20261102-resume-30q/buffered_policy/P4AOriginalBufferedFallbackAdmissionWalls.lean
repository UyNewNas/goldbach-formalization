import ImbalancedChen.P4AOriginalBufferedFallbackCaps
import ImbalancedChen.P5PresievedRoughSlotAffineGates

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

Actual ordinary admission changes caused by the finite v-cap approximation
are covered at the changed prefix itself by one fixed finite affine family
at each rank. The catalogue contains the total product row and EVERY
original odd-cardinality cube row. It is independent of N, the coarse mesh
size and the later compiler atom count. Properness is proved using the
first coordinate, which neither of the selected inputs p2 and p2*p3 uses.

This is cap-approximation admission coverage, not the unprovided global
tagged-compiler mixed-cell cover of full87. No strip estimate is repeated.
No arithmetic mass, signed density, support-inflation or reserve bound is
assumed or claimed.
-/

namespace ImbalancedChen.P4AOriginalBufferedFallbackAdmissionWalls
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P4AOriginalBufferedFallbackCaps
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P5Z.PresievedRoughSlotAffineGates

abbrev Gate (r : ℕ) := Option (Fin r)

def gateValue {r : ℕ} (g : Gate r) (t : Fin r → ℝ) : ℝ :=
  match g with
  | none => ∑ i, t i
  | some i => cube t i

def gateRow {r : ℕ} (g : Gate r) : (Fin r → ℝ) →L[ℝ] ℝ :=
  match g with
  | none => totalRow r
  | some i => cubeRow i

theorem gateRow_apply {r : ℕ} (g : Gate r) (t : Fin r → ℝ) :
    gateRow g t = gateValue g t := by
  cases g with
  | none => simp [gateRow, gateValue, totalRow, ContinuousLinearMap.sum_apply]
  | some i => exact cubeRow_apply i t

/-- false = selected p2; true = selected p2*p3. Both exclude p1. -/
def inputRow {r : ℕ} (hr : 3 ≤ r) (third : Bool) : (Fin r → ℝ) →L[ℝ] ℝ :=
  if third then ContinuousLinearMap.proj ⟨1, by omega⟩ +
    ContinuousLinearMap.proj ⟨2, by omega⟩
  else ContinuousLinearMap.proj ⟨1, by omega⟩

/-- The two literal limbs of v, with their original constants. -/
def wallRow {r : ℕ} (hr : 3 ≤ r) (third : Bool) (g : Gate r)
    (rising : Bool) : (Fin r → ℝ) →L[ℝ] ℝ :=
  if rising then gateRow g - (1 / 2 : ℝ) • inputRow hr third
  else gateRow g + (3 / 2 : ℝ) • inputRow hr third

def wallOffset (rising : Bool) : ℝ := if rising then 1 / 2 else 57 / 64

theorem wallRow_gap {r : ℕ} (hr : 3 ≤ r) (third : Bool) (g : Gate r)
    (rising : Bool) (t : Fin r → ℝ) :
    wallRow hr third g rising t - wallOffset rising =
      gateValue g t - (if rising then A (inputRow hr third t) else C (inputRow hr third t)) := by
  cases rising <;> simp only [wallRow, wallOffset, Bool.false_eq_true,
    Bool.true_eq_true, if_false, if_true, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    gateRow_apply, A, C] <;> ring

private def firstBasis {r : ℕ} (hr : 3 ≤ r) : Fin r → ℝ :=
  fun i => if i = ⟨0, by omega⟩ then 1 else 0

private theorem inputRow_firstBasis {r : ℕ} (hr : 3 ≤ r) (third : Bool) :
    inputRow hr third (firstBasis hr) = 0 := by
  cases third <;> simp [inputRow, firstBasis]

private theorem gateValue_firstBasis_pos {r : ℕ} (hr : 3 ≤ r) (g : Gate r) :
    0 < gateValue g (firstBasis hr) := by
  cases g with
  | none => simp [gateValue, firstBasis]
  | some i =>
      by_cases hi : i = ⟨0, by omega⟩
      · subst i
        simp [gateValue, cube, prefix, firstBasis]
      · have hi0 : 0 < i.val := by
          have hn : i.val ≠ 0 := by
            intro hh
            apply hi
            exact Fin.ext hh
          omega
        simp [gateValue, cube, prefix, firstBasis, hi, hi0]

/-- All walls are proper, including ties between v's two limbs. No
constant/equality region is deleted in order to obtain properness. -/
theorem wallRow_ne_zero {r : ℕ} (hr : 3 ≤ r) (third : Bool)
    (g : Gate r) (rising : Bool) : wallRow hr third g rising ≠ 0 := by
  intro hz
  have hh := congrArg (fun L : (Fin r → ℝ) →L[ℝ] ℝ => L (firstBasis hr)) hz
  have hp := gateValue_firstBasis_pos hr g
  cases rising <;>
    simp only [wallRow, Bool.false_eq_true, Bool.true_eq_true, if_false, if_true,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, inputRow_firstBasis,
      mul_zero, add_zero, sub_zero, gateRow_apply, ContinuousLinearMap.zero_apply] at hh <;>
    exact (ne_of_gt hp) hh

def OnWall {r : ℕ} (hr : 3 ≤ r) (third : Bool) (delta : ℝ) (t : Fin r → ℝ) : Prop :=
  ∃ g : Gate r, ∃ rising : Bool, |wallRow hr third g rising t - wallOffset rising| ≤ delta

private theorem region_admission_loss_wall {r : ℕ} (hr : 3 ≤ r) (third : Bool)
    (t : Fin r → ℝ) (lambda delta : ℝ)
    (hcap : v (inputRow hr third t) - delta ≤ lambda)
    (hi : t ∈ region r (v (inputRow hr third t)))
    (hb : t ∉ region r lambda) : OnWall hr third delta t := by
  have hg : ∃ g : Gate r, lambda ≤ gateValue g t ∧
      gateValue g t < v (inputRow hr third t) := by
    by_cases ht : (∑ i, t i) < lambda
    · by_contra hn
      apply hb
      refine ⟨ht, ?_⟩
      intro i heven
      by_contra hc
      exact hn ⟨some i, le_of_not_gt hc, hi.2 i heven⟩
    · exact ⟨none, le_of_not_gt ht, hi.1⟩
  obtain ⟨g, hgl, hgu⟩ := hg
  by_cases ha : A (inputRow hr third t) ≤ C (inputRow hr third t)
  · have he : v (inputRow hr third t) = A (inputRow hr third t) := by
      rw [v_eq_min, min_eq_left ha]
    refine ⟨g, true, ?_⟩
    rw [wallRow_gap]
    simp only [Bool.true_eq_true, if_true]
    apply abs_le.mpr
    rw [he] at hcap hgu
    constructor <;> linarith
  · have he : v (inputRow hr third t) = C (inputRow hr third t) := by
      rw [v_eq_min, min_eq_right (le_of_not_ge ha)]
    refine ⟨g, false, ?_⟩
    rw [wallRow_gap]
    simp only [Bool.false_eq_true, if_false]
    apply abs_le.mpr
    rw [he] at hcap hgu
    constructor <;> linarith

private theorem history_admission_iff_log {N r : ℕ} (hN : 1 < N)
    (pre : List ℕ) (hlen : pre.length = r) (hp : ∀ p ∈ pre, 0 < p)
    (horder : pre.Pairwise (· < ·)) (ell : ℝ) :
    ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell) pre ↔
      primeHistoryLogCoordinates (N : ℝ) r pre ∈ region r ell := by
  have hh := original_upper_prefix_iff_log hN ell (primeHistoryTuple r pre)
    (primeHistoryTuple_pos hlen hp) (primeHistoryTuple_strictAnti hlen horder)
  rw [primeHistoryTuple_reverse_ofFn hlen] at hh
  exact hh

theorem second_input_identity {r : ℕ} (hr : 3 ≤ r) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = r) :
    v (inputRow hr false (primeHistoryLogCoordinates N r pre)) = secondExponent N pre := by
  have hh := primeHistoryLogCoordinates_ancestor N hlen (by omega : 2 ≤ r) (1 : Fin 2)
  simpa only [inputRow, Bool.false_eq_true, if_false, ContinuousLinearMap.proj_apply,
    secondExponent] using congrArg v hh.symm

theorem third_input_identity {r : ℕ} (hr : 3 ≤ r) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = r) :
    v (inputRow hr true (primeHistoryLogCoordinates N r pre)) = thirdExponent N pre := by
  have h1 := primeHistoryLogCoordinates_ancestor N hlen hr (1 : Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen hr (2 : Fin 3)
  simpa only [inputRow, Bool.true_eq_true, if_true, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.proj_apply, thirdExponent] using congrArg v (congrArg₂ (· + ·) h1 h2).symm

/-- The entire original admission predicate changes only at one of this
fixed catalogue's walls, measured at the actual charged history. The
lower cap estimate is obtained from the new table, not supplied as input. -/
theorem second_actual_admission_change_wall (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer : ℝ) (hbuffer : buffer ≤ 2 * (d.e : ℝ))
    {N r : ℕ} (hN : 1 < N) (hr : 3 ≤ r)
    (pre : List ℕ) (hlen : pre.length = r) (hp : ∀ p ∈ pre, 0 < p)
    (horder : pre.Pairwise (· < ·)) (hs : selectedThird d (N : ℝ) pre)
    (hg : secondGuard (N : ℝ) pre)
    (hi : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ secondExponent (N : ℝ) pre) pre)
    (hb : ¬ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ effective2 d m buffer (N : ℝ) pre) pre) :
    OnWall hr false ((3 / 2 : ℝ) * step m + buffer)
      (primeHistoryLogCoordinates (N : ℝ) r pre) := by
  have hc := (effective2_interval d he m buffer (N : ℝ) hbuffer pre
    (by omega) hs hg).2.1
  have hl := history_admission_iff_log hN pre hlen hp horder
  apply region_admission_loss_wall hr false _ (effective2 d m buffer (N : ℝ) pre)
  · simpa only [second_input_identity hr (N : ℝ) pre hlen] using hc
  · rw [second_input_identity hr (N : ℝ) pre hlen]
    exact (hl _).mp hi
  · exact fun hh => hb ((hl _).mpr hh)

theorem third_actual_admission_change_wall (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer : ℝ) (hbuffer : buffer ≤ 2 * (d.e : ℝ))
    {N r : ℕ} (hN : 1 < N) (hr : 3 ≤ r)
    (pre : List ℕ) (hlen : pre.length = r) (hp : ∀ p ∈ pre, 0 < p)
    (horder : pre.Pairwise (· < ·)) (hs : selectedThird d (N : ℝ) pre)
    (hg : thirdGuard (N : ℝ) pre)
    (hi : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ thirdExponent (N : ℝ) pre) pre)
    (hb : ¬ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ effective3 d m buffer (N : ℝ) pre) pre) :
    OnWall hr true (3 * step m + buffer)
      (primeHistoryLogCoordinates (N : ℝ) r pre) := by
  have hc := (effective3_interval d he m buffer (N : ℝ) hbuffer pre
    (by omega) hs hg).2.1
  have hl := history_admission_iff_log hN pre hlen hp horder
  apply region_admission_loss_wall hr true _ (effective3 d m buffer (N : ℝ) pre)
  · simpa only [third_input_identity hr (N : ℝ) pre hlen] using hc
  · rw [third_input_identity hr (N : ℝ) pre hlen]
    exact (hl _).mp hi
  · exact fun hh => hb ((hl _).mpr hh)

/-- Directly consume rejection by the newly defined physical second
policy; the effective exponent is not an unattached cap record. -/
theorem second_policy_change_wall (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer : ℝ) (hbuffer : buffer ≤ 2 * (d.e : ℝ))
    {N r : ℕ} (hN : 1 < N) (hr : 3 ≤ r)
    (pre : List ℕ) (hlen : pre.length = r) (hp : ∀ p ∈ pre, 0 < p)
    (horder : pre.Pairwise (· < ·)) (hs : selectedThird d (N : ℝ) pre)
    (hg : secondGuard (N : ℝ) pre)
    (hi : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ secondExponent (N : ℝ) pre) pre)
    (hb : bufferedSecondPolicy d m buffer (N : ℝ) false pre = false) :
    OnWall hr false ((3 / 2 : ℝ) * step m + buffer)
      (primeHistoryLogCoordinates (N : ℝ) r pre) := by
  have hn : ¬pre.length ≤ 2 := by omega
  have hbad : ¬ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ effective2 d m buffer (N : ℝ) pre) pre := by
    simpa only [bufferedSecondPolicy, if_neg hn, if_pos (And.intro hs hg),
      ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
      oddFirstExitPolicy, Bool.false_or, decide_eq_false_iff_not] using hb
  exact second_actual_admission_change_wall d he m buffer hbuffer hN hr pre hlen hp horder hs hg hi hbad

/-- The third action is taken strictly after rank three; the previous
rank-three decision is untouched by this statement and by its definition. -/
theorem third_policy_change_wall (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer : ℝ) (hbuffer : buffer ≤ 2 * (d.e : ℝ))
    {N r : ℕ} (hN : 1 < N) (hr : 4 ≤ r)
    (pre : List ℕ) (hlen : pre.length = r) (hp : ∀ p ∈ pre, 0 < p)
    (horder : pre.Pairwise (· < ·)) (hs : selectedThird d (N : ℝ) pre)
    (hg : thirdGuard (N : ℝ) pre)
    (hi : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ thirdExponent (N : ℝ) pre) pre)
    (hb : bufferedThirdPolicy d m buffer (N : ℝ) false pre = false) :
    OnWall (show 3 ≤ r by omega) true (3 * step m + buffer)
      (primeHistoryLogCoordinates (N : ℝ) r pre) := by
  have hn : ¬pre.length ≤ 3 := by omega
  have hbad : ¬ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ effective3 d m buffer (N : ℝ) pre) pre := by
    simpa only [bufferedThirdPolicy, if_neg hn, if_pos (And.intro hs hg),
      ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
      oddFirstExitPolicy, Bool.false_or, decide_eq_false_iff_not] using hb
  exact third_actual_admission_change_wall d he m buffer hbuffer hN (by omega)
    pre hlen hp horder hs hg hi hbad

/-- Actual prime frontiers supply length, positivity and order. This does
not require the changed candidate to have passed the buffered admission. -/
theorem frontier_second_admission_change_wall (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (m : ℕ) (buffer : ℝ) (hbuffer : buffer ≤ 2 * (d.e : ℝ))
    {N r : ℕ} (hN : 1 < N) (hr : 3 ≤ r) (enumerationCap : ℕ) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (mass : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hstate : s ∈ firstExitDepthFrontier r parent mass [] true 1
      (roughPrimeUniverse N enumerationCap w z))
    (hs : selectedThird d (N : ℝ) s.selectedPrefix)
    (hg : secondGuard (N : ℝ) s.selectedPrefix)
    (hi : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix) s.selectedPrefix)
    (hb : ¬ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ effective2 d m buffer (N : ℝ) s.selectedPrefix) s.selectedPrefix) :
    OnWall hr false ((3 / 2 : ℝ) * step m + buffer)
      (primeHistoryLogCoordinates (N : ℝ) r s.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length r parent mass []
    (roughPrimeUniverse N enumerationCap w z) true 1 (by simp) s hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist r parent mass
    (roughPrimeUniverse N enumerationCap w z) s hstate
  have hp : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have ho : s.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N enumerationCap w z).sublist hsub
  exact second_actual_admission_change_wall d he m buffer hbuffer hN hr
    s.selectedPrefix hlen hp ho hs hg hi hb

end
end ImbalancedChen.P4AOriginalBufferedFallbackAdmissionWalls
