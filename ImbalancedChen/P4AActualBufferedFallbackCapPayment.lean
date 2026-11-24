import ImbalancedChen.P4AActualOwnCubeCapPayment
import ImbalancedChen.P4AOriginalBufferedFallbackCaps
import ImbalancedChen.P4AAll22OriginalKLedger

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

Actual arithmetic payment for the two finite buffered fallback cap tables
constructed in Q22.  The charged carrier is the original selectedThird
history, with the literal second/third guards, target-deleted prime triples
and full reciprocal-prime weight.  The old historical data are fixed first.
One mesh and one positive rational buffer pay both cap defects before N.

This supplies one compact cap-rounding component of the density catalogue.
It does not identify Q22's policy with the original full87 policy, provide
the untrimmed catalog5 residual difference, or pay the compiler reserve.
The absolute defects below cannot be silently identified with a complete
policy difference before its actual finite source dictionary is supplied.
-/

namespace ImbalancedChen.P4AActualBufferedFallbackCapPayment

noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AOriginalBufferedFallbackCaps P4AActualOwnCubeCapPayment

def history (p : Fin 3 → ℕ) : List ℕ := [p 2, p 1, p 0]

def secondTuples (d : OriginalData) (a : ℝ) (N : ℕ) : Finset (Fin 3 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ => a) (fun _ => (19 / 96 : ℝ))).filter
    (fun p => selectedThird d (N : ℝ) (history p) ∧
      secondGuard (N : ℝ) (history p))

def thirdTuples (d : OriginalData) (a : ℝ) (N : ℕ) : Finset (Fin 3 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ => a) (fun _ => (19 / 96 : ℝ))).filter
    (fun p => selectedThird d (N : ℝ) (history p) ∧
      thirdGuard (N : ℝ) (history p))

/-- A source occurrence is charged to at most one of the two fallbacks. -/
theorem fallback_tuples_disjoint (d : OriginalData) (a : ℝ) (N : ℕ) :
    Disjoint (secondTuples d a N) (thirdTuples d a N) := by
  apply Finset.disjoint_left.mpr
  intro p hp2 hp3
  exact second_third_disjoint (N : ℝ) (history p) (by simp [history])
    (Finset.mem_filter.mp hp2).2.2 (Finset.mem_filter.mp hp3).2.2

def secondCapDefect (d : OriginalData) (m : ℕ) (buffer a : ℝ) (N cap : ℕ) : ℝ :=
  capDefect 2 N cap (secondTuples d a N)
    (fun p => effective2 d m buffer (N : ℝ) (history p))
    (fun p => secondExponent (N : ℝ) (history p))

def thirdCapDefect (d : OriginalData) (m : ℕ) (buffer a : ℝ) (N cap : ℕ) : ℝ :=
  capDefect 2 N cap (thirdTuples d a N)
    (fun p => effective3 d m buffer (N : ℝ) (history p))
    (fun p => thirdExponent (N : ℝ) (history p))

private theorem second_exponent_bounds (N : ℝ) (pre : List ℕ)
    (hg : secondGuard N pre) :
    0 < secondExponent N pre ∧ secondExponent N pre ≤ thirdPrefixTheta := by
  let t := primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre)
  have hreg : SecondRegion (t 0) (t 1) := hg
  have hx : 0 < t 0 := by
    have h := hreg.1
    dsimp only [mu] at h
    linarith
  have hcube := above_mu_old_cap_gt_cube hreg.1 hreg.2.1
  have hnew := (second_initial_physical_gates hreg).2.2.2
  change 0 < v (t 1) ∧ v (t 1) ≤ thirdPrefixTheta
  exact ⟨by linarith, (v_le_cap _).trans (by norm_num [cap, thirdPrefixTheta])⟩

private theorem third_exponent_bounds (N : ℝ) (pre : List ℕ)
    (hg : thirdGuard N pre) :
    0 < thirdExponent N pre ∧ thirdExponent N pre ≤ thirdPrefixTheta := by
  let t := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  have hreg : ThirdRegion (t 0) (t 1) (t 2) := hg
  have hx : 0 < t 0 := by
    have h := hreg.1
    dsimp only [mu] at h
    linarith
  have hcube := above_mu_old_cap_gt_cube hreg.1 hreg.2.1
  have hnew := (third_initial_physical_gates hreg).2.2.2.2.2
  change 0 < v (t 1 + t 2) ∧ v (t 1 + t 2) ≤ thirdPrefixTheta
  exact ⟨by linarith, (v_le_cap _).trans (by norm_num [cap, thirdPrefixTheta])⟩

/-- Fixed old data and compact cutoff, then a shared finite mesh/buffer,
then N0.  The later covering cap is arbitrary.  Both absolute weighted
errors are paid from actual residual suppliers, rather than assumed. -/
theorem exists_one_preN_buffered_fallback_cap_payment
    (d : OriginalData) (he : 0 < (d.e : ℝ)) (a eta : ℝ)
    (ha : 0 < a) (harho : a < (19 / 96 : ℝ)) (heta : 0 < eta) :
    ∃ m : ℕ, ∃ buffer : ℚ, 0 < (buffer : ℝ) ∧
      (buffer : ℝ) ≤ 2 * (d.e : ℝ) ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        secondCapDefect d m buffer a N cap + thirdCapDefect d m buffer a N cap < eta := by
  obtain ⟨delta, hd, N0, hN0, hpay⟩ := exists_weighted_cap_payment
    2 a (19 / 96) (-1) thirdPrefixTheta (eta / 2)
    ha harho (by norm_num [thirdPrefixTheta]) (half_pos heta)
  let precision : ℝ := min delta (1 / 2)
  have hp : 0 < precision := lt_min hd (by norm_num)
  obtain ⟨m, buffer, hb, _hbp, hbe, happrox⟩ :=
    exists_one_preN_buffered_fallback d he precision hp
  refine ⟨m, buffer, hb, hbe, N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have hsecond : secondCapDefect d m buffer a N cap < eta / 2 := by
    apply hpay N hN hEven cap hcap (secondTuples d a N)
      (Finset.filter_subset _ _)
    intro p hp2
    obtain ⟨_hbox, hs, hg⟩ := Finset.mem_filter.mp hp2
    have hA := (happrox (N : ℝ) (history p) (by simp [history]) hs).1 hg
    have hI := second_exponent_bounds (N : ℝ) (history p) hg
    have hpdelta : precision ≤ delta := min_le_left _ _
    have hphalf : precision ≤ (1 / 2 : ℝ) := min_le_right _ _
    have hbelow : effective2 d m buffer (N : ℝ) (history p) ≤
        secondExponent (N : ℝ) (history p) := by linarith [hA.2.1]
    refine ⟨⟨by linarith [hA.2.2], hbelow.trans hI.2⟩,
      ⟨by linarith [hI.1], hI.2⟩, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hbelow)]
    linarith [hA.2.2]
  have hthird : thirdCapDefect d m buffer a N cap < eta / 2 := by
    apply hpay N hN hEven cap hcap (thirdTuples d a N)
      (Finset.filter_subset _ _)
    intro p hp3
    obtain ⟨_hbox, hs, hg⟩ := Finset.mem_filter.mp hp3
    have hA := (happrox (N : ℝ) (history p) (by simp [history]) hs).2 hg
    have hI := third_exponent_bounds (N : ℝ) (history p) hg
    have hpdelta : precision ≤ delta := min_le_left _ _
    have hphalf : precision ≤ (1 / 2 : ℝ) := min_le_right _ _
    have hbelow : effective3 d m buffer (N : ℝ) (history p) ≤
        thirdExponent (N : ℝ) (history p) := by linarith [hA.2.1]
    refine ⟨⟨by linarith [hA.2.2], hbelow.trans hI.2⟩,
      ⟨by linarith [hI.1], hI.2⟩, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hbelow)]
    linarith [hA.2.2]
  linarith

/-- An explicitly available u_d/8 allocation for this one compact cap
component.  The pre-existing u_d/4 third-functional payment and u_c are
not invoked or spent here; full-policy source matching remains separate. -/
theorem exists_buffered_fallback_density_eighth
    (d : OriginalData) (he : 0 < (d.e : ℝ)) (a : ℝ)
    (ha : 0 < a) (harho : a < (19 / 96 : ℝ)) :
    ∃ m : ℕ, ∃ buffer : ℚ, 0 < (buffer : ℝ) ∧
      (buffer : ℝ) ≤ 2 * (d.e : ℝ) ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        secondCapDefect d m buffer a N cap + thirdCapDefect d m buffer a N cap <
          P4AAll22OriginalKLedger20261024zSourceOnly.densityReserve / 8 := by
  apply exists_one_preN_buffered_fallback_cap_payment d he a _ ha harho
  exact div_pos P4AAll22OriginalKLedger20261024zSourceOnly.densityReserve_pos
    (by norm_num)

end
end ImbalancedChen.P4AActualBufferedFallbackCapPayment
