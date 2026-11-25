import ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass
import ImbalancedChen.P2MarkedPrimeDivisorFloorCore
import ImbalancedChen.P2MarkedPrimeProductFibreCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Ordinary radial payment for one ambient family with the original frozen
source-rank bound. The fixed-cutoff radial argument is reused with
cut(N) = N^(frozenLeafCutoffFloor / 2). There is no colour or history
multiplier: every ordered tuple is counted once, including repeated
primes. The sum includes rank zero, with its usual empty product and
0^0 = 1 fibre bound. No whole-history aggregation or J cost is asserted.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount
noncomputable section
open Filter Finset Real LiLiuPrereqBuchstab
open Part5OriginalH430ClassicalFixedClampGeometry (prime_divisor_floor)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5RadialRoughMass
open scoped Classical Topology BigOperators

def bandTuples (N k : ℕ) (b c : ℝ) : Finset (Fin k → Fin (2 * N + 1)) :=
  (Part3.labelledPrimeTuples k (2 * N)).filter (fun t =>
    (∀ i, cut N ≤ ((t i).val : ℝ)) ∧
      b * (N : ℝ) < (Part3.labelledProduct t : ℝ) ∧
      (Part3.labelledProduct t : ℝ) ≤ c * (N : ℝ))

def boundaryCount (N : ℕ) (b c : ℝ) : ℝ :=
  ∑ k : Fin (frozenSourceRankBound + 1), ((bandTuples N k.val b c).card : ℝ)

def multiplicity : ℝ :=
  ∑ k : Fin (frozenSourceRankBound + 1), ((k.val ^ k.val : ℕ) : ℝ)

/-- The existing product-fibre estimate is used at every rank, including
zero. The product map is not treated as injective. -/
theorem rank_bound (N k : ℕ) (b c : ℝ) :
    ((bandTuples N k b c).card : ℝ) ≤
      ((k ^ k : ℕ) : ℝ) * ((shell N b c).card : ℝ) := by
  let S := bandTuples N k b c
  have hsub : S ⊆ Part3.labelledPrimeTuples k (2 * N) := filter_subset _ _
  have hmap {t} (ht : t ∈ S) : Part3.labelledProduct t ∈ shell N b c := by
    obtain ⟨hprime, hfloor, hlo, hhi⟩ := mem_filter.mp ht
    have htpr := (mem_filter.mp hprime).2
    let L := List.ofFn (fun i : Fin k => (t i).val)
    have hL : ∀ q ∈ L, q.Prime ∧ cut N ≤ (q : ℝ) := by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact ⟨htpr i, hfloor i⟩
    have hprod : L.prod = Part3.labelledProduct t := by
      simp only [L, List.prod_ofFn, Part3.labelledProduct]
    refine mem_shell.mpr ⟨Finset.prod_pos (fun i _ => (htpr i).pos), hlo, hhi, ?_⟩
    intro q hq hd
    exact prime_divisor_floor hL q hq (hprod.symm ▸ hd)
  have hcard : S.card =
      ∑ m ∈ shell N b c, (S.filter (fun t => Part3.labelledProduct t = m)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ ht => hmap ht)
  change (S.card : ℝ) ≤ _
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ _m ∈ shell N b c, ((k ^ k : ℕ) : ℝ) :=
      sum_le_sum (fun m _ => by
        exact_mod_cast p5z_marked_prime_product_fibre_card_le S hsub m)
    _ = _ := by simp [mul_comm]

theorem all_ranks_bound (N : ℕ) (b c : ℝ) :
    boundaryCount N b c ≤ multiplicity * ((shell N b c).card : ℝ) := by
  have hh := Finset.sum_le_sum
    (s := (univ : Finset (Fin (frozenSourceRankBound + 1))))
    (fun k _ => rank_bound N k.val b c)
  rw [← sum_mul] at hh
  exact hh

theorem rank_card_le_boundaryCount (N k : ℕ) (b c : ℝ)
    (hk : k ≤ frozenSourceRankBound) :
    ((bandTuples N k b c).card : ℝ) ≤ boundaryCount N b c := by
  let j : Fin (frozenSourceRankBound + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  change ((bandTuples N j.val b c).card : ℝ) ≤
    ∑ i : Fin (frozenSourceRankBound + 1), ((bandTuples N i.val b c).card : ℝ)
  exact Finset.single_le_sum
    (fun (i : Fin (frozenSourceRankBound + 1)) _ =>
      (Nat.cast_nonneg (bandTuples N i.val b c).card : (0 : ℝ) ≤ _)) (mem_univ j)

/-- One ambient unit-weight tuple family is paid in ordinary N/log N
mass. The width is fixed before N; the original rank and its finite sum
remain symbolic. This is not a payment for aggregated history marks. -/
theorem absolute_radial_payment {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧ ∀ᶠ N : ℕ in atTop,
      P2FiniteMarkedGamma5RadialRoughMass.norm N *
        boundaryCount N (1 - 2 * h) (1 + 2 * h) ≤ ε := by
  let C := multiplicity * (cutExponent⁻¹ * 4)
  have hM : 0 ≤ multiplicity := by unfold multiplicity; positivity
  have hC : 0 ≤ C := mul_nonneg hM
    (mul_nonneg (inv_nonneg.mpr cutExponent_pos.le) (by norm_num))
  let h := min (1 / 8 : ℝ) (ε / (2 * (C + 1)))
  have hp : 0 < h := lt_min (by norm_num) (div_pos he (by linarith only [hC]))
  have hw : h ≤ 1 / 8 := min_le_left _ _
  have hh := (le_div_iff₀ (show 0 < 2 * (C + 1) by linarith only [hC])).mp
    (show h ≤ ε / (2 * (C + 1)) from min_le_right _ _)
  have hlim := (shell_limit (b := 1 - 2 * h) (c := 1 + 2 * h)
    (by linarith only [hw]) (by linarith only [hp])).const_mul multiplicity
  have homega := buchstab_le_one one_le_inv_cutExponent
  have hM' : 0 ≤ multiplicity * (cutExponent⁻¹ * ((1 + 2 * h) - (1 - 2 * h))) :=
    mul_nonneg hM (mul_nonneg (inv_nonneg.mpr cutExponent_pos.le)
      (by linarith only [hp]))
  have hmain := mul_le_mul_of_nonneg_left homega hM'
  have hsmall :
      multiplicity * (cutExponent⁻¹ * ((1 + 2 * h) - (1 - 2 * h)) *
        buchstab cutExponent⁻¹) < ε := by
    have hh' : C * h < ε := by
      nlinarith only [hh, hp, hC, mul_nonneg hC hp.le]
    dsimp only [C] at hh'
    linarith only [hmain, hh']
  refine ⟨h, hp, hw, ?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds hsmall),
    eventually_gt_atTop (1 : ℕ)] with N hN hlarge
  have hnorm : 0 ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast hlarge.le)) (Nat.cast_nonneg _)
  have hb := mul_le_mul_of_nonneg_left
    (all_ranks_bound N (1 - 2 * h) (1 + 2 * h)) hnorm
  calc
    _ ≤ _ := hb
    _ = multiplicity * (P2FiniteMarkedGamma5RadialRoughMass.norm N *
        ((shell N (1 - 2 * h) (1 + 2 * h)).card : ℝ)) := by ring
    _ ≤ _ := hN.le

end
end ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount
