import ImbalancedChen.AffinePrimeWallReserve
import ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient
import ImbalancedChen.P2MarkedPrimeProductFibreCore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
Count an affine wall by reserving one prime coordinate omitted by its
forms. The remaining positions retain their order, even at repeated
prime values. The omitted prime is a nonunit member of the original
rough carrier. The only bound on its multiplicity is that carrier's
actual count. No injectivity of the product map is needed.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall

noncomputable section
open Filter Finset Real LiLiuPrereqBuchstab
open P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent cutExponent_pos norm)
open P2FiniteMarkedGamma5NonunitQuotient (eventually_nonunit_quotient_le)
open scoped Classical BigOperators Topology

abbrev BoundedTuple (N d : ℕ) := Fin (d + 1) → Fin (2 * N + 1)

def remaining {N d : ℕ} (j : Fin (d + 1)) (t : BoundedTuple N d) :
    Fin d → ℕ := fun i => (t (j.succAbove i)).val

def wallTuples {d r : ℕ} (N : ℕ) (j : Fin (d + 1))
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) :
    Finset (BoundedTuple N d) :=
  (Part3.labelledPrimeTuples (d + 1) (2 * N)).filter fun t =>
    (∀ i, cut N ≤ ((t i).val : ℝ)) ∧ Part3.labelledProduct t ≤ 2 * N ∧
    (Part3.labelledProduct t).Coprime N ∧
    actualPrimeTupleLog N (remaining j t) ∈ primeAffineWallStrip L c δ

private def fixedBox {d r : ℕ} (N : ℕ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) :=
  (actualPrimeBoxTuples N (fun _ : Fin d => cutExponent) (fun _ => cutExponent + 2)).filter
    (fun v => actualPrimeTupleLog N v ∈ primeAffineWallStrip L c δ)

private def quotient {d : ℕ} (N : ℕ) (v : Fin d → ℕ) :=
  (roughNumbers (2 * (N : ℝ) / ((∏ i, v i : ℕ) : ℝ)) (cut N)).erase 1

/-- Encoding retains all positions. Decoding reinstates the omitted value
at j; no coprimality, primality, or distinctness is needed for injectivity. -/
private def encode {N d : ℕ} (j : Fin (d + 1)) (t : BoundedTuple N d) :
    Σ _ : Fin d → ℕ, ℕ := ⟨remaining j t, (t j).val⟩

private theorem encode_injective {N d : ℕ} (j : Fin (d + 1)) :
    Function.Injective (encode (N := N) j) := by
  intro t u he
  have hrem : remaining j t = remaining j u :=
    congrArg (fun a : Σ _ : Fin d → ℕ, ℕ => a.1) he
  have hj : (t j).val = (u j).val :=
    congrArg (fun a : Σ _ : Fin d → ℕ, ℕ => a.2) he
  funext i
  apply Fin.ext
  by_cases hi : i = j
  · subst i
    exact hj
  · obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hi
    exact congrFun hrem z

private theorem fixedProduct_two_le {d : ℕ} (hd : 0 < d) (v : Fin d → ℕ)
    (hp : ∀ i, (v i).Prime) : 2 ≤ ∏ i, v i := by
  let i : Fin d := ⟨0, hd⟩
  exact (hp i).two_le.trans (Nat.le_of_dvd (prod_pos (fun z _ => (hp z).pos))
    (dvd_prod_of_mem v (mem_univ i)))

private theorem encode_mem {N d r : ℕ} (hN : 2 < N) (j : Fin (d + 1))
    {L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ} {c : Fin r → ℝ} {δ : ℝ}
    {t : BoundedTuple N d} (ht : t ∈ wallTuples N j L c δ) :
    encode j t ∈ (fixedBox N L c δ).sigma (quotient N) := by
  obtain ⟨hlabel, hfloor, hcap, hcop, hwall⟩ := mem_filter.mp ht
  have hp : ∀ i, (t i).val.Prime := (mem_filter.mp hlabel).2
  have hNr : (2 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by linarith
  have hupper : 2 * (N : ℝ) < (N : ℝ) ^ (cutExponent + 2) := by
    calc
      _ < (N : ℝ) ^ (2 : ℕ) := by nlinarith
      _ = (N : ℝ) ^ (2 : ℝ) := (rpow_two _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hNr1 (by linarith only [cutExponent_pos])
  have hfac : Part3.labelledProduct t = (t j).val * ∏ i, remaining j t i :=
    Fin.prod_univ_succAbove (fun i => (t i).val) j
  have hden : 0 < ∏ i, remaining j t i := prod_pos (fun i _ => (hp (j.succAbove i)).pos)
  apply mem_sigma.mpr
  constructor
  · apply mem_filter.mpr
    refine ⟨mem_actualPrimeBoxTuples_iff.mpr ?_, hwall⟩
    intro i
    let z := j.succAbove i
    have hdiv : (t z).val ∣ Part3.labelledProduct t :=
      dvd_prod_of_mem (fun i => (t i).val) (mem_univ z)
    have hnot : ¬(t z).val ∣ N := by
      intro h
      exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨(t z).val, hp z, hdiv, h⟩) hcop
    have hle : (t z).val ≤ 2 * N := by have h := (t z).isLt; omega
    exact ⟨hp z, hnot, hfloor z, (by exact_mod_cast hle : ((t z).val : ℝ) ≤ 2 * N).trans_lt hupper⟩
  · apply mem_erase.mpr
    refine ⟨(hp j).ne_one, mem_roughNumbers.mpr ⟨(hp j).pos, ?_, ?_⟩⟩
    · apply (le_div_iff₀ (Nat.cast_pos.mpr hden)).mpr
      rw [hfac] at hcap
      exact_mod_cast hcap
    · intro q hq hqd
      have he : q = (t j).val := (Nat.prime_dvd_prime_iff_eq hq (hp j)).mp hqd
      simpa only [he] using hfloor j

/-- The width and threshold precede the target N. Both the wall and the
prime-box sum keep the complete ordered set of unreserved coordinates. -/
theorem exists_wallTuples_payment {d r : ℕ} (hd : 0 < d) (j : Fin (d + 1))
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ z, L z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      norm N * ((wallTuples N j L c δ).card : ℝ) ≤ ε := by
  let A : ℝ := 4 / cutExponent
  have hA : 0 < A := div_pos (by norm_num) cutExponent_pos
  obtain ⟨δ, hδ, T, _, H⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    cutExponent_pos (by linarith : cutExponent < cutExponent + 2)
    L c hL (ε / A) (div_pos hε hA)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_nonunit_quotient_le, eventually_ge_atTop T,
    eventually_gt_atTop (2 : ℕ)] with N hquot hT hN
  let S := fixedBox N L c δ
  have hcard : (wallTuples N j L c δ).card ≤ (S.sigma (quotient N)).card :=
    card_le_card_of_injOn (encode j) (fun _ ht => encode_mem hN j ht)
      (encode_injective j).injOn
  have hc : ((wallTuples N j L c δ).card : ℝ) ≤
      ∑ v ∈ S, ((quotient N v).card : ℝ) := by
    rw [card_sigma] at hcard
    exact_mod_cast hcard
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hnorm : 0 ≤ norm N := div_nonneg (log_pos hNr).le (Nat.cast_nonneg _)
  have hrow (v : Fin d → ℕ) (hv : v ∈ S) :
      norm N * ((quotient N v).card : ℝ) ≤ A * ∏ i, 1 / ((v i : ℝ) - 1) := by
    have hp := mem_actualPrimeBoxTuples_iff.mp (mem_filter.mp hv).1
    have hD := fixedProduct_two_le hd v (fun i => (hp i).1)
    have hrecip : 1 / ((∏ i, v i : ℕ) : ℝ) ≤ ∏ i, 1 / ((v i : ℝ) - 1) := by
      calc
        _ = ∏ i, 1 / (v i : ℝ) := by simp [one_div, Nat.cast_prod]
        _ ≤ _ := by
          apply Finset.prod_le_prod
          · intro i hi
            positivity
          · intro i hi
            have h1 : (1 : ℝ) < v i := by exact_mod_cast (hp i).1.one_lt
            exact one_div_le_one_div_of_le (sub_pos.mpr h1) (by linarith)
    exact (hquot _ hD).trans (by
      change A / ((∏ i, v i : ℕ) : ℝ) ≤ _
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hrecip hA.le)
  calc
    _ ≤ norm N * ∑ v ∈ S, ((quotient N v).card : ℝ) :=
      mul_le_mul_of_nonneg_left hc hnorm
    _ = _ := mul_sum ..
    _ ≤ ∑ v ∈ S, A * ∏ i, 1 / ((v i : ℝ) - 1) := sum_le_sum hrow
    _ = A * actualPrimeAffineWallStripMass N (fun _ : Fin d => cutExponent)
        (fun _ => cutExponent + 2) L c δ := (mul_sum ..).symm
    _ ≤ ε := by
      have hh := (lt_div_iff₀ hA).mp (H N hT)
      linarith only [mul_comm A (actualPrimeAffineWallStripMass N
        (fun _ : Fin d => cutExponent) (fun _ => cutExponent + 2) L c δ), hh]

end
end ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall
