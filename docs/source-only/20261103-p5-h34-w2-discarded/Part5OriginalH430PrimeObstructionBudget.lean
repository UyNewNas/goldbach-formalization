import ImbalancedChen.P2OriginalPrefixMaskMass
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite elementary payment for a prime coordinate on one of three endpoint
fibres or dividing the old prefix. The unrestricted second coordinate is
paid by the existing harmonic bound, not a new prime-distribution theorem.
The endpoint/repeat overlap is allowed in this MAJORANT only; the actual
carrier partition in the next file is disjoint. No count licence is assumed.
-/
namespace ImbalancedChen.Part5OriginalH430PrimeObstructionBudget

noncomputable section
open Set Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology

def primePool (N : ℕ) (A : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun p => p.Prime ∧ A ≤ (p : ℝ))

def logCoordinate (N : ℕ) (L : ℝ) (p : ℕ) : ℝ :=
  (Real.log (p : ℝ) / Real.log (N : ℝ)) / L

def endpointFibre (N : ℕ) (A L t : ℝ) : Finset ℕ :=
  (primePool N A).filter (fun p => logCoordinate N L p = t)

def obstructed (N d : ℕ) (L : ℝ) (faces : Fin 3 → ℝ) (p : ℕ) : Prop :=
  p ∣ d ∨ logCoordinate N L p = faces 0 ∨
    logCoordinate N L p = faces 1 ∨ logCoordinate N L p = faces 2

def badPool (N d : ℕ) (A L : ℝ) (faces : Fin 3 → ℝ) : Finset ℕ :=
  (primePool N A).filter (obstructed N d L faces)

def obstructionCount (N : ℕ) : ℝ := Real.log (N : ℝ) / Real.log 2 + 3

def harmonicBudget (N : ℕ) : ℝ := 1 + Real.log (N : ℝ)

@[simp] theorem mem_primePool {N p : ℕ} {A : ℝ} :
    p ∈ primePool N A ↔ 1 ≤ p ∧ p ≤ N ∧ p.Prime ∧ A ≤ (p : ℝ) := by
  simp only [primePool, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem logCoordinate_injective {N : ℕ} {L : ℝ}
    (hN : 1 < N) (hL : 0 < L) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (he : logCoordinate N L p = logCoordinate N L q) : p = q := by
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  have h1 := (div_left_inj' hL.ne').mp he
  have h2 := (div_left_inj' hlog).mp h1
  exact_mod_cast Real.log_injOn_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr hq) h2

theorem endpointFibre_card_le_one {N : ℕ} {A L : ℝ}
    (hN : 1 < N) (hL : 0 < L) (t : ℝ) : (endpointFibre N A L t).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hpt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqt⟩ := Finset.mem_filter.mp hq
  exact logCoordinate_injective hN hL (mem_primePool.mp hp).2.2.1.pos
    (mem_primePool.mp hq).2.2.1.pos (hpt.trans hqt.symm)

/-- Three actual coordinate equalities, not three null-set deletions. -/
theorem badPool_card {N d : ℕ} {A L : ℝ}
    (hN : 1 < N) (hL : 0 < L) (hd : 0 < d) (faces : Fin 3 → ℝ) :
    (badPool N d A L faces).card ≤ d.primeFactors.card + 3 := by
  let R := (primePool N A).filter (fun p => p ∣ d)
  let E0 := endpointFibre N A L (faces 0)
  let E1 := endpointFibre N A L (faces 1)
  let E2 := endpointFibre N A L (faces 2)
  have hR : R ⊆ d.primeFactors := by
    intro p hp
    obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_primePool.mp hp).2.2.1, hpd, hd.ne'⟩
  have he : badPool N d A L faces = ((R ∪ E0) ∪ E1) ∪ E2 := by
    ext p
    simp only [badPool, R, E0, E1, E2, endpointFibre, Finset.mem_filter,
      Finset.mem_union, obstructed]
    tauto
  rw [he]
  have h0 := endpointFibre_card_le_one (A := A) hN hL (faces 0)
  have h1 := endpointFibre_card_le_one (A := A) hN hL (faces 1)
  have h2 := endpointFibre_card_le_one (A := A) hN hL (faces 2)
  have hr := Finset.card_le_card hR
  have hu0 := Finset.card_union_le R E0
  have hu1 := Finset.card_union_le (R ∪ E0) E1
  have hu2 := Finset.card_union_le ((R ∪ E0) ∪ E1) E2
  change E0.card ≤ 1 at h0
  change E1.card ≤ 1 at h1
  change E2.card ≤ 1 at h2
  omega

theorem badPool_reciprocal_le {N d : ℕ} {A L : ℝ}
    (hN : 1 < N) (hL : 0 < L) (hd : 0 < d) (hdN : d ≤ N)
    (hA : 0 < A) (faces : Fin 3 → ℝ) :
    (∑ p ∈ badPool N d A L faces, 1 / (p : ℝ)) ≤ obstructionCount N / A := by
  have hcard : ((badPool N d A L faces).card : ℝ) ≤ obstructionCount N := by
    have hc : ((badPool N d A L faces).card : ℝ) ≤
        (d.primeFactors.card : ℝ) + 3 := by
      exact_mod_cast badPool_card (A := A) hN hL hd faces
    have hlog := Real.log_le_log (Nat.cast_pos.mpr hd) (by exact_mod_cast hdN)
    have hh := div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact hc.trans (add_le_add_right ((chen_primeFactors_card_le_log hd).trans hh) 3)
  calc
    _ ≤ ∑ _p ∈ badPool N d A L faces, 1 / A := by
      apply Finset.sum_le_sum
      intro p hp
      have hAp := (mem_primePool.mp (Finset.mem_filter.mp hp).1).2.2.2
      exact one_div_le_one_div_of_le hA hAp
    _ = ((badPool N d A L faces).card : ℝ) / A := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right hcard hA.le

theorem primePool_reciprocal_le (N : ℕ) (A : ℝ) :
    (∑ p ∈ primePool N A, 1 / (p : ℝ)) ≤ harmonicBudget N := by
  have hsub : primePool N A ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := harmonic_le_one_add_log N

def pairVector (p : ℕ × ℕ) : Fin 2 → ℕ := ![p.1, p.2]

def pairPool (P : Finset ℕ) : Finset (Fin 2 → ℕ) := (P ×ˢ P).image pairVector

theorem pairVector_injective : Function.Injective pairVector := by
  intro p q h
  apply Prod.ext
  · simpa [pairVector] using congrFun h 0
  · simpa [pairVector] using congrFun h 1

theorem mem_pairPool {P : Finset ℕ} {q : Fin 2 → ℕ} :
    q ∈ pairPool P ↔ q 0 ∈ P ∧ q 1 ∈ P := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simpa [pairVector] using Finset.mem_product.mp hp
  · intro h
    refine Finset.mem_image.mpr ⟨(q 0, q 1), Finset.mem_product.mpr h, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem sum_pairPool (P : Finset ℕ) (F : (Fin 2 → ℕ) → ℝ) :
    (∑ q ∈ pairPool P, F q) = ∑ p ∈ P, ∑ q ∈ P, F (pairVector (p,q)) := by
  rw [pairPool, Finset.sum_image]
  · exact Finset.sum_product
  · intro p _ q _ h
    exact pairVector_injective h

/-- Majorize a union of bad-coordinate fibres. The intersection may be
counted twice in this upper bound, never in the exact carrier identity. -/
theorem pair_bad_reciprocal_le (P B : Finset ℕ) (hBP : B ⊆ P)
    (T : Finset (Fin 2 → ℕ)) (hT : ∀ q ∈ T, q 0 ∈ P ∧ q 1 ∈ P)
    (hbad : ∀ q ∈ T, q 0 ∈ B ∨ q 1 ∈ B) :
    (∑ q ∈ T, (1 / (q 0 : ℝ)) * (1 / (q 1 : ℝ))) ≤
      2 * (∑ p ∈ B, 1 / (p : ℝ)) * (∑ p ∈ P, 1 / (p : ℝ)) := by
  let F : (Fin 2 → ℕ) → ℝ := fun q =>
    (if q 0 ∈ B then (1 / (q 0 : ℝ)) * (1 / (q 1 : ℝ)) else 0) +
    (if q 1 ∈ B then (1 / (q 0 : ℝ)) * (1 / (q 1 : ℝ)) else 0)
  have hnonneg : ∀ q, 0 ≤ F q := by
    intro q
    dsimp [F]
    split_ifs <;> positivity
  have hsub : T ⊆ pairPool P := fun q hq => mem_pairPool.mpr (hT q hq)
  have hfilter : P.filter (fun p => p ∈ B) = B := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hBP h,h⟩⟩
  have hs : (∑ p ∈ P, if p ∈ B then 1 / (p : ℝ) else 0) =
      ∑ p ∈ B, 1 / (p : ℝ) := by rw [← Finset.sum_filter, hfilter]
  calc
    _ ≤ ∑ q ∈ T, F q := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases h0 : q 0 ∈ B
      · by_cases h1 : q 1 ∈ B
        · simp only [F, if_pos h0, if_pos h1]
          exact le_add_of_nonneg_right (by positivity)
        · simp [F, h0, h1]
      · have h1 := (hbad q hq).resolve_left h0
        simp [F, h0, h1]
    _ ≤ ∑ q ∈ pairPool P, F q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hnonneg q)
    _ = _ := by
      rw [sum_pairPool]
      simp only [F, pairVector, Matrix.cons_val_zero, Matrix.cons_val_one]
      have he (p q : ℕ) :
          (if p ∈ B then (1/(p:ℝ))*(1/(q:ℝ)) else 0) +
            (if q ∈ B then (1/(p:ℝ))*(1/(q:ℝ)) else 0) =
          (if p ∈ B then 1/(p:ℝ) else 0)*(1/(q:ℝ)) +
            (1/(p:ℝ))*(if q ∈ B then 1/(q:ℝ) else 0) := by
        split_ifs <;> simp
      simp_rw [he]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [hs]
      ring

/-- An explicit vanishing budget, using only the existing log/power limit.
This is a threshold selection, not a replacement proof of that library input. -/
def removalRate (a : ℝ) (N : ℕ) : ℝ :=
  obstructionCount N * harmonicBudget N / (N : ℝ)^a

theorem removalRate_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (removalRate a) atTop (𝓝 0) := by
  have h0 := tendsto_nat_log_pow_div_rpow 0 ha
  have h1 := tendsto_nat_log_pow_div_rpow 1 ha
  have h2 := tendsto_nat_log_pow_div_rpow 2 ha
  have hh := ((h2.div_const (Real.log 2)).add
    ((h1.const_mul (1 / Real.log 2 + 3)).add (h0.const_mul 3)))
  convert hh using 1
  · funext N
    simp only [removalRate, obstructionCount, harmonicBudget, pow_zero, pow_one]
    ring
  · simp

end
end ImbalancedChen.Part5OriginalH430PrimeObstructionBudget
