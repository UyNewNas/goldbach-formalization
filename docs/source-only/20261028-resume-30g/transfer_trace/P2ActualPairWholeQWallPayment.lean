import ImbalancedChen.P2ActualPairJointPrefixWallCarrier

/-!
# Whole physical pair/rough q payment on fixed JOINT prefix walls

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual U6 pair is part of the physical modulus B=(p1*p2)*r and part
of the affine wall's variables. All target-deleted residual moduli are
summed AFTER the genuine joint-prefix/tail phi factorization. A full-q
fibre is injective by the original A/H/D bands, so its actual signed
rounded-minus-raw rough coefficient is bounded by two; no aggregate bound
is inserted as a premise. This is a rough physical coefficient payment,
not an assertion that the full beta-attached absolute norm is bounded by
the rough Euler constant or that the final same-rho density is proved.
-/

namespace ImbalancedChen.P2ActualPairWholeQWallPayment

noncomputable section
open scoped Classical BigOperators
open P2ActualPairJointPrefixWallCarrier P2CanonicalWallFullResidualPayment
open P2LowerFiniteCellRounding P2ActualResidualUniverseMass
open P5SelectedMaskTransport

def jointWallMarks {j k : ℕ} (N enum : ℕ) (omega : ℝ)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (sixthSupport N ×ˢ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent)).filter
    (fun x => j ≤ x.2.primeFactorsList.length ∧
      actualPrimeTupleLog N (jointPrefix j x.1 x.2) ∈ primeAffineWallStrip L c delta)

def physicalProduct (x : (ℕ × ℕ) × ℕ) : ℕ := (x.1.1 * x.1.2) * x.2

def jointWallProducts {j k : ℕ} (N enum : ℕ) (omega : ℝ)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) : Finset ℕ :=
  (jointWallMarks N enum omega L c delta).image physicalProduct

/-- Actual full q, including both external primes, enters the exact E
arithmetic product image. The pairRoot has NOT become a varying intercept. -/
theorem jointWallProducts_subset_lifted {j k : ℕ} {N : ℕ} (hN : 1 < (N : ℝ))
    (enum : ℕ) (omega : ℝ) (homega : omega ≤ aExponent)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    jointWallProducts N enum omega L c delta ⊆
      liftedModuli N enum (fun _ => omega) (fun _ => dExponent)
        ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) L c delta := by
  intro B hB
  obtain ⟨⟨p, r⟩, hmark, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨hpair, hj, hwall⟩ := Finset.mem_filter.mp hmark
  obtain ⟨hp, hr⟩ := Finset.mem_product.mp hpair
  obtain ⟨htuple, hinj, htail, hcop, hrec⟩ := joint_prefix_tail_data hN hp homega hr hj
  apply Finset.mem_image.mpr
  refine ⟨(jointPrefix j p r, canonicalTail j r), ?_, hrec⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨htuple, hwall⟩, htail⟩, hinj, hcop⟩

/-- Entire physical-q reciprocal-totient mass, already summed over ALL
external U6 pairs and ALL residual moduli. No per-modulus shortcut. -/
theorem whole_q_mass_le_joint_strip_mul_full_residual {j k : ℕ}
    {N : ℕ} (hN : 1 < (N : ℝ)) (enum : ℕ) (omega : ℝ) (homega : omega ≤ aExponent)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    (∑ B ∈ jointWallProducts N enum omega L c delta, 1 / (Nat.totient B : ℝ)) ≤
      actualPrimeAffineWallStripMass N (fun _ => omega) (fun _ => dExponent) L c delta *
        mass N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) := by
  apply le_trans ?_ (lifted_mass_le_strip_mul_residual N enum _ _ _ _ L c delta)
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (jointWallProducts_subset_lifted hN enum omega homega L c delta)
  intro B _ _
  positivity

def markDifference (keep : ℕ × ℕ → List ℕ → Bool) (N enum : ℕ) (omega tau : ℝ)
    (x : (ℕ × ℕ) × ℕ) : ℝ :=
  coefficient (keep x.1) N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) tau x.2 -
    raw (keep x.1) N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) x.2

theorem markDifference_abs_le_two (keep : ℕ × ℕ → List ℕ → Bool)
    (N enum : ℕ) (omega tau : ℝ) (x : (ℕ × ℕ) × ℕ) :
    |markDifference keep N enum omega tau x| ≤ 2 := by
  have hc := coefficient_abs_le_one (keep x.1) N enum
    ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) tau x.2
  have hr := fixedEvenRoughCoefficient_abs_le_one (keep x.1) N enum
    ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) x.2
  have ht := abs_sub_le (coefficient (keep x.1) N enum
    ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) tau x.2) 0
      (raw (keep x.1) N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) x.2)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  change |markDifference keep N enum omega tau x| ≤ 2
  unfold markDifference
  have hr' : |raw (keep x.1) N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent) x.2| ≤ 1 := hr
  exact ht.trans (by linarith)

/-- Independently defined full physical q fibre of the actual mark
differences. Its coefficients are not defined by a desired density value. -/
def physicalWallDifference {j k : ℕ} (keep : ℕ × ℕ → List ℕ → Bool)
    (N enum : ℕ) (omega tau : ℝ)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) (B : ℕ) : ℝ :=
  ∑ x ∈ jointWallMarks N enum omega L c delta with physicalProduct x = B,
    markDifference keep N enum omega tau x

theorem physicalWallDifference_at_product {j k : ℕ}
    (keep : ℕ × ℕ → List ℕ → Bool) (N enum : ℕ) (omega tau : ℝ)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    {x : (ℕ × ℕ) × ℕ} (hx : x ∈ jointWallMarks N enum omega L c delta) :
    physicalWallDifference keep N enum omega tau L c delta (physicalProduct x) =
      markDifference keep N enum omega tau x := by
  unfold physicalWallDifference
  rw [Finset.sum_eq_single x]
  · intro y hy hne
    obtain ⟨hywall, heq⟩ := Finset.mem_filter.mp hy
    exact (hne ((pair_rough_product_injOn N enum omega)
      (Finset.mem_filter.mp hywall).1 (Finset.mem_filter.mp hx).1 heq)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hx, rfl⟩)).elim

theorem physicalWallDifference_abs_le_two {j k : ℕ}
    (keep : ℕ × ℕ → List ℕ → Bool) (N enum : ℕ) (omega tau : ℝ)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ)
    {B : ℕ} (hB : B ∈ jointWallProducts N enum omega L c delta) :
    |physicalWallDifference keep N enum omega tau L c delta B| ≤ 2 := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hB
  rw [physicalWallDifference_at_product keep N enum omega tau L c delta hx]
  exact markDifference_abs_le_two keep N enum omega tau x

def wholeQWallCharge {j k : ℕ} (keep : ℕ × ℕ → List ℕ → Bool)
    (N enum : ℕ) (omega tau : ℝ)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) : ℝ :=
  ∑ B ∈ jointWallProducts N enum omega L c delta,
    |physicalWallDifference keep N enum omega tau L c delta B| / (Nat.totient B : ℝ)

theorem wholeQWallCharge_le_joint_strip {j k : ℕ}
    (keep : ℕ × ℕ → List ℕ → Bool) {N : ℕ} (hN : 1 < (N : ℝ))
    (enum : ℕ) (omega tau : ℝ) (homega : omega ≤ aExponent)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (delta : ℝ) :
    wholeQWallCharge keep N enum omega tau L c delta ≤
      2 * (actualPrimeAffineWallStripMass N (fun _ => omega) (fun _ => dExponent) L c delta *
        mass N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ aExponent)) := by
  apply le_trans ?_ (mul_le_mul_of_nonneg_left
    (whole_q_mass_le_joint_strip_mul_full_residual hN enum omega homega L c delta) (by norm_num))
  unfold wholeQWallCharge
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  simpa only [mul_one_div] using div_le_div_of_nonneg_right
    (physicalWallDifference_abs_le_two keep N enum omega tau L c delta hB)
      (Nat.cast_nonneg (Nat.totient B))

/-- Fixed JOINT affine forms and fixed cap heights choose delta BEFORE N.
All external pairs, all residual moduli, all later policies and fine meshes
are already included. No varying pairRoot intercept is used. -/
theorem exists_uniform_whole_q_joint_wall_payment {j k : ℕ}
    (omega : ℝ) (homega : 0 < omega) (hgap : omega < aExponent)
    (L : Fin k → (Fin (2 + j) → ℝ) →L[ℝ] ℝ) (c : Fin k → ℝ) (hL : ∀ i, L i ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ enum : ℕ,
      ∀ (keep : ℕ × ℕ → List ℕ → Bool) (tau : ℝ),
        wholeQWallCharge keep N enum omega tau L c delta < eta := by
  obtain ⟨C, hC, Nm, hNm, hmass⟩ :=
    exists_eventual_uniform_mass_bound omega aExponent homega hgap
  have hD : omega < dExponent := hgap.trans (by norm_num [aExponent, dExponent])
  obtain ⟨delta, hd, Ns, hNs, hstrip⟩ :=
    exists_actualPrimeAffineWallStrip_mass_lt homega hD L c hL
      (eta / (2 * C)) (by positivity)
  refine ⟨delta, hd, max Nm Ns, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven enum keep tau
  have hN2 : 2 ≤ N := hNm.trans ((le_max_left _ _).trans hN)
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hm := hmass N ((le_max_left _ _).trans hN) hEven enum
  have hs := hstrip N ((le_max_right _ _).trans hN)
  have hS : 0 ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin (2 + j) => omega) (fun _ => dExponent) L c delta := by
    unfold actualPrimeAffineWallStripMass
    exact Finset.sum_nonneg (fun p hp => actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1)
  have hmul := mul_le_mul_of_nonneg_left hm hS
  have hs' := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hs
  have hq := wholeQWallCharge_le_joint_strip keep hNR enum omega tau hgap.le L c delta
  nlinarith

end
end ImbalancedChen.P2ActualPairWholeQWallPayment
