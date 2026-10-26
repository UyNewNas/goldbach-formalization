import ImbalancedChen.U9PreprimeCRTEndpointCount

/-!
# The true ordinary local obstruction of the unsieved original U9 row

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every admissible residue carries the original centre mask and product-AP
condition. In a complete new coprime local block, exactly one of its ell
lifts is divisible by ell. Thus the unsieved integer local density is
1/ell, not the prime-product receiver density 1/(ell-1). The zero case is
kept absolute; empty admissible sets are never divided by their mass.
The preceding exact endpoint formula supplies the finite row boundaries.
No matching row sieve or prime progression saving is claimed.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section
open Classical
open scoped BigOperators

def residueLift (A : Finset ℕ) (D ell : ℕ) : Finset ℕ :=
  (Finset.range (D * ell)).filter fun r => r % D ∈ A

def residueLiftZero (A : Finset ℕ) (D ell : ℕ) : Finset ℕ :=
  (residueLift A D ell).filter fun r => ell ∣ r

private theorem complete_AP_card (D ell a : ℕ) (hD : 0 < D) :
    ((Finset.range (D * ell)).filter (fun r => Nat.ModEq D r a)).card = ell := by
  have h := Nat.count_modEq_card (D * ell) hD a
  simpa only [Nat.count_eq_card_filter_range, Nat.mul_div_cancel_left ell hD,
    Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, Nat.not_lt_zero,
    if_false, Nat.add_zero] using h

/-- Exactly one forbidden lift, constructed by the genuine CRT supplier. -/
private theorem complete_AP_zero_card {D ell : ℕ} (hD : 0 < D) (hell : 0 < ell)
    (hcop : Nat.Coprime D ell) (a : ℕ) :
    ((Finset.range (D * ell)).filter
      (fun r => Nat.ModEq D r a ∧ ell ∣ r)).card = 1 := by
  let b := Nat.chineseRemainder hcop a 0
  have hb : b.val < D * ell := Nat.chineseRemainder_lt_mul hcop a 0 hD.ne' hell.ne'
  have hset : (Finset.range (D * ell)).filter
      (fun r => Nat.ModEq D r a ∧ ell ∣ r) = {b.val} := by
    ext r
    constructor
    · intro hr
      obtain ⟨hrB, hrA, hrell⟩ := Finset.mem_filter.mp hr
      have hmod := Nat.chineseRemainder_modEq_unique hcop hrA
        (Nat.modEq_zero_iff_dvd.mpr hrell)
      have heq : r = b.val := by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp hrB),
          Nat.mod_eq_of_lt hb] using hmod
      exact Finset.mem_singleton.mpr heq
    · intro hr
      have heq := Finset.mem_singleton.mp hr
      subst r
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, b.prop.1,
        Nat.modEq_zero_iff_dvd.mp b.prop.2⟩
  rw [hset, Finset.card_singleton]

private theorem lift_fibre_eq {A : Finset ℕ} {D ell a : ℕ}
    (ha : a ∈ A) (haD : a < D) :
    (residueLift A D ell).filter (fun r => r % D = a) =
      (Finset.range (D * ell)).filter (fun r => Nat.ModEq D r a) := by
  ext r
  simp only [residueLift, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hr, _⟩, hrem⟩
    refine ⟨hr, ?_⟩
    change r % D = a % D
    rwa [Nat.mod_eq_of_lt haD]
  · rintro ⟨hr, hmod⟩
    have hrem : r % D = a := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt haD] using hmod
    exact ⟨⟨hr, by simpa only [hrem] using ha⟩, hrem⟩

private theorem lift_zero_fibre_eq {A : Finset ℕ} {D ell a : ℕ}
    (ha : a ∈ A) (haD : a < D) :
    (residueLiftZero A D ell).filter (fun r => r % D = a) =
      (Finset.range (D * ell)).filter (fun r => Nat.ModEq D r a ∧ ell ∣ r) := by
  ext r
  simp only [residueLiftZero, residueLift, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨hr, _⟩, hdiv⟩, hrem⟩
    refine ⟨hr, ?_, hdiv⟩
    change r % D = a % D
    rwa [Nat.mod_eq_of_lt haD]
  · rintro ⟨hr, hmod, hdiv⟩
    have hrem : r % D = a := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt haD] using hmod
    exact ⟨⟨⟨hr, by simpa only [hrem] using ha⟩, hdiv⟩, hrem⟩

theorem residueLift_card (A : Finset ℕ) {D ell : ℕ} (hD : 0 < D)
    (hA : A ⊆ Finset.range D) : (residueLift A D ell).card = A.card * ell := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun r => r % D) (t := A)
    (fun r hr => (Finset.mem_filter.mp hr).2)]
  calc
    _ = ∑ _a ∈ A, ell := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [lift_fibre_eq ha (Finset.mem_range.mp (hA ha))]
      exact complete_AP_card D ell a hD
    _ = _ := by simp

theorem residueLiftZero_card (A : Finset ℕ) {D ell : ℕ} (hD : 0 < D)
    (hell : 0 < ell) (hcop : Nat.Coprime D ell) (hA : A ⊆ Finset.range D) :
    (residueLiftZero A D ell).card = A.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun r => r % D) (t := A)
    (fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2)]
  calc
    _ = ∑ _a ∈ A, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [lift_zero_fibre_eq ha (Finset.mem_range.mp (hA ha))]
      exact complete_AP_zero_card hD hell hcop a
    _ = _ := by simp

/-- The original centre/AP admissibility mask, on its exact full modulus,
has precisely ell lifts per admitted old residue and one forbidden lift.
This remains meaningful when that original mask admits no residues. -/
theorem original_local_block_counts {N p q d ell : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hell : Nat.Prime ell)
    (hellD : ¬ell ∣ d) (hellN : ¬ell ∣ N) :
    let D := rowModulus N d 1
    let A := rowResidues N p q d 1
    (residueLift A D ell).card = A.card * ell ∧
      (residueLiftZero A D ell).card = A.card := by
  intro D A
  have hD : 0 < D := Nat.lcm_pos (Nat.lcm_pos hd zero_lt_one) hN
  have hA : A ⊆ Finset.range D := Finset.filter_subset _ _
  have hdiv : D ∣ d * N := by
    simpa only [D, rowModulus, Nat.lcm_one_right] using Nat.lcm_dvd_mul d N
  have hcop : Nat.Coprime D ell := by
    apply Nat.Coprime.symm
    apply hell.coprime_iff_not_dvd.mpr
    intro h
    rcases hell.dvd_mul.mp (h.trans hdiv) with h | h
    · exact hellD h
    · exact hellN h
  exact ⟨residueLift_card A hD hA, residueLiftZero_card A hD hell.pos hcop hA⟩

/-- The true local integer density on a NONEMPTY original masked block.
No assertion about distribution across incomplete rows is made here. -/
theorem original_local_density {N p q d ell : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hell : Nat.Prime ell)
    (hellD : ¬ell ∣ d) (hellN : ¬ell ∣ N)
    (hA : (rowResidues N p q d 1).Nonempty) :
    ((residueLiftZero (rowResidues N p q d 1) (rowModulus N d 1) ell).card : ℝ) /
      ((residueLift (rowResidues N p q d 1) (rowModulus N d 1) ell).card : ℝ) =
        1 / (ell : ℝ) := by
  obtain ⟨hfull, hzero⟩ := original_local_block_counts
    (p := p) (q := q) hN hd hell hellD hellN
  rw [hfull, hzero, Nat.cast_mul]
  have hpos : (0 : ℝ) < (rowResidues N p q d 1).card := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hell0 : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne_zero
  field_simp [hpos.ne', hell0] <;> ring

end
end ImbalancedChen.U9SemiprimeSwitch
