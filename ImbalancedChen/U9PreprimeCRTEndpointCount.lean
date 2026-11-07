import ImbalancedChen.U9OriginalPreprimeRow
import Mathlib.Data.Int.CardIntervalMod

/-!
# Exact complete-modulus residue and endpoint counts for the original U9 row

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The modulus is lcm(lcm(d,e),N), not a squarefree surrogate. Enumerating its
admissible residues retains the actual centre mask, arbitrary common
factors between d,e,N, and every compatibility obstruction. The count in
each residue is the exact rational-ceiling endpoint difference supplied
by pinned Mathlib, at the factor-dependent ORIGINAL row endpoints.
No density approximation or prime AP estimate is a hypothesis.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section
open Classical
open scoped BigOperators

def rowModulus (N d e : ℕ) : ℕ := Nat.lcm (Nat.lcm d e) N

def residueGate (N p q d e a : ℕ) : Prop :=
  Nat.Coprime a N ∧ Nat.ModEq d (p * a * q) N ∧ e ∣ a

def rowResidues (N p q d e : ℕ) : Finset ℕ :=
  (Finset.range (rowModulus N d e)).filter (residueGate N p q d e)

def rowAPDiv (N : ℕ) (X : ℝ) (p q d e : ℕ) : Finset ℕ :=
  (preprimeRow N X p q).filter fun r => Nat.ModEq d (p * r * q) N ∧ e ∣ r

private theorem gate_transport {N p q d e r a : ℕ}
    (h : Nat.ModEq (rowModulus N d e) r a) :
    residueGate N p q d e r ↔ residueGate N p q d e a := by
  have hd : d ∣ rowModulus N d e :=
    (Nat.dvd_lcm_left d e).trans (Nat.dvd_lcm_left (Nat.lcm d e) N)
  have he : e ∣ rowModulus N d e :=
    (Nat.dvd_lcm_right d e).trans (Nat.dvd_lcm_left (Nat.lcm d e) N)
  have hN : N ∣ rowModulus N d e := Nat.dvd_lcm_right _ _
  have hc : Nat.Coprime r N ↔ Nat.Coprime a N := by
    change Nat.gcd r N = 1 ↔ Nat.gcd a N = 1
    rw [(h.of_dvd hN).gcd_eq]
  have hp : Nat.ModEq d (p * r * q) (p * a * q) :=
    ((h.of_dvd hd).mul_left p).mul_right q
  have hAP : Nat.ModEq d (p * r * q) N ↔ Nat.ModEq d (p * a * q) N :=
    ⟨fun hr => hp.symm.trans hr, fun ha => hp.trans ha⟩
  have hv : e ∣ r ↔ e ∣ a := by
    constructor
    · intro hr
      exact Nat.modEq_zero_iff_dvd.mp
        ((h.of_dvd he).symm.trans (Nat.modEq_zero_iff_dvd.mpr hr))
    · intro ha
      exact Nat.modEq_zero_iff_dvd.mp
        ((h.of_dvd he).trans (Nat.modEq_zero_iff_dvd.mpr ha))
  unfold residueGate
  rw [hc, hAP, hv]

/-- Exact residue-class cardinal, expressed in integer ceilings so empty
or reversed endpoint intervals require no separate error term. -/
def endpointCount (A B M a : ℕ) : ℤ :=
  max (Int.ceil (((B : ℚ) - (a : ℚ)) / (M : ℚ)) -
    Int.ceil (((A : ℚ) - (a : ℚ)) / (M : ℚ))) 0

/-- Concrete finite CRT/endpoint identity at the unchanged old row.
All original complementary factor labels p,q occur on both sides. -/
theorem rowAPDiv_card_eq_exact_residue_endpoints {N p q d e : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) (he : 0 < e) :
    ((rowAPDiv N X p q d e).card : ℤ) =
      ∑ a ∈ rowResidues N p q d e,
        endpointCount (rowLower N X p q) (rowUpper N p q)
          (rowModulus N d e) a := by
  have hN : 0 < N :=
    (mem_chenAdditivePrimeCarrier.mp hf.1).2.1.pos.trans
      (mem_chenAdditivePrimeCarrier.mp hf.1).1
  have hM : 0 < rowModulus N d e := Nat.lcm_pos (Nat.lcm_pos hd he) hN
  let I := Finset.Ico (rowLower N X p q) (rowUpper N p q)
  let S := I.filter (residueGate N p q d e)
  have hsource : rowAPDiv N X p q d e = S := by
    rw [rowAPDiv, preprimeRow_eq_interval_coprime hf hX]
    ext r
    simp only [S, I, Finset.mem_filter, residueGate]
    tauto
  rw [hsource]
  have hmap : ∀ r ∈ S, r % rowModulus N d e ∈ rowResidues N p q d e := by
    intro r hr
    have hmod : Nat.ModEq (rowModulus N d e) r (r % rowModulus N d e) := by
      simp only [Nat.ModEq, Nat.mod_mod]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hM),
      (gate_transport hmod).mp (Finset.mem_filter.mp hr).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := S) (f := fun r => r % rowModulus N d e)
    (t := rowResidues N p q d e) hmap
  rw [hcard, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨haM, haGate⟩ := Finset.mem_filter.mp ha
  have haLt := Finset.mem_range.mp haM
  have hfilter : S.filter (fun r => r % rowModulus N d e = a) =
      I.filter (fun r => Nat.ModEq (rowModulus N d e) r a) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, hrem⟩
      refine ⟨(Finset.mem_filter.mp hr).1, ?_⟩
      change r % rowModulus N d e = a % rowModulus N d e
      rw [Nat.mod_eq_of_lt haLt]
      exact hrem
    · rintro ⟨hr, hmod⟩
      refine ⟨Finset.mem_filter.mpr ⟨hr, (gate_transport hmod).mpr haGate⟩, ?_⟩
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt haLt] using hmod
  rw [hfilter]
  exact Nat.Ico_filter_modEq_card (rowLower N X p q) (rowUpper N p q) hM a

/-- A sieving prime dividing the selected AP modulus or N is an exact
zero obstruction, before any interval or density estimate. -/
theorem rowAPDiv_prime_eq_empty {N p q d ℓ : ℕ} {X : ℝ}
    (hℓ : Nat.Prime ℓ) (hNd : Nat.Coprime N d)
    (hlocal : ℓ ∣ d ∨ ℓ ∣ N) : rowAPDiv N X p q d ℓ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hrow, hAP, hℓr⟩ := Finset.mem_filter.mp hr
  have hf : factorAllowed N p q := by
    by_contra hn
    simpa only [preprimeRow, if_neg hn, Finset.notMem_empty] using hrow
  rw [preprimeRow, if_pos hf] at hrow
  have hrcopN := (Finset.mem_filter.mp hrow).2.2.1
  rcases hlocal with hℓd | hℓN
  · have hprod : Nat.Coprime (p * r * q) d := by
      change Nat.gcd (p * r * q) d = 1
      rw [hAP.gcd_eq, hNd.gcd_eq_one]
    have hrcop := (Nat.coprime_mul_iff_left.mp
      (Nat.coprime_mul_iff_left.mp hprod).1).2
    have hbad := Nat.dvd_gcd hℓr hℓd
    rw [hrcop.gcd_eq_one] at hbad
    exact hℓ.ne_one (Nat.dvd_one.mp hbad)
  · have hbad := Nat.dvd_gcd hℓr hℓN
    rw [hrcopN.gcd_eq_one] at hbad
    exact hℓ.ne_one (Nat.dvd_one.mp hbad)

end
end ImbalancedChen.U9SemiprimeSwitch
