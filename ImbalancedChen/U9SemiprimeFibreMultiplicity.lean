import ImbalancedChen.U9SemiprimeSwitchedPrimeAP
import ImbalancedChen.OrderedBad

/-!
# Exact collision classification for the original U9 semiprime fibres

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two factors grouped into m=p₁*q need not be ordered. Their two possible
labellings are both retained when the ORIGINAL source admits them. Swapping
is not asserted to preserve its bands or its moving square-root cutoff:
the original source filter decides whether the second label really occurs.
Prime squares give a single label, without a squarefreeness hypothesis.

This proves the actual bounded coefficient needed by the switched-prime
family, for every original near-cap parameter X. It supplies no analytical
progression estimate and does not change the original count or its masks.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section

open scoped BigOperators
open Classical

/-- Swap only the two ORIGINAL factors grouped into the semiprime.
Membership of this swapped label must still be checked in the old source. -/
def swap (t : P5zU9Triple) : P5zU9Triple := ⟨(t.2, t.1.2), t.1.1⟩

theorem swap_swap (t : P5zU9Triple) : swap (swap t) = t := by
  rcases t with ⟨⟨p₁, p₂⟩, q⟩
  rfl

theorem key_swap (t : P5zU9Triple) : key (swap t) = key t := by
  simp only [swap, key, Nat.mul_comm]

private theorem triple_ext {t u : P5zU9Triple}
    (h₁ : u.1.1 = t.1.1) (h₂ : u.1.2 = t.1.2) (hq : u.2 = t.2) : u = t := by
  apply Sigma.ext (Prod.ext h₁ h₂)
  exact heq_of_eq hq

/-- These are ALL collisions, not just a chosen family of examples.
The actual prime product uniqueness supplier explicitly allows squares. -/
theorem key_eq_iff_eq_or_swap {N : ℕ} {X : ℝ} {t u : P5zU9Triple}
    (ht : t ∈ labels N X) (hu : u ∈ labels N X) :
    key u = key t ↔ u = t ∨ u = swap t := by
  constructor
  · intro hkey
    have htd := p5z_u9_order_source_data (Finset.mem_filter.mp ht).1
    have hud := p5z_u9_order_source_data (Finset.mem_filter.mp hu).1
    have htp := (chenY9PrimeSelector_ordered_prime_data htd.1).1
    have hup := (chenY9PrimeSelector_ordered_prime_data hud.1).1
    have hprod : u.1.1 * u.2 = t.1.1 * t.2 := congrArg Prod.fst hkey
    have hsecond : u.1.2 = t.1.2 := congrArg Prod.snd hkey
    rcases (prime_mul_eq_prime_mul_iff hup hud.2.2.1 htp htd.2.2.1).mp hprod with
      ⟨hfirst, hlast⟩ | ⟨hfirst, hlast⟩
    · exact Or.inl (triple_ext hfirst hsecond hlast)
    · exact Or.inr (triple_ext hfirst hsecond hlast)
  · rintro (rfl | rfl)
    · rfl
    · exact key_swap t

def fibre (N : ℕ) (X : ℝ) (m r : ℕ) : Finset P5zU9Triple :=
  (labels N X).filter fun t => key t = (m, r)

/-- The complete original fibre is the two candidate labels filtered by
the unchanged source. In particular the swapped label is never inserted
merely because it has the same product. -/
theorem fibre_eq_pair_filter {N : ℕ} {X : ℝ} {t : P5zU9Triple}
    (ht : t ∈ labels N X) :
    fibre N X (key t).1 (key t).2 =
      ({t, swap t} : Finset P5zU9Triple).filter (fun u => u ∈ labels N X) := by
  ext u
  simp only [fibre, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    Prod.eta]
  constructor
  · rintro ⟨hu, heq⟩
    exact ⟨(key_eq_iff_eq_or_swap ht hu).mp heq, hu⟩
  · rintro ⟨heq, hu⟩
    exact ⟨hu, (key_eq_iff_eq_or_swap ht hu).mpr heq⟩

/-- A uniform sharp two-label bound, valid also when a fibre is empty. -/
theorem fibre_card_le_two (N : ℕ) (X : ℝ) (m r : ℕ) :
    (fibre N X m r).card ≤ 2 := by
  by_cases hF : fibre N X m r = ∅
  · simp only [hF, Finset.card_empty]
    omega
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  obtain ⟨htsource, htkey⟩ := Finset.mem_filter.mp ht
  have hsame : fibre N X m r = fibre N X (key t).1 (key t).2 := by rw [htkey]
  rw [hsame, fibre_eq_pair_filter htsource]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans Finset.card_le_two

theorem weight_le_two (N : ℕ) (X : ℝ) (m r : ℕ) : weight N X m r ≤ 2 := by
  change ((fibre N X m r).card : ℝ) ≤ 2
  exact_mod_cast fibre_card_le_two N X m r

theorem abs_weight_le_two (N : ℕ) (X : ℝ) (m r : ℕ) : |weight N X m r| ≤ 2 := by
  rw [abs_of_nonneg (weight_nonneg N X m r)]
  exact weight_le_two N X m r

/-- On the prime-square diagonal, the swapped label is the same original
label and the original coefficient is exactly one, not two. -/
theorem weight_key_eq_one_of_diagonal {N : ℕ} {X : ℝ} {t : P5zU9Triple}
    (ht : t ∈ labels N X) (hdiag : t.1.1 = t.2) :
    weight N X (key t).1 (key t).2 = 1 := by
  have hswap : swap t = t := by
    apply triple_ext
    · exact hdiag.symm
    · rfl
    · exact hdiag
  have hF := fibre_eq_pair_filter ht
  simp only [hswap, Finset.insert_eq_of_mem (Finset.mem_singleton_self t),
    Finset.filter_singleton, ht, if_true] at hF
  change ((fibre N X (key t).1 (key t).2).card : ℝ) = 1
  rw [hF, Finset.card_singleton]
  norm_num

end

end ImbalancedChen.U9SemiprimeSwitch
