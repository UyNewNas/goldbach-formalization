import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Mechanical dependency extraction for the original marked-prime-product
fibre bound. The two Part3 definitions and the private/public P5z proof
blocks below are byte-identical to their registered owner preimages.
All public fully qualified names are retained. The private helper is
re-owned by this module, so its generated private name changes.

This module has only standard Mathlib imports. The corresponding original
owners must select their registered postimages when combined with it.
No product-map injectivity, squarefree restriction or new estimate is added.
-/
namespace ImbalancedChen

noncomputable section
open scoped BigOperators
open Classical

namespace Part3

/-- Labelled prime tuples, retaining repeated primes and their slot order. -/
def labelledPrimeTuples (k P : ℕ) : Finset (Fin k → Fin (P + 1)) :=
  Finset.univ.filter (fun t => ∀ i : Fin k, Nat.Prime (t i).val)

def labelledProduct {k P : ℕ} (t : Fin k → Fin (P + 1)) : ℕ :=
  ∏ i : Fin k, (t i).val

end Part3

private theorem p5z_prime_dvd_tuple_exists {rank P : ℕ}
    (u : Fin rank → Fin (P + 1)) (hu : ∀ i, Nat.Prime (u i).val)
    {p : ℕ} (hp : Nat.Prime p) (hd : p ∣ Part3.labelledProduct u) :
    ∃ i : Fin rank, p = (u i).val := by
  have haux (s : Finset (Fin rank)) :
      p ∣ ∏ i ∈ s, (u i).val → ∃ i ∈ s, p = (u i).val := by
    induction s using Finset.induction_on with
    | empty =>
        intro h
        simp only [Finset.prod_empty] at h
        exact (hp.ne_one (Nat.dvd_one.mp h)).elim
    | @insert i s hi ih =>
        intro h
        rw [Finset.prod_insert hi] at h
        rcases hp.dvd_mul.mp h with hpi | hrest
        · exact ⟨i, Finset.mem_insert_self _ _, (Nat.prime_dvd_prime_iff_eq hp (hu i)).mp hpi⟩
        · obtain ⟨j, hj, heq⟩ := ih hrest
          exact ⟨j, Finset.mem_insert_of_mem hj, heq⟩
  obtain ⟨i, _, heq⟩ := haux Finset.univ hd
  exact ⟨i, heq⟩

/-- No injection of the product map is asserted. A fibre has at most
rank^rank tuples, since every prime slot equals one of a witness's rank
prime values. The proof also works when primes repeat. -/
theorem p5z_marked_prime_product_fibre_card_le {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (m : ℕ) : (S.filter (fun t => Part3.labelledProduct t = m)).card ≤ rank ^ rank := by
  let F := S.filter (fun t => Part3.labelledProduct t = m)
  change F.card ≤ rank ^ rank
  by_cases hF : F = ∅
  · simp only [hF, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  have huS := (Finset.mem_filter.mp hu).1
  have hup : ∀ i, Nat.Prime (u i).val := (Finset.mem_filter.mp (hS huS)).2
  let T := Finset.univ.image (fun i : Fin rank => (u i).val)
  have hT : T.card ≤ rank := (Finset.card_image_le).trans (by simp)
  have hchoice (v : F) (i : Fin rank) : (v.val i).val ∈ T := by
    have hvS := (Finset.mem_filter.mp v.property).1
    have hvp : Nat.Prime (v.val i).val := (Finset.mem_filter.mp (hS hvS)).2 i
    have hprod : Part3.labelledProduct v.val = Part3.labelledProduct u :=
      (Finset.mem_filter.mp v.property).2.trans (Finset.mem_filter.mp hu).2.symm
    have hd : (v.val i).val ∣ Part3.labelledProduct u := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (fun j => (v.val j).val) (Finset.mem_univ i)
    obtain ⟨j, heq⟩ := p5z_prime_dvd_tuple_exists u hup hvp hd
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩
  let encode : F → (Fin rank → T) := fun v i => ⟨(v.val i).val, hchoice v i⟩
  have hinj : Function.Injective encode := by
    intro v w hvw
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun g : Fin rank → T => (g i).val) hvw
  have hcard := Fintype.card_le_of_injective encode hinj
  have hbound : F.card ≤ T.card ^ rank := by
    simpa only [Fintype.card_pi_const, Fintype.card_coe] using hcard
  exact hbound.trans (pow_le_pow_left₀ (Nat.zero_le _) hT rank)

end
end ImbalancedChen
