import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Lean.Elab.Tactic.Omega

namespace P26LocalMomentStructural
open scoped BigOperators

theorem sum_piAntidiag_univ_fin_succ {B : Type*} [AddCommMonoid B]
    (n k : ℕ) (F : (Fin (n + 1) → ℕ) → B) :
    (∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) k, F e) =
      ∑ j : Fin (k + 1),
        ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) (k - j.val),
          F (Fin.cons j.val e) := by
  classical
  have hsum (e : Fin (n + 1) → ℕ)
      (he : e ∈ Finset.piAntidiag Finset.univ k) :
      e 0 + (∑ r : Fin n, e r.succ) = k := by
    simpa only [Fin.sum_univ_succ] using (Finset.mem_piAntidiag.mp he).1
  let split : ∀ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) k,
      Σ _ : Fin (k + 1), Fin n → ℕ :=
    fun e he => ⟨⟨e 0, by have hs := hsum e he; omega⟩, Fin.tail e⟩
  rw [Finset.sum_sigma']
  refine Finset.sum_bij split ?_ ?_ ?_ ?_
  · intro e he
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_piAntidiag.mpr ⟨?_, ?_⟩⟩
    · change (∑ r : Fin n, e r.succ) = k - e 0
      have hs := hsum e he
      omega
    · intro r _
      exact Finset.mem_univ r
  · intro e₁ he₁ e₂ he₂ h
    have h0 := congrArg (fun p : Σ _ : Fin (k + 1), Fin n → ℕ => p.1.val) h
    have ht := congrArg (fun p : Σ _ : Fin (k + 1), Fin n → ℕ => p.2) h
    change e₁ 0 = e₂ 0 at h0
    change Fin.tail e₁ = Fin.tail e₂ at ht
    calc
      e₁ = Fin.cons (e₁ 0) (Fin.tail e₁) := (Fin.cons_self_tail e₁).symm
      _ = Fin.cons (e₂ 0) (Fin.tail e₂) := by rw [h0, ht]
      _ = e₂ := Fin.cons_self_tail e₂
  · intro b hb
    rcases b with ⟨j, e⟩
    have he : e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) (k - j.val) :=
      (Finset.mem_sigma.mp hb).2
    have hm : Fin.cons j.val e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) k := by
      apply Finset.mem_piAntidiag.mpr
      refine ⟨?_, fun r _ => Finset.mem_univ r⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [(Finset.mem_piAntidiag.mp he).1]
      omega
    refine ⟨Fin.cons j.val e, hm, ?_⟩
    simp only [split, Fin.cons_zero, Fin.tail_cons]
  · intro e he
    change F e = F (Fin.cons (e 0) (Fin.tail e))
    rw [Fin.cons_self_tail]

end P26LocalMomentStructural

#print axioms P26LocalMomentStructural.sum_piAntidiag_univ_fin_succ
