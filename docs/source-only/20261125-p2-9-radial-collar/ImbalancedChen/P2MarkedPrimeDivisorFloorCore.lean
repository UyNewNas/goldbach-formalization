import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The existing prime-divisor floor lemma, relocated from the classical
fixed-clamp geometry owner without changing its statement or fully
qualified name. Only the two list-membership proof terms are expressed
with simp. This supplies no new counting or analytic estimate.
-/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry
noncomputable section

theorem prime_divisor_floor {L : List ℕ} {z : ℝ}
    (hL : ∀q∈L,q.Prime ∧ z≤(q:ℝ)) (v : ℕ) (hv : v.Prime) (hd : v∣L.prod) : z≤(v:ℝ) := by
  induction L with
  | nil => exact (hv.not_dvd_one hd).elim
  | cons p L ih =>
    rcases hv.dvd_mul.mp hd with h | h
    · have hp := hL p (by simp)
      rw [(Nat.prime_dvd_prime_iff_eq hv hp.1).mp h]
      exact hp.2
    · exact ih (fun q hq => hL q (by simp only [List.mem_cons]; exact Or.inr hq)) h

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry
