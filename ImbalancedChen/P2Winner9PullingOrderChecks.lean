import ImbalancedChen.P2Winner9SeedArchiveChecks

/-! Small adjacent-key checks compose without deciding the complete finite family. -/

namespace ImbalancedChen.P2Winner9PullingOrderChecks

def Consecutive (P : ℕ → Prop) (first count : ℕ) : Prop :=
  ∀ i : Fin count, P (first + i.val)

instance (P : ℕ → Prop) [DecidablePred P] (first count : ℕ) :
    Decidable (Consecutive P first count) := by
  unfold Consecutive
  infer_instance

namespace Consecutive

theorem append {P : ℕ → Prop} {first n m : ℕ}
    (hx : Consecutive P first n) (hy : Consecutive P (first + n) m) :
    Consecutive P first (n + m) := by
  intro i
  by_cases hn : i.val < n
  · exact hx ⟨i.val, hn⟩
  · have hp : i.val - n < m := by omega
    have he : first + n + (i.val - n) = first + i.val := by omega
    simpa only [he] using hy ⟨i.val - n, hp⟩

theorem strictMono {key : ℕ → ℕ} {n : ℕ}
    (h : Consecutive (fun k => key k < key (k + 1)) 0 (n - 1)) :
    StrictMono (fun i : Fin n => key i.val) := by
  cases n with
  | zero =>
    intro i j hij
    exact i.elim0
  | succ n =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    change key i.val < key (i.val + 1)
    simpa only [Nat.zero_add] using h i

end Consecutive

end ImbalancedChen.P2Winner9PullingOrderChecks
