import Mathlib.Tactic

/-! Generic signed physical pushforward, extracted verbatim from the existing
P3ActualU6PhysicalRhoPushforward source. Same namespace and statements.
Source only; no new proof or kernel acceptance is claimed by extraction. -/

namespace ImbalancedChen.P3ActualU6PhysicalRhoPushforward

noncomputable section
open scoped Classical BigOperators

/-- Physical union, used only as the indexing carrier. Union is safe here
because actual integer coefficients below ADD over all labelled fibres. -/
def taggedPhysicalModuli
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ) : Finset ℕ :=
  T.biUnion (fun t => (Q t).image (modulus t))

/-- Signed integer pushforward, retaining all occurrences when distinct
original labels/quotients produce the same physical modulus. -/
def taggedPhysicalIntegerRho
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    (coeff : (ℕ × ℕ) → ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ t ∈ T, ∑ q ∈ Q t,
    if modulus t q = d then coeff t q else 0

theorem tagged_physical_mem
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    {t : ℕ × ℕ} (ht : t ∈ T) {q : ℕ} (hq : q ∈ Q t) :
    modulus t q ∈ taggedPhysicalModuli T Q modulus := by
  classical
  exact Finset.mem_biUnion.mpr
    ⟨t, ht, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

/-- There are no coefficient atoms outside the genuinely generated
physical moduli. This does not assert that all supported atoms are nonzero:
different original labelled occurrences may cancel. -/
theorem tagged_physical_integer_rho_zero_off_support
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    (coeff : (ℕ × ℕ) → ℕ → ℤ) (d : ℕ)
    (hd : d ∉ taggedPhysicalModuli T Q modulus) :
    taggedPhysicalIntegerRho T Q modulus coeff d = 0 := by
  classical
  unfold taggedPhysicalIntegerRho
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro q hq
  have hm : modulus t q ∈ taggedPhysicalModuli T Q modulus :=
    tagged_physical_mem T Q modulus ht hq
  have hne : modulus t q ≠ d := by
    intro h
    exact hd (h ▸ hm)
  simp [hne]

/-- Pure finite reindexing: the SINGLE integer coefficient of each
physical d gives exactly the original signed labelled sum, even with
noninjective t,q -> d. No sign or positivity hypothesis on coeff or F. -/
theorem tagged_physical_pushforward_identity
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    (coeff : (ℕ × ℕ) → ℕ → ℤ) (F : ℕ → ℝ) :
    (∑ d ∈ taggedPhysicalModuli T Q modulus,
       (taggedPhysicalIntegerRho T Q modulus coeff d : ℝ) * F d) =
      ∑ t ∈ T, ∑ q ∈ Q t, (coeff t q : ℝ) * F (modulus t q) := by
  classical
  let D := taggedPhysicalModuli T Q modulus
  have hcast (d : ℕ) :
      (taggedPhysicalIntegerRho T Q modulus coeff d : ℝ) =
        ∑ t ∈ T, ∑ q ∈ Q t,
          if modulus t q = d then (coeff t q : ℝ) else 0 := by
    simp [taggedPhysicalIntegerRho]
  have hsingle (t : ℕ × ℕ) (ht : t ∈ T)
      (q : ℕ) (hq : q ∈ Q t) :
      (∑ d ∈ D,
        (if modulus t q = d then (coeff t q : ℝ) else 0) * F d) =
        (coeff t q : ℝ) * F (modulus t q) := by
    have hm : modulus t q ∈ D :=
      tagged_physical_mem T Q modulus ht hq
    have hsum :
        (∑ d ∈ D,
          (if modulus t q = d then (coeff t q : ℝ) else 0) * F d) =
          (if modulus t q = modulus t q then
            (coeff t q : ℝ) else 0) * F (modulus t q) := by
      apply Finset.sum_eq_single (modulus t q)
      · intro d hd hne
        have hneq : modulus t q ≠ d := Ne.symm hne
        simp [hneq]
      · intro hnot
        exact False.elim (hnot hm)
    simpa using hsum
  change (∑ d ∈ D,
    (taggedPhysicalIntegerRho T Q modulus coeff d : ℝ) * F d) = _
  calc
    _ = ∑ d ∈ D, ∑ t ∈ T, ∑ q ∈ Q t,
          (if modulus t q = d then (coeff t q : ℝ) else 0) * F d := by
          simp only [hcast, Finset.sum_mul]
    _ = ∑ t ∈ T, ∑ q ∈ Q t, ∑ d ∈ D,
          (if modulus t q = d then (coeff t q : ℝ) else 0) * F d := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_comm]
    _ = ∑ t ∈ T, ∑ q ∈ Q t, (coeff t q : ℝ) * F (modulus t q) := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro q hq
          exact hsingle t ht q hq

end
end ImbalancedChen.P3ActualU6PhysicalRhoPushforward
