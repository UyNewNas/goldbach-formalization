import ImbalancedChen.P3PhysicalOriginalW

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Exact insertion of an arbitrary original labelled-prime geometric W_T
into the actual previously constructed U5 / HB chart.

The source algebra preserves the physical original group products, the
COMPLETE product, each existing multiplier, and the identical integer rho.
No new arithmetic filter or shifted mean is introduced. The old logarithm
core hypotheses are derived elsewhere; this file only consumes them.
-/
namespace ImbalancedChen.P3PhysicalOriginalWInsertion
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets P3U5RootAtlas
open P3U5PhysicalProductChart P3HBLogSourceDictionary
open P3PhysicalOriginalW P3U5OriginalWComposition

/-- At a source point, the previous extended chart with the ACTUAL original
W_T pullback equals the unmodified physical original-prime weight times
the original full-product/U5/HB factor. -/
theorem exact_originalW_chart {d g : ℕ} {a ell : ℝ}
    (ha : 0 < a) (hell : 0 < ell)
    (W : (Fin g → ℝ) → ℝ) (U : Fin d → ℝ)
    (hU : ∀ i, 0 < U i) (R : Fin g → ℝ)
    (hR : ∀ j, 0 < R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g)
    (hne : pair 0 ≠ pair 1) (pick : Fin g → Fin d)
    {T : ℝ} (hT : 0 < T) (m : ℕ) (l : Lane)
    (z : Point d)
    (hslot : ∀ i, 0 ≤ Real.log (U i * Real.exp (z i)) / ell ∧
      Real.log (U i * Real.exp (z i)) / ell ≤ 2)
    (hgroup : ∀ j, a ≤ Real.log
      (groupProduct group (fun i => U i * Real.exp (z i)) j) / ell ∧
      Real.log (groupProduct group (fun i => U i * Real.exp (z i)) j) / ell ≤ 2) :
    withOriginalW (pulledOriginalW W U group) a ell
      (fun j => groupBase U group (pair j)) (pairSlots group pair) group
      (fun j => Real.log (groupBase U group j / R j))
      (Real.log ((∏ j, groupBase U group j) / T))
      (fun i => Real.log (U i)) (fun j => Real.log (groupBase U group j))
      pick m l z =
    originalPrimeWeight W group (slotValue U z) *
      physicalProfile ell (groupBase U group) R group pair T m l z *
      originalLogFactor group pick (slotValue U z) := by
  rw [withOriginalW_eq_physical ha hell (pulledOriginalW W U group)
    U hU R hR group pair hne pick hT m l z hslot hgroup,
    pulledOriginalW_eq_original]
  ring

/-- The same equality stated directly on the original physical HB slot
values n_i; all logarithmic coordinates are reconstructed, not postulated. -/
theorem exact_originalW_on_slots {d g : ℕ} {a ell : ℝ}
    (ha : 0 < a) (hell : 0 < ell)
    (W : (Fin g → ℝ) → ℝ) (U n : Fin d → ℝ)
    (hU : ∀ i, 0 < U i) (hn : ∀ i, 0 < n i)
    (R : Fin g → ℝ) (hR : ∀ j, 0 < R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g)
    (hne : pair 0 ≠ pair 1) (pick : Fin g → Fin d)
    {T : ℝ} (hT : 0 < T) (m : ℕ) (l : Lane)
    (hslot : ∀ i, 0 ≤ Real.log (n i) / ell ∧ Real.log (n i) / ell ≤ 2)
    (hgroup : ∀ j, a ≤ Real.log (groupProduct group n j) / ell ∧
      Real.log (groupProduct group n j) / ell ≤ 2) :
    withOriginalW (pulledOriginalW W U group) a ell
      (fun j => groupBase U group (pair j)) (pairSlots group pair) group
      (fun j => Real.log (groupBase U group j / R j))
      (Real.log ((∏ j, groupBase U group j) / T))
      (fun i => Real.log (U i)) (fun j => Real.log (groupBase U group j))
      pick m l (slotLog U n) =
    originalPrimeWeight W group n *
      physicalProfile ell (groupBase U group) R group pair T m l (slotLog U n) *
      originalLogFactor group pick n := by
  have hz : (fun i => U i * Real.exp (slotLog U n i)) = n := by
    exact slotValue_slotLog U n hU hn
  have hs : ∀ i, 0 ≤ Real.log (U i * Real.exp (slotLog U n i)) / ell ∧
      Real.log (U i * Real.exp (slotLog U n i)) / ell ≤ 2 := by
    simpa only [hz] using hslot
  have hg : ∀ j, a ≤ Real.log
      (groupProduct group (fun i => U i * Real.exp (slotLog U n i)) j) / ell ∧
      Real.log (groupProduct group (fun i => U i * Real.exp (slotLog U n i)) j) / ell ≤ 2 := by
    simpa only [hz] using hgroup
  have h := exact_originalW_chart ha hell W U hU R hR group pair hne
    pick hT m l (slotLog U n) hs hg
  simpa only [slotValue, hz] using h

/-- EXACT finite signed-source identity, including the same rho in the
count and the coprime mean. F may be the original signed count-minus-mean
kernel. This proves no distribution bound or HB source coverage. -/
theorem same_rho_originalW_slots {ι : Type*} {d g : ℕ}
    {a ell : ℝ} (ha : 0 < a) (hell : 0 < ell)
    (Q : Finset ℕ) (S : Finset ι) (rho : ℕ → ℝ)
    (F : ℕ → ι → ℝ) (W : (Fin g → ℝ) → ℝ)
    (U : Fin d → ℝ) (hU : ∀ i, 0 < U i)
    (n : ι → Fin d → ℝ)
    (hn : ∀ t ∈ S, ∀ i, 0 < n t i)
    (R : Fin g → ℝ) (hR : ∀ j, 0 < R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g)
    (hne : pair 0 ≠ pair 1) (pick : Fin g → Fin d)
    {T : ℝ} (hT : 0 < T) (m : ℕ) (l : Lane)
    (hslot : ∀ t ∈ S, ∀ i, 0 ≤ Real.log (n t i) / ell ∧
      Real.log (n t i) / ell ≤ 2)
    (hgroup : ∀ t ∈ S, ∀ j,
      a ≤ Real.log (groupProduct group (n t) j) / ell ∧
      Real.log (groupProduct group (n t) j) / ell ≤ 2) :
    (∑ q ∈ Q, rho q * ∑ t ∈ S, F q t *
      withOriginalW (pulledOriginalW W U group) a ell
        (fun j => groupBase U group (pair j)) (pairSlots group pair) group
        (fun j => Real.log (groupBase U group j / R j))
        (Real.log ((∏ j, groupBase U group j) / T))
        (fun i => Real.log (U i)) (fun j => Real.log (groupBase U group j))
        pick m l (slotLog U (n t))) =
    (∑ q ∈ Q, rho q * ∑ t ∈ S, F q t *
      (originalPrimeWeight W group (n t) *
        physicalProfile ell (groupBase U group) R group pair T m l
          (slotLog U (n t)) *
        originalLogFactor group pick (n t))) := by
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [exact_originalW_on_slots ha hell W U (n t) hU (hn t ht)
    R hR group pair hne pick hT m l (hslot t ht) (hgroup t ht)]

/-- A completely explicit exact count-minus-coprime-mean test. Here P_j
stands for an ORIGINAL labelled product; this is an algebraic kernel, not a
claim that expanded HB slots are individually prime. The actual PP
application restricts to positive q with (q,T)=1. -/
def exactCoprimeTest {g : ℕ} (T q : ℕ) (p : Fin g → ℕ) : ℝ :=
  (if (∏ j, p j) % q = T % q then 1 else 0) -
    (if Nat.Coprime (∏ j, p j) q then (Nat.totient q : ℝ)⁻¹ else 0)

/-- Multiplying the original labels recovers every HB integer slot ONCE. -/
theorem natural_group_total {d g : ℕ}
    (group : Fin d → Fin g) (n : Fin d → ℕ) :
    (∏ j : Fin g, ∏ i : Fin d, if group i = j then n i else 1) =
      ∏ i, n i := by
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- Both the residue test and the exact coprime mean refer to the same
complete physical modulus after HB expansion, including exact equality
to T. The prime-property/coefficients are still separate obligations. -/
theorem exactCoprimeTest_after_HB {d g : ℕ}
    (T q : ℕ) (group : Fin d → Fin g) (n : Fin d → ℕ) :
    exactCoprimeTest T q
        (fun j => ∏ i : Fin d, if group i = j then n i else 1) =
      ((if (∏ i, n i) % q = T % q then 1 else 0) -
        (if Nat.Coprime (∏ i, n i) q
          then (Nat.totient q : ℝ)⁻¹ else 0)) := by
  simp only [exactCoprimeTest, natural_group_total]

end
end ImbalancedChen.P3PhysicalOriginalWInsertion
