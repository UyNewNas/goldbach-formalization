import ImbalancedChen.P5All16MarkedCommonFineSource
import ImbalancedChen.P5ActualInnerPerLabelGamma

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

FULL marked+residual common-fine words, with the original residual-only
denominator, have a fixed restoring scalar budget.  The bound sums EVERY
coarse owner, EVERY marked fine label, EVERY residual fine label and ALL
fixed physical rough ranks.  There is no sum over arithmetic marked
primes or over beta e in the scalar: these are convolution coordinates.
The same finite bound is uniform in N, beta, test, and in every fixed
whole-occurrence partition.  It is not a full-modulus mass bound.

This proves the budget for the actual independently certified Cartesian
subsource of MarkedCommonFineSource.  Matching its whole union to the
actual coefficient with an independent remainder is a separate finite
source assembly; no cover, small wall estimate or PP conclusion is assumed.
-/

namespace ImbalancedChen.P5Z.All16MarkedFineScalarBudget
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen
open PresievedRoughGateMeshReserve All16FineMeshGateScalar
open All16InnerCartesianDictionary All16MarkedCommonFineSource

theorem marked_labels_injective {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) : Function.Injective a := by
  have hlo : logPrimeMeshLo 0 1 m a ∈ cell 0 1 m a := by
    apply mem_logPrimeMeshCell.mpr
    intro i
    exact ⟨le_rfl, (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m a i).2.1⟩
  have hanti := (h.prefix _ hlo).2.2.2.1
  intro i k hik
  apply hanti.injective
  simp only [logPrimeMeshLo, hik]

/-- The same alphabet has disjoint marked/residual occurrence labels.
The separation is proved from their literal shared endpoints at Z. -/
theorem marked_residual_labels_disjoint {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) : List.Disjoint (List.ofFn a) (List.ofFn j) := by
  apply List.disjoint_left.mpr
  intro x hx hres
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hres
  have hstep := (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m j k).2.1
  have heq : logPrimeMeshLo 0 1 m j k = logPrimeMeshLo 0 1 m a i := by
    simp only [logPrimeMeshLo, hk]
  have hu := h.residualUpper k
  have hl := h.markedLower i
  linarith

theorem full_word_nodup {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) : (fullWord a j).Nodup := by
  apply List.nodup_append.mpr
  exact ⟨List.nodup_ofFn.mpr (marked_labels_injective h),
    List.nodup_ofFn.mpr (inner_mesh_labels_injective (cellEll n eta c) h.inner),
    marked_residual_labels_disjoint h⟩

/-- The actual common w<=Z licence is sufficient even at residual rank
zero.  Every prime in EVERY occurring common label is rough above w;
this pays beta attachment without treating its result as rough. -/
theorem whole_label_rough_lower {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) (hcut : rho ≤ cellZeta n eta c)
    {i : Fin (m + 1)} (hi : i ∈ fullWord a j) {p : ℕ}
    (hp : p ∈ commonAlphabet N m i) : (N : ℝ) ^ rho ≤ (p : ℝ) := by
  have hlo : rho ≤ logPrimeMeshPoint 0 1 m i.val := by
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
      exact hcut.trans (h.markedLower k)
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
      exact h.residualLower k
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hN)
  exact (Real.rpow_le_rpow_of_exponent_le hn hlo).trans (Finset.mem_filter.mp hp).2.1

theorem whole_subword_product_rough {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) (hcut : rho ≤ cellZeta n eta c)
    (word : List (Fin (m + 1))) (hword : ∀ i ∈ word, i ∈ fullWord a j)
    {d : ℕ} (hd : d ∈ (actualPrimeSlotBox (commonAlphabet N m) word).image List.prod) :
    RoughPrimeSupportedAt ((N : ℝ) ^ rho) d := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  have hp : ∀ p ∈ ps, Nat.Prime p ∧ (N : ℝ) ^ rho ≤ (p : ℝ) :=
    actualPrimeSlotBox_forall _ word _ (by
      intro i hi p hp
      exact ⟨(mem_roughPrimeFinset.mp (ActualInnerMeshSeparatedGamma.mesh_prime_rough hp)).2.1,
        whole_label_rough_lower hN h hcut (hword i hi) hp⟩) ps hps
  have hpos : 0 < ps.prod := List.prod_pos (fun p hmem => (hp p hmem).1.pos)
  refine ⟨hpos.ne', ?_⟩
  intro p hfactor
  have hlist : p ∈ ps.prod.primeFactorsList := by
    apply List.mem_toFinset.mp
    simpa only [Nat.toFinset_factors] using hfactor
  have hperm := Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod)
    (fun p hmem => (hp p hmem).1)
  exact (hp p (hperm.mem_iff.mpr hlist)).2

/-- M_mark is retained, and here is DERIVED to be one because this
strict whole-box subdivision gives distinct labels. It is not divided
out of the original raw marked source. -/
theorem marked_multiplicity_one {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) :
    ActualInnerPerLabelGamma.multiplicity (List.ofFn a) = 1 :=
  ActualInnerPerLabelGamma.multiplicity_eq_one_of_nodup _
    (List.nodup_ofFn.mpr (marked_labels_injective h))

theorem partition_group_multiplicities_one {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j)
    (out : List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)))
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm (fullWord a j)) :
    ActualInnerPerLabelGamma.multiplicity out.1 = 1 ∧
      ActualInnerPerLabelGamma.multiplicity out.2.1 = 1 ∧
      ActualInnerPerLabelGamma.multiplicity out.2.2 = 1 := by
  have hnd := hpart.nodup_iff.mpr (full_word_nodup h)
  obtain ⟨h1, h23, _⟩ := List.nodup_append.mp hnd
  obtain ⟨h2, h3, _⟩ := List.nodup_append.mp h23
  exact ⟨ActualInnerPerLabelGamma.multiplicity_eq_one_of_nodup _ h1,
    ActualInnerPerLabelGamma.multiplicity_eq_one_of_nodup _ h2,
    ActualInnerPerLabelGamma.multiplicity_eq_one_of_nodup _ h3⟩

/-- The manuscript restoring scalar: original state sign, RESIDUAL
parity, three original per-label group factorials, and M_res only. -/
def restoringScalar {r m : ℕ} (epsilon : ℝ) (j : Grid r m)
    (out : List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1))) : ℝ :=
  epsilon * (-1 : ℝ) ^ r *
    (ActualInnerPerLabelGamma.multiplicity out.1 : ℝ) *
    (ActualInnerPerLabelGamma.multiplicity out.2.1 : ℝ) *
    (ActualInnerPerLabelGamma.multiplicity out.2.2 : ℝ) / (meshMultiplicity j : ℝ)

theorem restoring_scalar_abs {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j) (epsilon : ℝ)
    (out : List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)))
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm (fullWord a j)) :
    |restoringScalar epsilon j out| = |epsilon| := by
  obtain ⟨h1, h2, h3⟩ := partition_group_multiplicities_one h out hpart
  simp [restoringScalar, h1, h2, h3, inner_mesh_multiplicity_one (cellEll n eta c) h.inner,
    abs_mul, abs_pow]

abbrev Key (n m r : ℕ) := CoarseGrid n × Grid 4 m × Grid r m

def certifiedKeys (n m r : ℕ) (eta : ℚ) (rho : ℝ) (M : Set (ℝ × ℝ)) :
    Finset (Key n m r) :=
  Finset.univ.filter (fun k => WholeCell eta rho M k.1 k.2.1 k.2.2 ∧ rho ≤ cellZeta n eta k.1)

/-- This scalar budget contains NO N, arithmetic tuple, beta e or q. -/
def scalarBudget (R n m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    (((n + 1) ^ 4 * (m + 1) ^ 4 * (m + 1) ^ r : ℕ) : ℝ)

theorem whole_rank_scalar_mass (n m r : ℕ) (eta : ℚ) (rho epsilon : ℝ)
    (M : Set (ℝ × ℝ))
    (out : Key n m r → List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)))
    (hpart : ∀ k ∈ certifiedKeys n m r eta rho M,
      ((out k).1 ++ (out k).2.1 ++ (out k).2.2).Perm (fullWord k.2.1 k.2.2)) :
    (∑ k ∈ certifiedKeys n m r eta rho M, |restoringScalar epsilon k.2.2 (out k)|) ≤
      |epsilon| * (((n + 1) ^ 4 * (m + 1) ^ 4 * (m + 1) ^ r : ℕ) : ℝ) := by
  calc
    _ = ∑ _k ∈ certifiedKeys n m r eta rho M, |epsilon| := by
      apply Finset.sum_congr rfl
      intro k hk
      exact restoring_scalar_abs (Finset.mem_filter.mp hk).2.1 epsilon (out k) (hpart k hk)
    _ = |epsilon| * ((certifiedKeys n m r eta rho M).card : ℝ) := by simp [mul_comm]
    _ ≤ |epsilon| * (Fintype.card (Key n m r) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg epsilon)
      exact_mod_cast Finset.card_le_univ (certifiedKeys n m r eta rho M)
    _ = _ := by
      simp [Key, CoarseGrid, U1011OriginalFifteenNativeGridCells.Grid, Grid,
        Fintype.card_fun, mul_assoc]

/-- ALL physical ranks, coarse owners and marked/residual colours are
paid AFTER beta and marked primes have become convolution coordinates.
The bound is uniform in any N-dependent, fixed whole-word partition. -/
theorem complete_cartesian_scalar_mass (R n m : ℕ) (eta : ℚ) (rho epsilon : ℝ)
    (M : Set (ℝ × ℝ))
    (out : ∀ r, Key n m r →
      List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)))
    (hpart : ∀ r ∈ Finset.range (R + 1), ∀ k ∈ certifiedKeys n m r eta rho M,
      ((out r k).1 ++ (out r k).2.1 ++ (out r k).2.2).Perm (fullWord k.2.1 k.2.2)) :
    (∑ r ∈ Finset.range (R + 1), ∑ k ∈ certifiedKeys n m r eta rho M,
      |restoringScalar epsilon k.2.2 (out r k)|) ≤ |epsilon| * scalarBudget R n m := by
  rw [scalarBudget, Finset.mul_sum]
  exact Finset.sum_le_sum (fun r hr => whole_rank_scalar_mass n m r eta rho epsilon M
    (out r) (hpart r hr))

end
end ImbalancedChen.P5Z.All16MarkedFineScalarBudget
