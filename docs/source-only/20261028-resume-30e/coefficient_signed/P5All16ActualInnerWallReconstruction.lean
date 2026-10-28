import ImbalancedChen.P5All16FineMeshGateScalar
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual physical all16 coefficient is pulled back to its true marked
prefix/small-beta/rough pair carrier, then partitioned into original fine
inner cells and the actual complementary arithmetic wall remainder.
The wall coefficient is defined INDEPENDENTLY as the full-q fibre sum of
those genuine pairs.  Full-q injectivity is derived from the installed
physical compiler and unique small/rough factorization; therefore the wall
coefficient is one-bounded, with its original signed row/beta weight.
Every wall pair has an actual proper affine-row reserve witness.  No
continuous-nullity argument removes an arithmetic prime.

The inner-cell sum below is an exact finite restriction of the same row
weights; replacing it by separated normalized whole-box gamma tensors is
a subsequent obligation.  This file does not assert a small wall mass,
complete marked scalar budget, or the prime-product estimate.
-/

namespace ImbalancedChen.P5Z.All16ActualInnerWallReconstruction
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalJointPresievedCompiler OriginalPresievedRoughPrimeSlots
open JointPresievedSlotAffineRealization All16PhysicalOwnerDiscrepancy
open PresievedRoughGateMeshReserve All16FineMeshGateScalar
open All16CanonicalFineWordNoZGuard

abbrev PairMark := Σ _ : Four, ℕ × ℕ

def pairMarks (n N : ℕ) (eta : ℚ) (w : ℝ) (E : ℕ × ℕ → Prop) : Finset PairMark :=
  (U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E).sigma
    (fun t => (rowSmall n N eta w t).product (rowRough n N eta w t))

def pairModulus (a : PairMark) : ℕ := fullPrefix a.1 * (a.2.1 * a.2.2)

def pairWeight (n N : ℕ) (eta : ℚ) (w B : ℝ) (a : PairMark) : ℝ :=
  rowCoefficient n N eta w B a.1 (a.2.1 * a.2.2)

def pairToJoint (a : PairMark) : Mark := ⟨a.1, a.2.1 * a.2.2⟩

def pairSlots (n N : ℕ) (eta : ℚ) (w : ℝ) (a : PairMark) : List ℕ :=
  rowSlots n N eta w a.1 a.2.2

def pairLevel (n N : ℕ) (eta : ℚ) (a : PairMark) : ℝ :=
  (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual
    (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N a.1)
    (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N a.1) eta : ℝ)

def pairLog (n N : ℕ) (eta : ℚ) (w : ℝ) (a : PairMark) :
    Fin (pairSlots n N eta w a).length → ℝ :=
  actualPrimeTupleLog N (slotVector (pairSlots n N eta w a))

/-- Literal original fine-cell ownership of the canonical residual word. -/
def pairInner (n N : ℕ) (eta : ℚ) (w : ℝ) (m : ℕ) (a : PairMark) : Prop :=
  ∃ j ∈ innerCells (pairSlots n N eta w a).length 0 1 (pairLevel n N eta a) m,
    pairLog n N eta w a ∈ cell 0 1 m j

def innerPairs (n N : ℕ) (eta : ℚ) (w : ℝ) (m : ℕ)
    (E : ℕ × ℕ → Prop) : Finset PairMark :=
  (pairMarks n N eta w E).filter (pairInner n N eta w m)

def wallPairs (n N : ℕ) (eta : ℚ) (w : ℝ) (m : ℕ)
    (E : ℕ × ℕ → Prop) : Finset PairMark :=
  (pairMarks n N eta w E).filter (fun a => ¬ pairInner n N eta w m a)

def wallSupport (n N : ℕ) (eta : ℚ) (w : ℝ) (m : ℕ)
    (E : ℕ × ℕ → Prop) : Finset ℕ :=
  (wallPairs n N eta w m E).image pairModulus

/-- Independently defined arithmetic wall coefficient, with full q and
actual original signed row/beta weights. -/
def wallRho (n N : ℕ) (eta : ℚ) (w B : ℝ) (m : ℕ)
    (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ a ∈ (wallPairs n N eta w m E).filter (fun a => pairModulus a = q),
    pairWeight n N eta w B a

/-- Every displayed pair is a genuine original joint physical mark. -/
theorem pair_to_joint_mem {n N : ℕ} {eta : ℚ} {w : ℝ}
    {E : ℕ × ℕ → Prop} {a : PairMark} (ha : a ∈ pairMarks n N eta w E) :
    pairToJoint a ∈ jointMarks n N eta w E := by
  obtain ⟨ht, hed⟩ := Finset.mem_sigma.mp ha
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  apply Finset.mem_sigma.mpr
  refine ⟨ht, ?_⟩
  change a.2.1 * a.2.2 ∈ actualSmallRoughModuli
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta a.1)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta a.1)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta a.1)
  exact Finset.mem_image.mpr ⟨a.2, Finset.mem_product.mpr ⟨he, hd⟩, rfl⟩

/-- Full-q uniqueness includes the real four-prime marked prefix and
both small/rough factors; it is not just per-prefix injectivity. -/
theorem pair_modulus_injective {n N : ℕ} {eta : ℚ} {w : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    Set.InjOn pairModulus (pairMarks n N eta w E : Set PairMark) := by
  rintro ⟨t, e, d⟩ ha ⟨s, f, c⟩ hb hq
  have hj : (⟨t, e * d⟩ : Mark) = (⟨s, f * c⟩ : Mark) :=
    joint_modulus_injective hN heta E hw (pair_to_joint_mem ha) (pair_to_joint_mem hb) hq
  have hts : t = s := congrArg Sigma.fst hj
  subst s
  have hprod : e * d = f * c := congrArg (fun a : Mark => a.2) hj
  obtain ⟨ht, hed⟩ := Finset.mem_sigma.mp ha
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  obtain ⟨ht', hfc⟩ := Finset.mem_sigma.mp hb
  obtain ⟨hf, hc⟩ := Finset.mem_product.mp hfc
  have hpair : (e, d) = (f, c) := smallRough_factorization_unique
    (actualSmallRosserSupport_smallPrimeSupportedAt N _ w he)
    (fixedRoughSupport_roughPrimeSupportedAt
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N _ w _ hd)
    (actualSmallRosserSupport_smallPrimeSupportedAt N _ w hf)
    (fixedRoughSupport_roughPrimeSupportedAt
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N _ w _ hc) hprod
  cases hpair
  rfl

/-- Actual wall pairs have an explicit proper affine-row reserve witness.
Their original marked prefix, small beta factor and strict cutoffs remain. -/
theorem wall_pair_has_actual_affine_wall {n N m : ℕ} {eta : ℚ} {w : ℝ}
    {E : ℕ × ℕ → Prop} (hN : 1 < N) (heta : 0 < eta)
    {a : PairMark} (ha : a ∈ wallPairs n N eta w m E) :
    wallReserve (pairSlots n N eta w a).length 0 1 (pairLevel n N eta a) m
      (pairLog n N eta w a) := by
  obtain ⟨ha, hnot⟩ := Finset.mem_filter.mp ha
  obtain ⟨ht, hed⟩ := Finset.mem_sigma.mp ha
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  have hL := (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  obtain ⟨j, hj, hbox, hv, hcert | hwall⟩ := retained_actual_mesh_cell_or_wall hN
    (all16_physical_Z_le_N (by omega) heta ht) hL hd m
  · exact (hnot ⟨j, hcert, hv⟩).elim
  · exact hwall

/-- The wall support lies on the unchanged actual physical joint carrier. -/
theorem wall_support_subset_joint (n N m : ℕ) (eta : ℚ) (w : ℝ)
    (E : ℕ × ℕ → Prop) : wallSupport n N eta w m E ⊆ jointSupport n N eta w E := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨pairToJoint a,
    pair_to_joint_mem (Finset.mem_filter.mp ha).1, rfl⟩

/-- At each occupied full-q fibre the independently defined wall rho
is exactly its genuine signed physical row, without extra multiplicity. -/
theorem wall_rho_eq_pair {n N m : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    {a : PairMark} (ha : a ∈ wallPairs n N eta w m E) :
    wallRho n N eta w B m E (pairModulus a) = pairWeight n N eta w B a := by
  have hf : (wallPairs n N eta w m E).filter (fun b => pairModulus b = pairModulus a) = {a} := by
    ext b
    constructor
    · intro hb
      obtain ⟨hb, hq⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_singleton.mpr
        (pair_modulus_injective hN heta E hw (Finset.mem_filter.mp hb).1
          (Finset.mem_filter.mp ha).1 hq)
    · intro hb
      have heq := Finset.mem_singleton.mp hb
      subst b
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  simp only [wallRho, hf, Finset.sum_singleton]

theorem wall_rho_zero_off_support (n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) {q : ℕ} (hq : q ∉ wallSupport n N eta w m E) :
    wallRho n N eta w B m E q = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha, hq'⟩ := Finset.mem_filter.mp ha
  exact (hq (Finset.mem_image.mpr ⟨a, ha, hq'⟩)).elim

/-- A full-q absolute envelope for the actual arithmetic wall coefficient.
No wall smallness or signed distribution estimate is a premise. -/
theorem wall_rho_abs_le_one {n N m : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) (q : ℕ) :
    |wallRho n N eta w B m E q| ≤ 1 := by
  by_cases hq : q ∈ wallSupport n N eta w m E
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    rw [wall_rho_eq_pair hN heta E hw ha]
    exact rowCoefficient_abs_le_one n N eta w B a.1 (a.2.1 * a.2.2)
  · rw [wall_rho_zero_off_support n N m eta w B E hq]
    norm_num

/-- Exact wall pushforward, independent of the later signed test F. -/
theorem wall_exact_pushforward (n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ a ∈ wallPairs n N eta w m E, pairWeight n N eta w B a * F (pairModulus a)) =
      ∑ q ∈ wallSupport n N eta w m E, wallRho n N eta w B m E q * F q := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := wallPairs n N eta w m E) (t := wallSupport n N eta w m E) (g := pairModulus)
    (fun a ha => Finset.mem_image_of_mem _ ha)
    (fun a => pairWeight n N eta w B a * F (pairModulus a))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q hq
  unfold wallRho
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

def innerAtomLinear (n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) : ℝ :=
  ∑ a ∈ pairMarks n N eta w E,
    ∑ j ∈ innerCells (pairSlots n N eta w a).length 0 1 (pairLevel n N eta a) m,
      if pairLog n N eta w a ∈ cell 0 1 m j then
        pairWeight n N eta w B a * F (pairModulus a) else 0

/-- A canonical point belongs to at most one half-open inner cell. -/
theorem inner_cell_sum_eq_indicator {r m : ℕ} (ell C : ℝ) (v : Fin r → ℝ) :
    (∑ j ∈ innerCells r 0 1 ell m, if v ∈ cell 0 1 m j then C else 0) =
      if ∃ j ∈ innerCells r 0 1 ell m, v ∈ cell 0 1 m j then C else 0 := by
  by_cases hv : ∃ j ∈ innerCells r 0 1 ell m, v ∈ cell 0 1 m j
  · rw [if_pos hv]
    obtain ⟨j, hj, hvj⟩ := hv
    rw [Finset.sum_eq_single j]
    · rw [if_pos hvj]
    · intro k hk hne
      apply if_neg
      intro hvk
      exact hne (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 1) hvk hvj)
    · intro hn
      exact (hn hj).elim
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro j hj
    exact if_neg (fun hvj => hv ⟨j, hj, hvj⟩)

/-- Full physical all16 signed reconstruction.  The arithmetic wall
remainder is explicit and retains both original beta and marked-prefix
sums.  The identity holds simultaneously for count and exact coprime mean. -/
theorem actual_all16_inner_plus_wall (n N m : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta w E, jointPresievedSigma n N eta w B E q * F q) =
      innerAtomLinear n N m eta w B E F +
        ∑ q ∈ wallSupport n N eta w m E, wallRho n N eta w B m E q * F q := by
  have hfull : (∑ q ∈ jointSupport n N eta w E,
      jointPresievedSigma n N eta w B E q * F q) =
      ∑ a ∈ pairMarks n N eta w E, pairWeight n N eta w B a * F (pairModulus a) := by
    rw [← joint_exact_pushforward n N eta w B E F]
    unfold pairMarks
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    rw [physical_row_pullback, Finset.sum_product]
    rfl
  rw [hfull, ← wall_exact_pushforward]
  unfold innerAtomLinear wallPairs
  simp_rw [inner_cell_sum_eq_indicator]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change pairWeight n N eta w B a * F (pairModulus a) =
    (if pairInner n N eta w m a then pairWeight n N eta w B a * F (pairModulus a) else 0) +
    (if ¬ pairInner n N eta w m a then pairWeight n N eta w B a * F (pairModulus a) else 0)
  by_cases hi : pairInner n N eta w m a <;> simp [hi]

/-- Only an OUTER full-q absolute value is taken.  The right side is the
actual arithmetic wall kernel to be paid by a separate prime/divisor bound;
there is no assumption that it is small. -/
theorem actual_wall_test_abs_le {n N m : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) (F : ℕ → ℝ) :
    |∑ q ∈ wallSupport n N eta w m E, wallRho n N eta w B m E q * F q| ≤
      ∑ q ∈ wallSupport n N eta w m E, |F q| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (wall_rho_abs_le_one hN heta E hw q) (abs_nonneg _)).trans_eq
    (one_mul _)

end
end ImbalancedChen.P5Z.All16ActualInnerWallReconstruction
