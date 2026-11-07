import ImbalancedChen.P2OriginalThirdLowerWallReserve
import ImbalancedChen.ActualLowerSmallRoughAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact actualLowerSmallRoughRho entry is used in both the signed wall sum
and its absolute majorant. Its unit bound is derived from the existing
coefficient constructor, not supplied as a new envelope premise. The
prime carrier/weights and the concrete third lower wall family are those
of the preceding batches. This pays one modulus pullback at a time; no
unproved sum over all residual moduli or normalized density is asserted.
-/

namespace ImbalancedChen.P2ActualLowerRhoEntryWallPayment

noncomputable section
open scoped Classical BigOperators
open P1ActualMovingAffineWallMass
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalThirdLowerWallReserve

abbrev PrimeTuple := Fin 3 → ℕ

-- These are literal arguments of the existing actual lower constructor.
-- They can read a fixed causal row; no coefficient value or bound is data.
structure ActualLowerRow where
  retainEven : List ℕ → Bool
  cap : ℕ
  w : ℝ
  z : ℝ
  L : ℝ

def ActualLowerRow.rho (R : ActualLowerRow) (N q : ℕ) : ℝ :=
  actualLowerSmallRoughRho R.retainEven N R.cap R.w R.z R.L q

theorem ActualLowerRow.rho_abs_le_one (R : ActualLowerRow) (N q : ℕ) :
    |R.rho N q| ≤ 1 :=
  actualLowerSmallRoughRho_abs_le_one R.retainEven N R.cap R.w R.z R.L q

def originalWallTuples (S : CompactStart) (rho delta : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) : Finset PrimeTuple :=
  (actualPrimeBoxTuples N a b).filter (fun p =>
    actualPrimeTupleLog N p ∈ primeAffineWallStrip finiteForms (finiteHeights S rho) delta)

def actualLowerEntrySignedWall (S : CompactStart) (rho delta : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) (rows : PrimeTuple → ActualLowerRow)
    (modulus : PrimeTuple → ℕ) : ℝ :=
  ∑ p ∈ originalWallTuples S rho delta N a b,
    tupleWeight p * (rows p).rho N (modulus p)

def actualLowerEntryAbsoluteWall (S : CompactStart) (rho delta : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) (rows : PrimeTuple → ActualLowerRow)
    (modulus : PrimeTuple → ℕ) : ℝ :=
  ∑ p ∈ originalWallTuples S rho delta N a b,
    tupleWeight p * |(rows p).rho N (modulus p)|

theorem signedWall_abs_le_actual_absolute (S : CompactStart) (rho delta : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) (rows : PrimeTuple → ActualLowerRow)
    (modulus : PrimeTuple → ℕ) :
    |actualLowerEntrySignedWall S rho delta N a b rows modulus| ≤
      actualLowerEntryAbsoluteWall S rho delta N a b rows modulus := by
  unfold actualLowerEntrySignedWall actualLowerEntryAbsoluteWall
  calc
    _ ≤ ∑ p ∈ originalWallTuples S rho delta N a b,
        |tupleWeight p * (rows p).rho N (modulus p)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hw := actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
      rw [abs_mul, abs_of_nonneg hw]

-- All signs and selected policies stay inside the same actual native rho.
-- No absolute-density theorem or sum over q is assumed or inferred here.
theorem actual_absoluteWall_le_prime_strip (S : CompactStart) (rho delta : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) (rows : PrimeTuple → ActualLowerRow)
    (modulus : PrimeTuple → ℕ) :
    actualLowerEntryAbsoluteWall S rho delta N a b rows modulus ≤
      actualPrimeAffineWallStripMass N a b finiteForms (finiteHeights S rho) delta := by
  unfold actualLowerEntryAbsoluteWall actualPrimeAffineWallStripMass
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
  have hentry := ActualLowerRow.rho_abs_le_one (rows p) N (modulus p)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hentry hw

-- A requested tolerance chooses one positive wall width before N, uniformly
-- every later row construction and modulus pullback. This uniformity is
-- proved from the actual native rho constructor's universal unit bound.
theorem exists_actual_lower_entry_wall_payment
    (S : CompactStart) (rho : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (reserve : ℝ) (hreserve : 0 < reserve) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∀ rows : PrimeTuple → ActualLowerRow, ∀ modulus : PrimeTuple → ℕ,
          |actualLowerEntrySignedWall S rho delta N (fun _ => a) (fun _ => b) rows modulus| < reserve ∧
          actualLowerEntryAbsoluteWall S rho delta N (fun _ => a) (fun _ => b) rows modulus < reserve := by
  obtain ⟨delta, hd, N₀, hN₀, hmass⟩ :=
    exists_actual_lower_wall_strip_reserve S rho ha hab reserve hreserve
  refine ⟨delta, hd, N₀, hN₀, ?_⟩
  intro N hN rows modulus
  have haBound := (actual_absoluteWall_le_prime_strip S rho delta N
    (fun _ => a) (fun _ => b) rows modulus).trans_lt (hmass N hN)
  exact ⟨(signedWall_abs_le_actual_absolute S rho delta N
    (fun _ => a) (fun _ => b) rows modulus).trans_lt haBound, haBound⟩

end
end ImbalancedChen.P2ActualLowerRhoEntryWallPayment
