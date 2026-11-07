import ImbalancedChen.P2OriginalStoredWQueryRounding
import ImbalancedChen.P2ActualLowerRhoEntryWallPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An exact finite signed query-compiler loss sums EVERY actual residual
modulus of each native lower row. The bound is errorEnvelope times the
explicit absolute reciprocal-totient norm of the same complete coefficient.
No normalized norm or asymptotic convergence is assumed. The ideal and
stored query values come from the independently defined original formulas.
-/

namespace ImbalancedChen.P2ActualLowerFullModuliQueryCompilerLoss

noncomputable section
open scoped Classical BigOperators
open Set
open P1ActualMovingAffineWallMass
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalStrictWLocalRationalCover
open P2OriginalLowerWThirdPhysicalRow
open P2OriginalStoredWQueryRounding
open P2ActualLowerRhoEntryWallPayment

def rowModuli (R : ActualLowerRow) (N : ℕ) : Finset ℕ :=
  actualLowerSmallRoughModuli R.retainEven N R.cap R.w R.z

def rowAbsoluteMean (R : ActualLowerRow) (N : ℕ) : ℝ :=
  ∑ q ∈ rowModuli R N, |R.rho N q| / (Nat.totient q : ℝ)

def retainedSource (N : ℕ) (a b : Fin 3 → ℝ) (K : Set Point) : Finset PrimeTuple :=
  (actualPrimeBoxTuples N a b).filter (fun p => actualPrimeTupleLog N p ∈ K)

def fullAbsoluteMeanNorm (N : ℕ) (a b : Fin 3 → ℝ) (K : Set Point)
    (rows : PrimeTuple → ActualLowerRow) : ℝ :=
  ∑ p ∈ retainedSource N a b K, tupleWeight p * rowAbsoluteMean (rows p) N

def fullSignedQueryLoss (S : CompactStart) (mesh N : ℕ) (r : ℚ)
    (a b : Fin 3 → ℝ) (K : Set Point) (rows : PrimeTuple → ActualLowerRow) : ℝ :=
  ∑ p ∈ retainedSource N a b K, tupleWeight p *
    (∑ q ∈ rowModuli (rows p) N,
      (rows p).rho N q / (Nat.totient q : ℝ) *
        (idealWQuery (actualPrimeTupleLog N p) -
          storedWQuery S mesh (actualPrimeTupleLog N p) r))

theorem rowAbsoluteMean_nonneg (R : ActualLowerRow) (N : ℕ) :
    0 ≤ rowAbsoluteMean R N := by
  exact Finset.sum_nonneg (fun q _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

-- This identity uses the very production physicalDensitySum on its entire
-- native carrier; no single arbitrary modulus replaces the inner sum.
theorem fullSignedQueryLoss_eq_same_rho_means
    (S : CompactStart) (mesh N : ℕ) (r : ℚ) (a b : Fin 3 → ℝ)
    (K : Set Point) (rows : PrimeTuple → ActualLowerRow) :
    fullSignedQueryLoss S mesh N r a b K rows =
      ∑ p ∈ retainedSource N a b K, tupleWeight p *
        (physicalDensitySum (rowModuli (rows p) N) ((rows p).rho N) *
          (idealWQuery (actualPrimeTupleLog N p) -
            storedWQuery S mesh (actualPrimeTupleLog N p) r)) := by
  unfold fullSignedQueryLoss physicalDensitySum
  simp only [Finset.sum_mul]

private theorem row_signed_loss_le (R : ActualLowerRow) (N : ℕ)
    (d E : ℝ) (hd : |d| ≤ E) :
    |∑ q ∈ rowModuli R N, R.rho N q / (Nat.totient q : ℝ) * d| ≤
      E * rowAbsoluteMean R N := by
  calc
    _ ≤ ∑ q ∈ rowModuli R N, |R.rho N q / (Nat.totient q : ℝ) * d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ rowModuli R N, (|R.rho N q| / (Nat.totient q : ℝ)) * |d| := by
      apply Finset.sum_congr rfl
      intro q _
      rw [abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ q ∈ rowModuli R N, (|R.rho N q| / (Nat.totient q : ℝ)) * E := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left hd
        (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = E * rowAbsoluteMean R N := by
      rw [← Finset.sum_mul]
      unfold rowAbsoluteMean
      ring

-- All actual prime rows and all their residual moduli remain in the
-- finite total norm. The theorem gives a quantitative loss, not a claim
-- that this N-dependent norm is uniformly bounded on the final scale.
theorem full_signed_query_compiler_loss_le
    (S : CompactStart) (rho : ℝ) (mesh N : ℕ) (r delta : ℚ)
    (a b : Fin 3 → ℝ) (K : Set Point) (rows : PrimeTuple → ActualLowerRow)
    (hstrict : ∀ x ∈ K, StrictWPoint S rho x)
    (hW : ∀ p ∈ retainedSource N a b K,
      WBoxCheck S (P2OriginalCommonActualWMesh.canonicalThirdCode S mesh
        (actualPrimeTupleLog N p)) rho r delta) :
    |fullSignedQueryLoss S mesh N r a b K rows| ≤
      storedErrorEnvelope S mesh r * fullAbsoluteMeanNorm N a b K rows := by
  have hrow (p : PrimeTuple) (hp : p ∈ retainedSource N a b K) :
      |∑ q ∈ rowModuli (rows p) N,
        (rows p).rho N q / (Nat.totient q : ℝ) *
          (idealWQuery (actualPrimeTupleLog N p) -
            storedWQuery S mesh (actualPrimeTupleLog N p) r)| ≤
      storedErrorEnvelope S mesh r * rowAbsoluteMean (rows p) N := by
    have hK := (Finset.mem_filter.mp hp).2
    have hx := P2OriginalCommonActualWMesh.strict_point_in_compact_coordinates
      S rho (actualPrimeTupleLog N p) (hstrict _ hK)
    have hquery := actual_stored_W_query_loss S rho mesh _ hx r delta (hW p hp)
    exact row_signed_loss_le (rows p) N _ _
      (by simpa only [abs_of_nonneg hquery.1] using hquery.2)
  unfold fullSignedQueryLoss fullAbsoluteMeanNorm
  calc
    _ ≤ ∑ p ∈ retainedSource N a b K,
        |tupleWeight p * (∑ q ∈ rowModuli (rows p) N,
          (rows p).rho N q / (Nat.totient q : ℝ) *
            (idealWQuery (actualPrimeTupleLog N p) -
              storedWQuery S mesh (actualPrimeTupleLog N p) r))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ retainedSource N a b K,
        tupleWeight p * (storedErrorEnvelope S mesh r * rowAbsoluteMean (rows p) N) := by
      apply Finset.sum_le_sum
      intro p hp
      have hw := actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hrow p hp) hw
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

end
end ImbalancedChen.P2ActualLowerFullModuliQueryCompilerLoss
