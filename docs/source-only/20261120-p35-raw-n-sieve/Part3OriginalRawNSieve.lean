import ImbalancedChen.Part3OriginalExceptionalPostRemovalPair

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
The fixed-level exceptional sieve applied directly to the original raw
signed n row. Its frequency length still contains |a|*nu.
-/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRawNSieve20261120
open Finset
open scoped BigOperators MatrixGroups Classical
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualContinuousPoincarePairing20261110
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalNativeCuspFunctionals20261102 OriginalPrincipalTraceRow20261102r
open ActualPrincipalCuspOneRemoval20261102r
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau)
open OriginalExceptionalJInitialAverage20261113 (signed_row)
open OriginalExceptionalPostRemovalPair20261113 (rowLength rowMass)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

/-- A fixed original level and the full unremoved signed trace row. -/
theorem raw_original_row_square (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (upper negativeM : Bool) (ell : D4 → ℤ)
    (ha : D.block.atom.residue ≠ 0) {X : ℝ} (hX : 0 < X) :
    let q : ℕ+ := ⟨z.val, (levelCarrier_licensed D k z.property).1⟩
    (∑ i : ↥(exceptional q),
      X ^ tau q i.val * ‖originalNFunctional D r k upper negativeM ell q.val q.property i.val‖^2) ≤
      (sieveConstant*(1+max 1 X))*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ) : ℝ)*rowLength k)/(q.val : ℝ)) *
        rowMass D r k q := by
  classical
  let q : ℕ+ := ⟨z.val, (levelCarrier_licensed D k z.property).1⟩
  let G : ℕ := D.block.atom.residue.natAbs*k.1
  let L : ℝ := rowLength k
  let S := nCarrier D k q.val
  let s := principalTraceSign D k negativeM
  obtain ⟨n₀, hn₀⟩ := levelCarrier_has_n D k z.property
  have hnu : 0 < k.1 := (nCarrier_positive_coprime D k q.val hn₀).1
  have hG : 0 < G := Nat.mul_pos (Int.natAbs_pos.mpr ha) hnu
  have hGr : 0 < (G : ℝ) := by exact_mod_cast hG
  have hL : 0 < L := div_pos (dyadicScale_pos _) (by exact_mod_cast hnu)
  let f : ℕ → ℕ := fun n => G*n
  let w : ℕ → ℂ := fun m => traceBeta D r k upper negativeM ell q.val (m/G)
  have hf (n : ℕ) : f n / G = n := by
    simp [f, Nat.mul_comm, hG.ne']
  have hinj : Function.Injective f := by
    intro n m h
    have h' := congrArg (fun x : ℕ => x/G) h
    simpa only [hf] using h'
  have band (n : ℕ) (hn : n ∈ S) : L < (n : ℝ) ∧ (n : ℝ) ≤ 2*L := by
    have ⟨lo, hi⟩ := nCarrier_dyadic D k q.val hn
    have nu : 0 < (k.1 : ℝ) := by exact_mod_cast hnu
    rw [Nat.cast_mul] at lo hi
    constructor
    · exact (div_lt_iff₀ nu).mpr (by simpa only [L,rowLength,mul_comm (k.1 : ℝ) (n : ℝ)] using lo)
    · change (n : ℝ) ≤ 2*(dyadicScale k.2.1/(k.1 : ℝ))
      rw [← mul_div_assoc]
      exact (le_div_iff₀ nu).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using hi)
  have scaledBand (m : ℕ) (hm : m ∈ S.image f) :
      (G : ℝ)*L < (m : ℝ) ∧ (m : ℝ) ≤ 2*((G : ℝ)*L) := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have b := band n hn
    simp only [f, Nat.cast_mul]
    constructor
    · exact mul_lt_mul_of_pos_left b.1 hGr
    · nlinarith only [mul_le_mul_of_nonneg_left b.2 hGr.le]
  have range : X ≤ X*max 1 ((q.val : ℝ)/((G : ℝ)*L)) := by
    have hh := mul_le_mul_of_nonneg_left
      (le_max_left (1:ℝ) ((q.val : ℝ)/((G : ℝ)*L))) hX.le
    simpa only [mul_one] using hh
  have h := signed_row q true (mul_pos hGr hL) hX range
    (S.image f) w s (principalTraceSign_cases D k negativeM) scaledBand
  have hm : (∑ m ∈ S.image f, ‖w m‖^2) = rowMass D r k q := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    unfold rowMass
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hf,traceBeta_eq_principal_phase,norm_mul,sourceCuspPhase_norm,
      mul_one,norm_modulatedBeta]
  have hrow (i : ↥(exceptional q)) :
      (∑ m ∈ S.image f, w m*basisR q q.property i.val (originalFrame true) (s*(m:ℤ))) =
        originalNFunctional D r k upper negativeM ell q.val q.property i.val := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    unfold originalNFunctional
    apply Finset.sum_congr rfl
    intro n hn
    have hwf : w (f n) = traceBeta D r k upper negativeM ell q.val n := by
      simp only [w,hf]
    rw [hwf,traceIndex_eq_principalTraceSign]
    simp only [originalFrame,if_true,f,G,Nat.cast_mul,s]
  simp only [hrow,hm] at h
  simpa only [G,L] using h

end ImbalancedChen.Part3.OriginalRawNSieve20261120
end
