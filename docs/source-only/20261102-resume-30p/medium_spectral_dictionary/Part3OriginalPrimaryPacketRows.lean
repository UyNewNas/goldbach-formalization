import ImbalancedChen.Part3OriginalCompletedReciprocalSource
import ImbalancedChen.Part3ZActualPrimaryDyadicAssembly
import ImbalancedChen.Part3ActualCuspScalingSourceOnly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual O joint source is reindexed by its computed primary/sign/y-dyadic
key, then by the exact positive level and positive quotient n.  No arbitrary
beta, row support, coprime gate, inverse dictionary or energy is a premise.

The result constructs genuine CoprimePacket coefficient rows.  It deliberately
does not manufacture a PacketData.kernel: the normalized Kuznetsov/ABL link
from the original discrete c-sum to actual automorphic Fourier coefficients
is a separate, still open obligation.  A K or J scalar test alone is not it.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
open P3ActualLiteralPacketIntegralSourceOnly
open P3ActualCuspScalingSourceOnly

namespace ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102

attribute [local instance] Classical.propDecidable

abbrev BlockKey := ImbalancedChen.P3ZActualPrimaryDyadicAssembly.Key

def originalKeys (D : OriginalData) : Finset BlockKey :=
  keys D.block.atom.residue (originalSource D)

def primaryBlock (D : OriginalData) (k : BlockKey) : Finset Source :=
  block D.block.atom.residue (originalSource D) k

def outputCarrier (D : OriginalData) (k : BlockKey) : Finset Output :=
  (primaryBlock D k).image output

def levelCarrier (D : OriginalData) (k : BlockKey) : Finset ℕ :=
  (outputCarrier D k).image Prod.fst

def outputFibre (D : OriginalData) (k : BlockKey) (z : ℕ) : Finset Output :=
  (outputCarrier D k).filter (fun zy => zy.1 = z)

def quotientIndex (nu : ℕ) (zy : Output) : ℕ := (zy.2 / (nu : ℤ)).natAbs

def nCarrier (D : OriginalData) (k : BlockKey) (z : ℕ) : Finset ℕ :=
  (outputFibre D k z).image (quotientIndex k.1)

def decode (k : BlockKey) (z n : ℕ) : Output :=
  (z, signedY k.2.2 (k.1 * n))

def blockBeta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (zy : Output) : ℂ := jointBeta D r (primaryBlock D k) zy

theorem signedY_natAbs_of_sign (negative : Bool) (y : ℤ)
    (hsign : if negative then y < 0 else 0 < y) :
    signedY negative y.natAbs = y := by
  cases negative
  · simp only [Bool.false_eq_true, if_false] at hsign
    simp only [signedY, Bool.false_eq_true, if_false,
      Int.natCast_natAbs, abs_of_pos hsign]
  · simp only [if_true] at hsign
    simp only [signedY, if_true, Int.natCast_natAbs, abs_of_neg hsign, neg_neg]

/-- Every fact is read from an original source witness and the existing
computed-key block.  The multiplier is not a divisor of the modulus c. -/
theorem outputCarrier_data (D : OriginalData) (k : BlockKey) {zy : Output}
    (hzy : zy ∈ outputCarrier D k) :
    0 < k.1 ∧ 0 < zy.1 ∧ D.block.atom.residue.natAbs.Coprime zy.1 ∧
      zy.2 ≠ 0 ∧ (k.1 : ℤ) ∣ zy.2 ∧
      (quotientIndex k.1 zy).Coprime D.block.atom.residue.natAbs ∧
      (if k.2.2 then zy.2 < 0 else 0 < zy.2) ∧
      dyadicScale k.2.1 < |(zy.2 : ℝ)| ∧
      |(zy.2 : ℝ)| ≤ 2 * dyadicScale k.2.1 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hzy
  have hs0 := block_subset D.block.atom.residue (originalSource D) k hs
  have hso : s ∈ originalSource D := (mem_filter.mp hs0).1
  have hy : (output s).2 ≠ 0 := (mem_filter.mp hs0).2
  have hsd : s ∈ dyadicSource D.block.atom.residue (originalSource D)
      k.1 (dyadicScale k.2.1) k.2.2 := by
    rw [← block_eq_dyadicSource]
    exact hs
  obtain ⟨hp, hlo, hhi, hsign⟩ := mem_filter.mp hsd
  have hkey := (mem_filter.mp hp).2
  have hnu : 0 < k.1 := by
    simpa only [hkey] using rhoPrimaryNu_pos D.block.atom.residue (output s).2
  have hgate := primaryFibre_gate
    (fun t ht => (mem_filter.mp ht).2) hp
  have hlevel := original_output_licensed D hso
  exact ⟨hnu, hlevel.1, hlevel.2, hy, hgate.1, hgate.2,
    hsign, hlo, hhi⟩

/-- The inverse is proved on the literal output carrier.  Taking natAbs
does not identify the two signs: the fixed sign is restored by decode. -/
theorem decode_quotient (D : OriginalData) (k : BlockKey) {zy : Output}
    (hzy : zy ∈ outputCarrier D k) :
    decode k zy.1 (quotientIndex k.1 zy) = zy := by
  obtain ⟨hnu, hz, hcop, hy, hdvd, hq, hsign, hb⟩ := outputCarrier_data D k hzy
  have hprod : k.1 * quotientIndex k.1 zy = zy.2.natAbs := by
    have hh := congrArg Int.natAbs (Int.mul_ediv_cancel' hdvd)
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, quotientIndex] using hh
  apply Prod.ext rfl
  change signedY k.2.2 (k.1 * quotientIndex k.1 zy) = zy.2
  rw [hprod]
  exact signedY_natAbs_of_sign k.2.2 zy.2 hsign

theorem quotient_decode (k : BlockKey) (hnu : 0 < k.1) (z n : ℕ) :
    quotientIndex k.1 (decode k z n) = n := by
  exact signedY_div k.2.2 hnu n

theorem nCarrier_decode (D : OriginalData) (k : BlockKey) (z : ℕ) {n : ℕ}
    (hn : n ∈ nCarrier D k z) : decode k z n ∈ outputCarrier D k := by
  obtain ⟨zy, hzy, he⟩ := mem_image.mp hn
  obtain ⟨hout, hz⟩ := mem_filter.mp hzy
  have hrec : decode k z n = zy := by
    simpa only [hz, he] using decode_quotient D k hout
  rw [hrec]
  exact hout

theorem nCarrier_positive_coprime (D : OriginalData) (k : BlockKey) (z : ℕ) {n : ℕ}
    (hn : n ∈ nCarrier D k z) :
    0 < k.1 ∧ 0 < n ∧ n.Coprime D.block.atom.residue.natAbs := by
  have hdata := outputCarrier_data D k (nCarrier_decode D k z hn)
  have hn0 : n ≠ 0 := by
    intro he
    have hz := hdata.2.2.2.1
    apply hz
    simp only [decode, he, mul_zero, signedY]
    split_ifs <;> simp
  refine ⟨hdata.1, Nat.pos_of_ne_zero hn0, ?_⟩
  simpa only [quotient_decode k hdata.1 z n] using hdata.2.2.2.2.2.1

theorem nCarrier_dyadic (D : OriginalData) (k : BlockKey) (z : ℕ) {n : ℕ}
    (hn : n ∈ nCarrier D k z) :
    dyadicScale k.2.1 < ((k.1 * n : ℕ) : ℝ) ∧
      ((k.1 * n : ℕ) : ℝ) ≤ 2 * dyadicScale k.2.1 := by
  have hd := outputCarrier_data D k (nCarrier_decode D k z hn)
  simpa only [decode, signedY_abs] using hd.2.2.2.2.2.2.2

/-- This is the sharper original y-coordinate geometry required by the
physical scalar lemma, not merely the generic (-32,32) PacketData box. -/
theorem nCarrier_normalized (D : OriginalData) (k : BlockKey) (z : ℕ) {n : ℕ}
    (hn : n ∈ nCarrier D k z) :
    ((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1 ∈ Set.Icc (1 : ℝ) 2 := by
  have hU := dyadicScale_pos k.2.1
  have hb := nCarrier_dyadic D k z hn
  exact ⟨(le_div_iff₀ hU).mpr (by simpa only [one_mul] using hb.1.le),
    (div_le_iff₀ hU).mpr hb.2⟩

theorem levelCarrier_licensed (D : OriginalData) (k : BlockKey) {z : ℕ}
    (hz : z ∈ levelCarrier D k) :
    0 < z ∧ D.block.atom.residue.natAbs.Coprime z := by
  obtain ⟨zy, hzy, rfl⟩ := mem_image.mp hz
  have hd := outputCarrier_data D k hzy
  exact ⟨hd.2.1, hd.2.2.1⟩

/-- Every occupied level has an actual quotient index; no padding level
is used to make the row set appear nonempty. -/
theorem levelCarrier_has_n (D : OriginalData) (k : BlockKey) {z : ℕ}
    (hz : z ∈ levelCarrier D k) : (nCarrier D k z).Nonempty := by
  obtain ⟨zy, hzy, he⟩ := mem_image.mp hz
  exact ⟨quotientIndex k.1 zy,
    mem_image.mpr ⟨zy, mem_filter.mpr ⟨hzy, he⟩, rfl⟩⟩

/-- A finite arithmetic row type, with no fallback invalid level. -/
abbrev Row (D : OriginalData) (k : BlockKey) := {z : ℕ // z ∈ levelCarrier D k}

def rowPacket (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) : CoprimePacket :=
  dyadicPacket D.block.atom.residue (originalSource D) k.1 z.val
    (dyadicScale k.2.1) k.2.2 (D.lambda r) D.omega
    (levelCarrier_licensed D k z.property).1
    (levelCarrier_licensed D k z.property).2

/-- Its beta is the existing exact primary/sign/dyadic beta of the O
source.  This equality is proved from the existing block identity. -/
theorem rowPacket_beta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (n : ℕ) :
    (rowPacket D r k z).beta (k.1 * n) z.val =
      blockBeta D r k (decode k z.val n) := by
  exact (signed_beta_block_eq D.block.atom.residue (originalSource D)
    k.1 k.2.1 k.2.2 (D.lambda r) D.omega n z.val).symm

/-- The ABL coprime coefficient gate is supplied by the computed primary
source, even away from the finite n carrier (where beta may be zero). -/
theorem rowCoefficient_eq (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (n : ℕ) :
    signedCoefficient k.2.2 (rowPacket D r k z) n =
      blockBeta D r k (decode k z.val n) * cuspPhase k.2.2 z.val n := by
  change (if n.Coprime D.block.atom.residue.natAbs then
    (rowPacket D r k z).beta (k.1 * n) z.val * cuspPhase k.2.2 z.val n else 0) = _
  rw [rowPacket_beta]
  by_cases hc : n.Coprime D.block.atom.residue.natAbs
  · exact if_pos hc
  · have hb : blockBeta D r k (decode k z.val n) = 0 := by
      by_contra hb
      exact hc (assembled_beta_coprime hb)
    simp only [if_neg hc, hb, zero_mul]

/-- Exact unphasing is kept explicit.  It is not the automorphic ABL
oldform identity and pays no (|a|nu)^theta factor. -/
theorem rowCoefficient_unphase (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (n : ℕ) :
    signedCoefficient k.2.2 (rowPacket D r k z) n * cuspPhase (!k.2.2) z.val n =
      blockBeta D r k (decode k z.val n) := by
  rw [rowCoefficient_eq, mul_assoc]
  have hp : cuspPhase k.2.2 z.val n * cuspPhase (!k.2.2) z.val n = 1 := by
    cases k.2.2
    · exact cuspPhase_false_mul_true z.val n
    · exact cuspPhase_true_mul_false z.val n
  rw [hp, mul_one]

theorem norm_rowCoefficient (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (n : ℕ) :
    ‖signedCoefficient k.2.2 (rowPacket D r k z) n‖ =
      ‖blockBeta D r k (decode k z.val n)‖ := by
  rw [rowCoefficient_eq, norm_mul]
  simp only [cuspPhase, P3Period64NativeReconstructionSourceOnly.norm_e, mul_one]

/-- Exact quotient-coordinate change in a fixed level fibre. -/
theorem sum_outputFibre_eq_n (D : OriginalData) (k : BlockKey) (z : ℕ)
    (F : Output → ℂ) :
    (∑ zy ∈ outputFibre D k z, F zy) =
      ∑ n ∈ nCarrier D k z, F (decode k z n) := by
  unfold nCarrier
  rw [sum_image]
  · apply sum_congr rfl
    intro zy hzy
    have hd := decode_quotient D k (mem_filter.mp hzy).1
    have hz := (mem_filter.mp hzy).2
    exact congrArg F (by simpa only [hz] using hd.symm)
  · intro zy hzy zy' hzy' he
    have hd := decode_quotient D k (mem_filter.mp hzy).1
    have hd' := decode_quotient D k (mem_filter.mp hzy').1
    have hz := (mem_filter.mp hzy).2
    have hz' := (mem_filter.mp hzy').2
    calc
      zy = decode k z (quotientIndex k.1 zy) := by simpa only [hz] using hd.symm
      _ = decode k z (quotientIndex k.1 zy') := congrArg (decode k z) he
      _ = zy' := by simpa only [hz'] using hd'

/-- No multiplicity loss: one original joint output becomes one (z,n).
The original source multiplicities remain inside blockBeta. -/
theorem sum_output_eq_rows (D : OriginalData) (k : BlockKey) (F : Output → ℂ) :
    (∑ zy ∈ outputCarrier D k, F zy) =
      ∑ z ∈ levelCarrier D k, ∑ n ∈ nCarrier D k z, F (decode k z n) := by
  have hf := sum_fiberwise_of_maps_to (s := outputCarrier D k)
    (t := levelCarrier D k) (g := Prod.fst)
    (fun zy hzy => mem_image_of_mem _ hzy) F
  calc
    _ = ∑ z ∈ levelCarrier D k, ∑ zy ∈ outputFibre D k z, F zy := hf.symm
    _ = _ := by
      apply sum_congr rfl
      intro z hz
      exact sum_outputFibre_eq_n D k z F

/-- A nonzero original beta produces a nonempty TRUE arithmetic row and
a nonzero signed coefficient.  Unconditional nonemptiness would be false
for an empty original carrier or identically zero original coefficients. -/
theorem nonzero_original_beta_has_row (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) {zy : Output}
    (hb : jointBeta D r (nonzeroSource (originalSource D)) zy ≠ 0) :
    ∃ (k : BlockKey) (z : Row D k) (n : ℕ),
      k ∈ originalKeys D ∧ n ∈ nCarrier D k z.val ∧ decode k z.val n = zy ∧
        signedCoefficient k.2.2 (rowPacket D r k z) n ≠ 0 := by
  let k : BlockKey := outputKey D.block.atom.residue zy
  have hk : k ∈ originalKeys D := beta_nonzero_key_mem hb
  have hbb : blockBeta D r k zy ≠ 0 := by
    change beta (block D.block.atom.residue (originalSource D) k)
      (D.lambda r) D.omega zy ≠ 0
    rw [beta_block, if_pos rfl]
    exact hb
  have hout : zy ∈ outputCarrier D k := beta_ne_zero_mem_image hbb
  have hz : zy.1 ∈ levelCarrier D k := mem_image_of_mem _ hout
  let z : Row D k := ⟨zy.1, hz⟩
  let n : ℕ := quotientIndex k.1 zy
  have hn : n ∈ nCarrier D k z.val :=
    mem_image.mpr ⟨zy, mem_filter.mpr ⟨hout, rfl⟩, rfl⟩
  have hrec : decode k z.val n = zy := decode_quotient D k hout
  refine ⟨k, z, n, hk, hn, hrec, ?_⟩
  intro hc
  have he := norm_rowCoefficient D r k z n
  rw [hc, norm_zero, hrec] at he
  exact hbb (norm_eq_zero.mp he.symm)

end ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
end
