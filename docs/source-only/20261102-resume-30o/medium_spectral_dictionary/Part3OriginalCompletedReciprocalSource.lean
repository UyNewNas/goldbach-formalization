import ImbalancedChen.Part3OriginalSimultaneousPrefixCompletion
import ImbalancedChen.Part3OriginalMaskedOuterCaller
import ImbalancedChen.Part3ActualCompletedSquarePushforward

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This file supplies the missing positive smooth-cover caller for the M
common-s-frequency energy.  The six pieces are then identified with the
actual signed joint-beta source by the existing b-Poisson theorem.

No spectral PacketData is defined here.  In particular the s-frequency r
never becomes a Poisson m argument.  The later continuous spectral kernel,
cusp conversion and ABL extraction remain separate open obligations.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102
open ImbalancedChen.Part3.OriginalReciprocalPrefixDictionary20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalMaskedDivisorEnergy20261102
open ImbalancedChen.Part3.OriginalMaskedOuterCaller20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.ActualFixedFeaturePacketPushforwardSourceOnly
open ImbalancedChen.Part3.ActualPositiveLatticeSmoothCoverSourceOnly
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

namespace ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102

attribute [local instance] Classical.propDecidable

/-- One original frozen branch.  All three ordered polarization labels
and both independent smooth labels remain part of the branch identity.
Only polarS occurs in the inner reciprocal row after M's outer Cauchy. -/
structure OriginalData where
  block : FixedBlock
  atom : MediumAtom
  roughCutoff : ℝ
  key : Key
  small : ℕ
  rectangle : Rectangle
  smoothLeft : ℕ × ℕ
  smoothRight : ℕ × ℕ
  polarS : Fin 4
  polarR : Fin 4
  polarN : Fin 4

namespace OriginalData

def bScale (D : OriginalData) : ℝ := D.block.atom.U * scaleR D.key
def cScale (D : OriginalData) : ℝ := D.bScale * scaleS D.key
def fScale (D : OriginalData) : ℝ := 2 * D.block.atom.U / D.block.atom.Q1
def sCarrier (D : OriginalData) : Finset ℕ :=
  commonS D.atom D.roughCutoff D.key D.small D.smoothLeft
def hBound (D : OriginalData) : ℕ := Nat.ceil D.block.H
def omega (D : OriginalData) : ℤ → ℂ := originalOmega D.block D.rectangle
def lambda (D : OriginalData) (r : ZMod (prefixPeriod D.key)) : ℕ → ℂ :=
  completedLambda D.atom D.smoothLeft D.smoothRight D.polarS D.key r
def row (D : OriginalData) (r : ZMod (prefixPeriod D.key)) : Packet → ℂ :=
  finiteReciprocalRow 1 D.block.atom.residue D.sCarrier D.hBound (D.lambda r) D.omega

theorem bScale_pos (D : OriginalData) : 0 < D.bScale :=
  mul_pos D.block.U_pos (scaleR_pos D.key)
theorem cScale_pos (D : OriginalData) : 0 < D.cScale :=
  mul_pos D.bScale_pos (scaleS_pos D.key)
theorem fScale_pos (D : OriginalData) : 0 < D.fScale := by
  exact div_pos (mul_pos (by norm_num) D.block.U_pos) D.block.Q_pos

/-- The row is the original completedBare, by the M arithmetic dictionary. -/
theorem row_eq_completedBare (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (o : Outer) :
    D.row r ((packetB o, packetC o), o.f) =
      completedBare D.block D.atom D.roughCutoff D.key D.small D.rectangle
        D.smoothLeft D.smoothRight D.polarS o r := by
  exact (completedBare_eq_finiteReciprocalRow D.block D.atom D.roughCutoff
    D.key D.small D.rectangle D.smoothLeft D.smoothRight D.polarS o r).symm

theorem sCarrier_positive (D : OriginalData) {s : ℕ} (hs : s ∈ D.sCarrier) :
    0 < s := by
  have hlo := (commonS_window D.atom D.roughCutoff D.key D.small D.smoothLeft hs).1
  exact (pow_pos (by norm_num : 0 < (2 : ℕ)) D.key.u).trans_le hlo

theorem sCarrier_subset_factorCarrier (D : OriginalData) :
    D.sCarrier ⊆ factorCarrier (scaleS D.key) := by
  intro s hs
  have hw := commonS_window D.atom D.roughCutoff D.key D.small D.smoothLeft hs
  have hlo : scaleS D.key ≤ (s : ℝ) := by exact_mod_cast hw.1
  have hhi : (s : ℝ) ≤ 2 * scaleS D.key := by exact_mod_cast hw.2.le
  exact mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩

end OriginalData

/-- Pure reassociation of the existing M packet index. -/
def reassociate (v : PacketIndex) : Packet := ((v.1, v.2.1), v.2.2)

theorem reassociate_injective : Function.Injective reassociate := by
  intro v w h
  exact Prod.ext (congrArg (fun p : Packet => p.1.1) h)
    (Prod.ext (congrArg (fun p : Packet => p.1.2) h)
      (congrArg (fun p : Packet => p.2) h))

theorem representative_injective : Function.Injective packetRepresentative := by
  intro v w h
  have hb := congrArg (fun o : Outer => packetB o) h
  have hc := congrArg (fun o : Outer => packetC o) h
  have hf := congrArg (fun o : Outer => o.f) h
  rcases v with ⟨b, c, f⟩
  rcases w with ⟨b', c', f'⟩
  simp only [packetRepresentative, packetB, packetC, mul_one] at hb hc hf
  exact Prod.ext hb (Prod.ext hc hf)

/-- The new smooth caller reads the actual M ambient carrier; it does not
assume that carrier's membership in a six-cover box. -/
theorem ambient_physical_bounds (D : OriginalData) {v : PacketIndex}
    (hv : v ∈ packetAmbient D.block D.key) :
    D.bScale ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) ≤ 4 * D.bScale ∧
    D.cScale ≤ (v.2.1 : ℝ) ∧ (v.2.1 : ℝ) ≤ 8 * D.cScale ∧
    |(v.2.2 : ℝ)| ≤ D.fScale ∧ v.2.2 ≠ 0 ∧ v.1.Coprime v.2.1 := by
  obtain ⟨hrect, hcop⟩ := mem_filter.mp hv
  obtain ⟨hb, hrest⟩ := mem_product.mp hrect
  obtain ⟨hc, hf⟩ := mem_product.mp hrest
  have hU := D.block.U_pos
  have hR := scaleR_pos D.key
  have hS := scaleS_pos D.key
  obtain ⟨hbl, hbu⟩ := mem_Icc.mp hb
  obtain ⟨hcl, hcu⟩ := mem_Icc.mp hc
  obtain ⟨hf0, hfI⟩ := mem_erase.mp hf
  have hblo : D.bScale ≤ (v.1 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hbl)
  have hbhi : (v.1 : ℝ) ≤ 4 * D.bScale := by
    have h := (show (v.1 : ℝ) ≤ Nat.floor (4 * D.block.atom.U * scaleR D.key) by
      exact_mod_cast hbu).trans (Nat.floor_le (by positivity :
        0 ≤ 4 * D.block.atom.U * scaleR D.key))
    simpa only [OriginalData.bScale, mul_assoc] using h
  have hclo : D.cScale ≤ (v.2.1 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcl)
  have hchi : (v.2.1 : ℝ) ≤ 8 * D.cScale := by
    have h := (show (v.2.1 : ℝ) ≤
        Nat.floor (8 * D.block.atom.U * scaleR D.key * scaleS D.key) by
      exact_mod_cast hcu).trans (Nat.floor_le (by positivity :
        0 ≤ 8 * D.block.atom.U * scaleR D.key * scaleS D.key))
    simpa only [OriginalData.cScale, OriginalData.bScale, mul_assoc] using h
  have hfi : |v.2.2| ≤ (Nat.floor D.fScale : ℤ) :=
    abs_le.mpr (mem_Icc.mp hfI)
  have hfr : |(v.2.2 : ℝ)| ≤ (Nat.floor D.fScale : ℝ) := by exact_mod_cast hfi
  exact ⟨hblo, hbhi, hclo, hchi,
    hfr.trans (Nat.floor_le D.fScale_pos.le), hf0, hcop⟩

theorem ambient_mem_packetBox (D : OriginalData) {v : PacketIndex}
    (hv : v ∈ packetAmbient D.block D.key) :
    reassociate v ∈ packetBox D.bScale D.cScale D.fScale := by
  obtain ⟨hblo, hbhi, hclo, hchi, hf, hf0, hcop⟩ := ambient_physical_bounds D hv
  have hbp : 0 < v.1 := by exact_mod_cast D.bScale_pos.trans_le hblo
  have hcp : 0 < v.2.1 := by exact_mod_cast D.cScale_pos.trans_le hclo
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩, hcop, hf0⟩
  · exact mem_Ioc.mpr ⟨hbp, Nat.le_floor (by linarith [D.bScale_pos])⟩
  · exact mem_Ioc.mpr ⟨hcp, Nat.le_floor (by linarith [D.cScale_pos])⟩
  · exact mem_Icc.mpr ⟨Int.ceil_le.mpr (abs_le.mp hf).1,
      Int.le_floor.mpr (abs_le.mp hf).2⟩

theorem ambient_weight_ge_one (D : OriginalData) {v : PacketIndex}
    (hv : v ∈ packetAmbient D.block D.key) :
    1 ≤ packetWeight D.bScale D.cScale (reassociate v) := by
  obtain ⟨hbl, hbu, hcl, hcu, _⟩ := ambient_physical_bounds D hv
  exact one_le_mul (bCover_ge_one D.bScale_pos ⟨hbl, hbu⟩)
    (cCover_ge_one D.cScale_pos ⟨hcl, hcu⟩)

def completedAmbientEnergy (D : OriginalData) (r : ZMod (prefixPeriod D.key)) : ℝ :=
  ∑ v ∈ packetAmbient D.block D.key, ‖D.row r (reassociate v)‖^2

def smoothSix (D : OriginalData) (r : ZMod (prefixPeriod D.key)) : ℝ :=
  sixSmoothMass D.bScale D.cScale (packetBox D.bScale D.cScale D.fScale) (D.row r)

/-- Positive b,c smoothing of exactly the common completed reciprocal row.
Every signed f/h mask is still inside row.  No bound for an oscillatory
restricted sum by an unrestricted oscillatory sum is asserted. -/
theorem completedAmbientEnergy_le_smoothSix (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) : completedAmbientEnergy D r ≤ smoothSix D r := by
  calc
    _ ≤ ∑ v ∈ packetAmbient D.block D.key,
        packetWeight D.bScale D.cScale (reassociate v) * ‖D.row r (reassociate v)‖^2 := by
      apply sum_le_sum
      intro v hv
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (ambient_weight_ge_one D hv) (sq_nonneg ‖D.row r (reassociate v)‖)
    _ = ∑ w ∈ (packetAmbient D.block D.key).image reassociate,
        packetWeight D.bScale D.cScale w * ‖D.row r w‖^2 := by
      rw [sum_image]
      intro v hv w hw h
      exact reassociate_injective h
    _ ≤ ∑ w ∈ packetBox D.bScale D.cScale D.fScale,
        packetWeight D.bScale D.cScale w * ‖D.row r w‖^2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro w hw
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
        exact ambient_mem_packetBox D hv
      · intro w hw hnot
        exact mul_nonneg (packetWeight_nonneg _ _ _) (sq_nonneg _)
    _ = _ := cover_mass_eq_six _ _ _ _

theorem completedAmbientEnergy_eq_M (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) :
    completedAmbientEnergy D r =
      simultaneousEnergy D.block D.atom D.roughCutoff D.key D.small D.rectangle
        D.smoothLeft D.smoothRight D.polarS
        ((packetAmbient D.block D.key).image packetRepresentative) r := by
  unfold completedAmbientEnergy simultaneousEnergy
  rw [sum_image]
  · apply sum_congr rfl
    intro v hv
    rw [← D.row_eq_completedBare r]
    simp only [packetRepresentative, packetB, packetC, mul_one, reassociate]
  · intro v hv w hw h
    exact representative_injective h

/-- Direct consumer of M's simultaneous completion, followed by the
proved positive six-cover comparison.  r is chosen after the entire
ambient outer energy, before squaring/pushforward/Poisson m charting. -/
theorem exists_common_frequency_six_smooth (D : OriginalData) :
    ∃ r : ZMod (prefixPeriod D.key),
      unweightedPacketEnergy D.block D.atom D.roughCutoff D.key D.small
        D.rectangle D.smoothLeft D.smoothRight D.polarS ≤
      (2 + Real.log (prefixPeriod D.key))^2 * smoothSix D r := by
  obtain ⟨r, hr⟩ := exists_common_prefix_frequency D.block D.atom D.roughCutoff
    D.key D.small D.rectangle D.smoothLeft D.smoothRight D.polarS
    ((packetAmbient D.block D.key).image packetRepresentative)
  have hleft :
      (∑ o ∈ (packetAmbient D.block D.key).image packetRepresentative,
        rowEnvelope D.block D.atom D.roughCutoff D.key D.small D.rectangle
          D.smoothLeft D.smoothRight D.polarS o ^ 2) =
      unweightedPacketEnergy D.block D.atom D.roughCutoff D.key D.small
        D.rectangle D.smoothLeft D.smoothRight D.polarS := by
    rw [sum_image]
    · rfl
    · intro v hv w hw h
      exact representative_injective h
  rw [hleft, ← completedAmbientEnergy_eq_M] at hr
  exact ⟨r, hr.trans (mul_le_mul_of_nonneg_left
    (completedAmbientEnergy_le_smoothSix D r) (sq_nonneg _))⟩

open ActualCompletedSquarePushforwardSourceOnly

def originalSource (D : OriginalData) : Finset Source :=
  carrier 1 D.block.atom.residue D.sCarrier D.hBound
    (Icc (Int.ceil (-D.fScale)) (Int.floor D.fScale))

def jointBeta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (U : Finset Source) (zy : Output) : ℂ := beta U (D.lambda r) D.omega zy

def jointMass (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (M N : ℝ) (U : Finset Source) : ℂ :=
  ∑ zy ∈ U.image output,
    jointBeta D r U zy * completedKernel M N D.cScale D.block.atom.residue zy

def threeLanes (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (M N : ℝ) : ℂ :=
  jointMass D r M N (zeroSource (originalSource D)) +
    jointMass D r M N (positiveSource (originalSource D)) +
    jointMass D r M N (negativeSource (originalSource D))

theorem original_piece_eq_three_lanes (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (M N : ℝ) :
    completedPiece 1 D.block.atom.residue D.sCarrier D.hBound
      (D.lambda r) D.omega M N D.bScale D.cScale D.fScale = threeLanes D r M N := by
  exact completedPiece_eq_three_joint_betas 1 D.block.atom.residue D.sCarrier
    D.hBound (D.lambda r) D.omega M N D.bScale D.cScale D.fScale

/-- Exact six-piece identity, with zero difference and both signed y lanes
kept separately in EACH piece.  This is a complex equality, not a new
positivity claim for its expanded terms. -/
theorem original_six_eq_signed_joint_source (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) :
    (smoothSix D r : ℂ) =
      threeLanes D r D.bScale D.cScale +
      threeLanes D r D.bScale (2 * D.cScale) +
      threeLanes D r D.bScale (4 * D.cScale) +
      threeLanes D r (2 * D.bScale) D.cScale +
      threeLanes D r (2 * D.bScale) (2 * D.cScale) +
      threeLanes D r (2 * D.bScale) (4 * D.cScale) := by
  unfold smoothSix OriginalData.row
  rw [sixSmoothMass_eq_completed _ _ _ _ _ _ D.bScale_pos]
  simp only [original_piece_eq_three_lanes]

/-- The original a-unit gate is a theorem about the ACTUAL grouped source. -/
theorem original_output_licensed (D : OriginalData) {s : Source}
    (hs : s ∈ originalSource D) :
    0 < (output s).1 ∧ D.block.atom.residue.natAbs.Coprime (output s).1 :=
  ⟨output_positive_level (fun t ht => D.sCarrier_positive ht) hs,
    output_residue_coprime hs⟩

theorem original_output_bounds (D : OriginalData) {s : Source}
    (hs : s ∈ originalSource D) :
    0 < (output s).1 ∧ (scaleS D.key)^2 ≤ ((output s).1 : ℝ) ∧
      ((output s).1 : ℝ) ≤ 4 * (scaleS D.key)^2 ∧
      |((output s).2 : ℝ)| ≤ 4 * D.fScale * (D.hBound : ℝ) * scaleS D.key := by
  exact output_support (scaleS_pos D.key) D.fScale_pos.le D.sCarrier_subset_factorCarrier
    (fun f hf => actual_f_window_bound D.fScale hf) hs

/-- Nonzero beta gives an original source witness.  Empty geometry is
never asserted to supply a nonzero original packet. -/
theorem nonzero_beta_has_original_witness (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) {zy : Output}
    (hb : jointBeta D r (nonzeroSource (originalSource D)) zy ≠ 0) :
    ∃ s ∈ originalSource D, output s = zy ∧ zy.2 ≠ 0 ∧
      0 < zy.1 ∧ D.block.atom.residue.natAbs.Coprime zy.1 := by
  obtain ⟨s, hs, he⟩ := mem_image.mp (beta_ne_zero_mem_image hb)
  have hsc := (mem_filter.mp hs).1
  have hy := (mem_filter.mp hs).2
  have hd := original_output_licensed D hsc
  exact ⟨s, hsc, he, he ▸ hy, he ▸ hd.1, he ▸ hd.2⟩

end ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
end
