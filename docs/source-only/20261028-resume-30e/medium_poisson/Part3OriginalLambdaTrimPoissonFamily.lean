import ImbalancedChen.Part3OriginalGevreyCleanE3Assembly
import ImbalancedChen.Part3OriginalSamePsiS1OwnedAtlas
import ImbalancedChen.Part3MediumPrimitivePsiSource
import ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
import Mathlib.Tactic

/-!
Source only, uncompiled, zero formal credit.

Actual blocks are constructed from the literal lambdaTrim key, active
preliminary d, the original three disjoint q pieces and both h signs.
The strict receiver cutoff is exactly floor(z)+1/2; the source numerical
rough cutoff remains the original z. Inert S1 frequency fields are replaced
by the actual real H window, including the empty H<1 cases. The active-d
restriction is justified by the actual lambdaTrim zero theorem.

The old unfiltered dCarrier receiver cannot generally be instantiated:
inactive labels can have d not coprime to a, whereas FixedBlock requires
that licence. The new source index is exactly the active key/d source,
without claiming unfiltered coverage or throwing away a nonzero term.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex
open ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028
open ImbalancedChen.Part3.OriginalGevreyCleanE3Assembly20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas

namespace ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028

attribute [local instance] Classical.propDecidable

/-- Replace only the source profile fields; retain the actual lambdaTrim
coefficient of the independent source block. -/
def actualProfile (B : FixedBlock) : FixedBlock :=
  { B with
    psi0 := paperPsiComplex
    psi0_support := by
      intro v hv
      change (OriginalGevreyFinalPsi20261028.paperPsi v : ℂ) = 0
      rw [OriginalGevreyFinalPsi20261028.paperPsi_zero_outside v hv]
      rfl
    psiHat0 := 𝓕 paperPsiComplex }

@[simp] theorem actualProfile_carrier (B : FixedBlock) :
    (actualProfile B).carrier = B.carrier := rfl

/-- The q/d/w structure is inherited from the actual owned atlas;
H is its source real cutoff and hLo/hHi are actual positive/negative
windows. The original separation order is explicit and remains fixed. -/
def poissonAtlasBlock {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k)
    (negative : Bool) : FixedBlock :=
  let B := atlasBlock atom (strictReceiverCutoff z) y k hA j small hd
  actualProfile { B with
    hLo := if negative then -(Nat.ceil B.H : ℤ) else 1
    hHi := if negative then -1 else (Nat.ceil B.H : ℤ)
    separationOrder := Csep
    h_one_sign := by cases negative <;> simp }

@[simp] theorem poissonAtlasBlock_d {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).d = small := rfl

@[simp] theorem poissonAtlasBlock_atom {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).atom = atom := rfl

@[simp] theorem poissonAtlasBlock_lambda {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) (w : ℕ) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).lambdaD w =
      lambdaTrim atom (strictReceiverCutoff z) y k small w := rfl

@[simp] theorem poissonAtlasBlock_qCarrier {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).qCarrier =
      qPiece atom.Q1 j := rfl

/-- The source data themselves construct a finite family. No function
blocks with an unproved atom/d/SourceBind identity is a parameter. -/
abbrev SourceBlockIndex (atom : MediumAtom) (z y : ℝ) :=
  Σ k : {k : Key // k ∈ keyBank atom (strictReceiverCutoff z) y},
    Σ small : {small : ℕ // small ∈ activeD atom k.val}, Fin 3 × Bool

noncomputable instance sourceBlockIndexFintype (atom : MediumAtom) (z y : ℝ) :
    Fintype (SourceBlockIndex atom z y) := inferInstance

def genuineBlock {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) (i : SourceBlockIndex atom z y) : FixedBlock :=
  poissonAtlasBlock atom z y i.1.val hA Csep i.2.2.1 i.2.1.val i.2.1.property i.2.2.2

@[simp] theorem genuineBlock_atom {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) (i : SourceBlockIndex atom z y) :
    (genuineBlock atom z y hA Csep i).atom = atom := rfl

@[simp] theorem genuineBlock_d {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) (i : SourceBlockIndex atom z y) :
    (genuineBlock atom z y hA Csep i).d = i.2.1.val := rfl

@[simp] theorem genuineBlock_lambda {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) (i : SourceBlockIndex atom z y) (w : ℕ) :
    (genuineBlock atom z y hA Csep i).lambdaD w =
      lambdaTrim atom (strictReceiverCutoff z) y i.1.val i.2.1.val w := rfl

/-- No nonprimitive preliminary-d contribution is lost. This exact
zero identity is inherited from actual gamma support, not a d licence. -/
theorem actual_lambda_pair_sum_eq_active {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (r s : ℕ)
    (f : ℕ → ℂ) (hA : MediumAdmissible b σ κ c0 atom) :
    (∑ small ∈ dyadicWindow k.d,
      lambdaTrim atom (strictReceiverCutoff z) y k small r *
        star (lambdaTrim atom (strictReceiverCutoff z) y k small s) * f small) =
      ∑ small ∈ activeD atom k,
      lambdaTrim atom (strictReceiverCutoff z) y k small r *
        star (lambdaTrim atom (strictReceiverCutoff z) y k small s) * f small :=
  sum_d_lambda_pair_eq_active atom (strictReceiverCutoff z) y k r s f hA

/-- Signed ownership of exactly the real 1<=abs(h)<=H window. It is
empty for H<1; no singleton is fabricated by rounding ceil(H). -/
def signedHWindow (H : ℝ) (negative : Bool) : Finset ℤ :=
  ((Finset.Icc (-(Nat.ceil H : ℤ)) (Nat.ceil H : ℤ)) ∩
    (if negative then Finset.Icc (-(Nat.ceil H : ℤ)) (-1)
      else Finset.Icc 1 (Nat.ceil H : ℤ))).filter
    (fun h => 1 ≤ h.natAbs ∧ (h.natAbs : ℝ) ≤ H)

theorem signedHWindow_unique (H : ℝ) (h : ℤ) :
    (1 ≤ h.natAbs ∧ (h.natAbs : ℝ) ≤ H) ↔
      ∃! negative : Bool, h ∈ signedHWindow H negative := by
  constructor
  · intro hh
    have hceil : h.natAbs ≤ Nat.ceil H := by
      have hc : (h.natAbs : ℝ) ≤ (Nat.ceil H : ℝ) := hh.2.trans (Nat.le_ceil H)
      exact_mod_cast hc
    have hzero : h ≠ 0 := by
      intro heq
      subst h
      simpa using hh.1
    have hbound : -(Nat.ceil H : ℤ) ≤ h ∧ h ≤ (Nat.ceil H : ℤ) := by
      have hc : (h.natAbs : ℤ) ≤ (Nat.ceil H : ℤ) := by exact_mod_cast hceil
      rw [Int.natCast_natAbs] at hc
      exact abs_le.mp hc
    by_cases hn : h < 0
    · refine ⟨true, ?_, ?_⟩
      · simp only [signedHWindow, Finset.mem_filter, Finset.mem_inter, Finset.mem_Icc]
        exact ⟨⟨hbound, ⟨hbound.1, by omega⟩⟩, hh⟩
      · intro other ho
        cases other
        · have hpos : 1 ≤ h := (Finset.mem_Icc.mp
            (Finset.mem_inter.mp (Finset.mem_filter.mp ho).1).2).1
          omega
        · rfl
    · refine ⟨false, ?_, ?_⟩
      · have hp : 1 ≤ h := by omega
        simp only [signedHWindow, Finset.mem_filter, Finset.mem_inter, Finset.mem_Icc]
        exact ⟨⟨hbound, ⟨hp, hbound.2⟩⟩, hh⟩
      · intro other ho
        cases other
        · rfl
        · have hneg : h ≤ -1 := (Finset.mem_Icc.mp
            (Finset.mem_inter.mp (Finset.mem_filter.mp ho).1).2).2
          omega
  · rintro ⟨negative, hh, hu⟩
    exact (Finset.mem_filter.mp hh).2

/-- Direct source-family frequency-field identity, with real H support
and both h signs. S1's inert singleton is no longer used. -/
theorem poissonAtlasBlock_hCarrier {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    let B := atlasBlock atom (strictReceiverCutoff z) y k hA j small hd
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).hCarrier =
      signedHWindow B.H negative := by
  dsimp only
  cases negative <;> rfl


/-- The constructed block coefficient is the independently defined
original INCLUSIVE kept individual-window key fiber. This consumes the
peer identity instead of defining both sides as the same receiver. -/
theorem genuineBlock_lambda_eq_original_keyKept {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (x z : ℝ) (hz : 0 ≤ z)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (i : SourceBlockIndex atom z (ImbalancedChen.Part3OriginalS2PaperBlockEmbedding.roughY x))
    (w : ℕ) :
    (genuineBlock atom z (ImbalancedChen.Part3OriginalS2PaperBlockEmbedding.roughY x) hA Csep i).lambdaD w =
      Part3OriginalS2ActualKeyCoefficients.keyKept atom x z i.1.val i.2.1.val w := by
  rw [genuineBlock_lambda]
  exact (Part3OriginalS2ActualKeyCoefficients.keyKept_eq_actual_lambdaTrim
    hA x z hz i.1.val i.2.1.val w (Finset.mem_filter.mp i.2.1.property).1).symm


/-- The real Poisson window is computed from the actual key's common-d
and total rough scales, independently of q chart and frequency sign. -/
def keyRealH (atom : MediumAtom) (k : Key) : ℝ :=
  atom.Q1 * keyD k * keyR k ^ 2 * Real.log atom.scale ^ 5 / atom.V

theorem poissonAtlasBlock_H {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).H = keyRealH atom k := rfl

end ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
