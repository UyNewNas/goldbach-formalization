import ImbalancedChen.Part3ActualContinuousClassFourier
import ImbalancedChen.Part3OriginalNativeCuspFunctionals

/-! The marked n row of the original manuscript on the complete
orthogonal continuous character basis. The inverse norm is the true
4πφ(H) on the actual almost-everywhere independent function span. -/
namespace ImbalancedChen.Part3.OriginalContinuousClassRemoval20261110

noncomputable section
open Complex Set Finset MeasureTheory
open scoped MatrixGroups BigOperators
open ActualYoungFormalClass20261110 ActualYoungCriticalProjection20261110
open ActualContinuousClassFourier20261110 ActualOrdinaryContinuousModes20261110
open ActualCriticalCuspEvaluation20261110 ActualYoungCriticalD20261110
open ActualCharacterOriginalCuspFourier20261110 ActualCuspDenominatorClasses20261110
open ActualYoungDilationInverse20261110
open OriginalCharacterTraceRow20261110 OriginalPrincipalTraceRow20261102r
open ActualPrincipalOldformRemoval20261102r ActualPrincipalCuspOneRemoval20261102r
open CriticalEisensteinScattering20261025a NormalizedEisensteinPrimeAmplitude20261026b
open CharacterPairDivisorAmplitude20261102s
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open P3NativePeriod64SamplingSourceOnly (D4)

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

def markedRow (S : Finset ℕ) (w : ℕ → ℂ) (index : ℕ → ℤ) (R : ℤ → ℂ) : ℂ :=
  ∑ n ∈ S,w n*R (index n)

def M (J j : ℕ) (ell : D4 → ℤ) : (ℤ → ℂ) → ℂ :=
  markedRow (commonMBlock J j) (fun p => star ((commonPoissonCompleted J j (ell 1)).weight p)) (fun p => (p : ℤ))

def source (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) : (ℤ → ℂ) → ℂ :=
  markedRow (nCarrier D k z.val) (traceBeta D r k upper negativeM ell z.val)
    (traceIndex D k negativeM z.val)

def reduced (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) : (ℤ → ℂ) → ℂ :=
  markedRow (nCarrier D k z.val) (fun n => modulatedBeta D r k upper ell z.val n*
    sourceCuspPhase z.val (-(principalTraceSign D k negativeM*(n : ℤ)))) (fun n => principalTraceSign D k negativeM*(n : ℤ))

theorem markedRow_sum {ι : Type*} [Fintype ι] (S : Finset ℕ) (w : ℕ → ℂ) (index : ℕ → ℤ)
    (c : ι → ℂ) (R : ι → ℤ → ℂ) :
    markedRow S w index (fun n => ∑ i : ι,c i*R i n) = ∑ i : ι,c i*markedRow S w index (R i) := by
  unfold markedRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro n _
  ring

def eigenFactor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℕ) (t : ℝ) : ℂ :=
  if q = 1 then normalizedDivisorAmplitude a (criticalPoint t) else pairAmplitude χ χ a (criticalPoint t)

theorem eigenFactor_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℕ) (t : ℝ) :
    ‖eigenFactor χ a t‖ ≤ (a.divisors.card : ℝ) := by
  have hs : criticalPoint t = criticalParameter t := by simp only [criticalPoint,criticalParameter,mul_comm I]
  by_cases hq : q = 1
  · simpa only [eigenFactor,if_pos hq,hs] using normalizedAmplitude_critical_norm_le_divisors a t
  · simpa only [eigenFactor,if_neg hq,hs,criticalParameter] using pairAmplitude_critical_norm_le_divisors χ χ a t

theorem dilation_removal (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (d : ℕ+) (hle : q^2*(d : ℕ) ∣ z.val) (t : ℝ) :
    let R := fun n => dilationR χ z.val (levelCarrier_licensed D k z.property).1 d hle true n t
    source D r k z upper negativeM ell R = eigenFactor χ (D.block.atom.residue.natAbs*k.1) t *
      reduced D r k z upper negativeM ell R := by
  dsimp only
  by_cases h : q = 1
  · subst q
    let e := complement z.val 1 (levelCarrier_licensed D k z.property).1 (NeZero.pos 1) d hle
    have he : (e : ℕ) ∣ z.val := Nat.div_dvd_of_dvd hle
    have hp : χ (-1 : ZMod 1) = 1 := by rw [Subsingleton.elim (-1 : ZMod 1) 1,map_one]
    have hc (n : ℤ) : sourceCuspPhase z.val (-n)*dilationR χ z.val (levelCarrier_licensed D k z.property).1 d hle true n t =
        principalFactor (criticalPoint t)*principalDilationAmplitude e n.natAbs (criticalPoint t) := by
      simp only [dilationR,if_true,cuspR,infR,if_pos rfl,hp,one_mul,← mul_assoc,sourceCuspPhase_neg_mul_self,e]
    have habs (a : ℕ) : (principalTraceSign D k negativeM*(a : ℤ)).natAbs = a := by
      rcases principalTraceSign_cases D k negativeM with hs | hs <;> simp [hs]
    unfold source reduced markedRow
    rw [eigenFactor,if_pos rfl,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [traceBeta_eq_principal_phase,traceIndex_eq_principalTraceSign,mul_assoc,hc,habs]
    rw [original_row_principal_dilation_removal D k z e he hn]
    ring
  · simpa only [source,reduced,markedRow,dilationR,if_true,cuspR,infR,if_neg h,cuspOneR,eigenFactor] using
      actual_character_row_removal D r k z upper negativeM ell (NeZero.pos q) h χ hχ d hle (criticalPoint t)

theorem channel_removal (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    ∀ i : CharacterSlots z.val, letI : NeZero i.2.conductor := ⟨i.2.conductor_ne_zero⟩
      source D r k z upper negativeM ell (fun n => channelR i true n t) =
        eigenFactor i.2.primitiveCharacter (D.block.atom.residue.natAbs*k.1) t*
          reduced D r k z upper negativeM ell (fun n => channelR i true n t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  intro i
  letI : NeZero i.2.conductor := ⟨i.2.conductor_ne_zero⟩
  let S := originalSlot i
  let c := fun b : Div S.L => dilationCoefficient i.2.primitiveCharacter (criticalPoint t) S.j b
  let R := fun (b : Div S.L) (n : ℤ) => dilationR i.2.primitiveCharacter z.val (NeZero.pos z.val)
    (dilation S.pos b) (legal S b) true n t
  change source D r k z upper negativeM ell (fun n => ∑ b : Div S.L,c b*R b n) =
    _*reduced D r k z upper negativeM ell (fun n => ∑ b : Div S.L,c b*R b n)
  have hS : source D r k z upper negativeM ell (fun n => ∑ b : Div S.L,c b*R b n) =
      ∑ b : Div S.L,c b*source D r k z upper negativeM ell (R b) := markedRow_sum _ _ _ _ _
  have hR : reduced D r k z upper negativeM ell (fun n => ∑ b : Div S.L,c b*R b n) =
      ∑ b : Div S.L,c b*reduced D r k z upper negativeM ell (R b) := markedRow_sum _ _ _ _ _
  rw [hS,hR,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have H := dilation_removal D r k z upper negativeM ell i.2.primitiveCharacter i.2.primitiveCharacter_isPrimitive
    (dilation S.pos b) (legal S b) t
  change source D r k z upper negativeM ell (R b) = _*reduced D r k z upper negativeM ell (R b) at H
  rw [H]
  ring

/-- Sum with the exact inverse orthogonal class norms. Once the raw
Kuznetsov factor 1/(4π) is moved outside, these are the relative 1/φ
weights. This formula uses the 4π factor exactly once. -/
def continuousMass (N : ℕ) [NeZero N] (X : CharacterSlots N → ℂ) : ℝ :=
  ∑ f : Div N, ∑ ξ : DirichletCharacter ℂ (band N f.1), ‖X ⟨f,ξ⟩‖^2/
    (4*Real.pi*((band N f.1).totient : ℝ))

theorem full_continuous_removal (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    continuousMass z.val (fun i => source D r k z upper negativeM ell (fun n => channelR i true n t)) ≤
      ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2*
      continuousMass z.val (fun i => reduced D r k z upper negativeM ell (fun n => channelR i true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  unfold continuousMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ξ _
  let i : CharacterSlots z.val := ⟨f,ξ⟩
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  let a := D.block.atom.residue.natAbs*k.1
  let W := 4*Real.pi*((band z.val f.1).totient : ℝ)
  let V := reduced D r k z upper negativeM ell (fun n => channelR i true n t)
  change ‖source D r k z upper negativeM ell (fun n => channelR i true n t)‖^2/W ≤
    (a.divisors.card : ℝ)^2*(‖V‖^2/W)
  rw [channel_removal D r k z upper negativeM ell t i,norm_mul,mul_pow]
  have he := pow_le_pow_left₀ (norm_nonneg _) (eigenFactor_bound ξ.primitiveCharacter a t) 2
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ ≤ (a.divisors.card : ℝ)^2*‖V‖^2/W :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (sq_nonneg _)) hW
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalContinuousClassRemoval20261110

