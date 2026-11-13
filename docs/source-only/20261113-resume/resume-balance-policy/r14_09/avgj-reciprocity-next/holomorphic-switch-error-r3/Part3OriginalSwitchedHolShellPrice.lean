import ImbalancedChen.Part3OriginalSwitchedUniformHolBudget
import ImbalancedChen.Part3OriginalHolomorphicInfinityCumulative

/-! Apply the actual all-weight identity-cusp sieve to the two linear
factors of each reflected mode. The weight shell is charged only once. -/
namespace ImbalancedChen.Part3.OriginalSwitchedHolShellPrice20261113
noncomputable section
open Finset Complex
open scoped BigOperators MatrixGroups
open OriginalRegularPacketTest20261113 (Dyadic energy)
open OriginalRegularHolomorphicCumulative20261113 (functional shell weights mem_weights)
open OriginalRegularHolomorphicWeight20261113 (order)
open OriginalHolomorphicInfinityCumulative20261113 (manuscript_holomorphic_infinity)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex formsBasis)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicCuspFrames20261110 (frameR)
open ActualContinuousPoincarePairing20261110 (originalFrame)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalSwitchedSeparatedNativeSlots20261113 (legs)
open OriginalSwitchedSeparatedBlocks20261113 (rowSum multiplier)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalSwitchedFourCoordinateSymbol20261113 (coefficient)
open P3Period64NativeReconstructionSourceOnly (e norm_e)
open private phaseAt_norm from ImbalancedChen.Part3ActualIntervalGeometricSum

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

def native (d : ℕ+) (h : ℕ) (i : BasisIndex d.val (h+1)) (m : ℕ) :=
  frameR d.val (NeZero.pos d.val) (h+1) (formsBasis d.val (h+1) i) 1 m

def gamma (h : ℕ) := Real.Gamma (2*((h+1:ℕ):ℝ))

theorem gamma_pos (h : ℕ) : 0<gamma h := Real.Gamma_pos_of_pos (by positivity)

def mixed (d : ℕ+) (j h : ℕ) (ω : ℝ) (k : D4→ℤ) (u : ℕ→ℂ) :=
  ∑ i : BasisIndex d.val (h+1),gamma h*‖legs j ω k (fun m => u m*native d h i m)‖

theorem multiplier_price (k : D4→ℤ) (ζ : ℝ) : ‖multiplier k ζ‖≤‖coefficient k‖ := by
  unfold multiplier
  split_ifs <;> simp only [norm_mul,norm_e,mul_one,le_rfl,norm_zero,norm_nonneg]

private theorem one_shell (d : ℕ+) (j h : ℕ) (ω : ℝ) (u : ℕ→ℂ) :
    (∑ i : BasisIndex d.val (h+1),gamma h*‖rowSum j ω (fun m => u m*native d h i m)‖^2)=
      shell d.val h false (dyadicWindow j) (fun n => phaseAt ω n*u n) (formsBasis d.val (h+1)) := by
  have G : gamma h=Real.Gamma (2*(h:ℝ)+2) := by
    dsimp only [gamma]
    congr 1
    push_cast;ring
  simp only [rowSum,Finset.univ_eq_attach,Finset.sum_attach,shell,functional,originalFrame,
    Bool.false_eq_true,if_false,native,←mul_assoc,G,Finset.mul_sum]

theorem mixed_price {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (d : ℕ+) (j h : ℕ) (ω : ℝ) (k : D4→ℤ) (u : ℕ→ℂ),
      mixed d j h ω k u≤C*(((2*h+1:ℕ):ℝ)^2+(classicalMScale j)^(1+ε)/(d.val:ℝ))*
        energy (dyadicWindow j) u := by
  obtain ⟨C,cp,H⟩ := manuscript_holomorphic_infinity ε ep
  refine ⟨C,cp,fun d j h ω k u => ?_⟩
  let S := dyadicWindow j
  let M := classicalMScale j
  let G := gamma h
  let K : ℝ := (order h:ℕ)
  let P := C*(K^2+M^(1+ε)/(d.val:ℝ))*energy S u
  have band : Dyadic M S := fun n hn => (OriginalExceptionalJNativeCompletion20261110.mem_full_classical_block j n).mp hn
  have k1 : 1≤K := by
    change (1:ℝ)≤((2*h+1:ℕ):ℝ)
    exact_mod_cast (show 1≤2*h+1 by omega)
  have row (y : ℝ) : (∑ i : BasisIndex d.val (h+1),G*‖rowSum j y (fun n => u n*native d h i n)‖^2)≤P := by
    rw [one_shell]
    let f := fun n => phaseAt y n*u n
    have p := H d.val k1 (OriginalClassicalSpectralSupports20261102.classicalMScale_bounds j).1 S f band
      (fun v => formsBasis d.val (v+1))
    have nn (r : ℕ) (_ : r∈weights K) : 0≤shell d.val r false S f (formsBasis d.val (r+1)) :=
      mul_nonneg (Real.Gamma_pos_of_pos (by positivity)).le (sum_nonneg fun _ _ => sq_nonneg _)
    have E : energy S f=energy S u := by simp only [energy,f,norm_mul,phaseAt_norm,one_mul]
    rw [E] at p
    exact (Finset.single_le_sum nn (mem_weights.mpr (show (order h:ℝ)≤K from le_rfl))).trans p
  let y := ω-(k 1:ℝ)/(64*M)
  let z := ω+(k 2:ℝ)/(64*M)
  let X := fun i : BasisIndex d.val (h+1) => rowSum j y (fun m => u m*native d h i m)
  let Z := fun i : BasisIndex d.val (h+1) => rowSum j z (fun m => u m*native d h i m)
  have pair (i : BasisIndex d.val (h+1)) : G*(‖X i‖*‖Z i‖)≤(G*‖X i‖^2+G*‖Z i‖^2)/2 :=
    (mul_le_mul_of_nonneg_left (show ‖X i‖*‖Z i‖≤(‖X i‖^2+‖Z i‖^2)/2 by
      nlinarith only [sq_nonneg (‖X i‖-‖Z i‖)]) (gamma_pos h).le).trans_eq (by ring)
  simp only [mixed,legs,norm_mul,norm_star]
  change (∑ i : BasisIndex d.val (h+1),G*(‖X i‖*‖Z i‖))≤P
  apply (sum_le_sum (fun i _ => pair i)).trans
  rw [←Finset.sum_div,Finset.sum_add_distrib]
  have hX : (∑ i : BasisIndex d.val (h+1),G*‖X i‖^2)≤P := row y
  have hZ : (∑ i : BasisIndex d.val (h+1),G*‖Z i‖^2)≤P := row z
  linarith only [hX,hZ]

end
end ImbalancedChen.Part3.OriginalSwitchedHolShellPrice20261113
