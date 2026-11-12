import ImbalancedChen.P4BOriginalMediumFibreSWWindow
import ImbalancedChen.P5ActualHBLogarithmRoleSW
import ImbalancedChen.P5ActualHBAuxiliaryPrefixes

/-! The separable numerator of the retained original HB mode. Its logarithm
is normalized at its own dyadic scale and restored by a scalar independent
of the integer, the complete physical modulus and the moving residue. -/
namespace ImbalancedChen.P4BOriginalMediumHBHead
noncomputable section
open Classical
open scoped BigOperators
open P5Z.ActualRoughHeathBrownWords (Role actual)
open P5Z.HBRightClosedDyadicRoles (Block Owns blockValue)
open P5Z.ActualHBDyadicProductWindow (lower owns_bounds)
open P5Z.ActualHBMediumBranchPartition (lower_one_le)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode logOccurrence)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots)
open P5Z.ActualSelectedRoughSlotAPDictionary (selectedCoefficient roughRole)
open P5Z.FixedProfileNormalizedLogVariation (retainedProfile logFactor logFactor_norm_le)
open P5Z.ActualChartFixedProfileRoughSW (profiledSelectedCoefficient selectedCoefficient_norm_le)
open P5Z.ActualHBLogarithmRoleSW (logarithmRoleMode logarithm_role_scalar_restoration logarithm_role_erasure)
open Part3.PrimeMellinProfileVariation20261026b (phase)
open P4BUpperPairOrderedRowGeometry (blockScales)

def muRole : Role → Bool
  | .mobius => true
  | _ => false

def logRole : Role → Bool
  | .logarithm => true
  | _ => false

def source (b : Block) (Z Y : ℝ) (r : Role) (τ : ℝ) (n : ℕ) : ℂ :=
  blockValue Z Y r b n * phase τ ((n:ℝ)/(lower b:ℝ))

def scalar (b : Block) (r : Role) : ℝ :=
  if logRole r then Real.log (2*(lower b:ℝ)) else 1

def alpha (b : Block) (Z Y : ℝ) (r : Role) (τ : ℝ) : ℕ → ℂ :=
  profiledSelectedCoefficient b (muRole r) Z Y τ (fun _ => 1) (logRole r)

theorem scalar_pos (b : Block) (r : Role) : 0<scalar b r := by
  have h := lower_one_le b
  cases r <;> simp only [scalar,logRole,if_true,Bool.false_eq_true,if_false]
  all_goals first | exact zero_lt_one | exact Real.log_pos (by linarith)

theorem restores (b : Block) (Z Y : ℝ) (r : Role) (τ : ℝ) (n : ℕ) :
    source b Z Y r τ n = (scalar b r:ℂ) * alpha b Z Y r τ n := by
  cases r with
  | one => simp [source,scalar,alpha,muRole,logRole,profiledSelectedCoefficient,
                 selectedCoefficient,roughRole,retainedProfile,logFactor]
  | mobius => simp [source,scalar,alpha,muRole,logRole,profiledSelectedCoefficient,
                    selectedCoefficient,roughRole,retainedProfile,logFactor]
  | logarithm =>
    have h := logarithm_role_scalar_restoration b Z Y τ (fun _ => 1) n
    rw [logarithm_role_erasure] at h
    simpa only [source,scalar,logRole,if_true,alpha,muRole,logarithmRoleMode,mul_one] using h

theorem alpha_one (b : Block) (Z Y : ℝ) (r : Role) (τ : ℝ) (n : ℕ) :
    ‖alpha b Z Y r τ n‖≤1 := by
  by_cases ho : Owns b n
  · have hlo : (lower b:ℝ)≤n := by exact_mod_cast (owns_bounds ho).1
    have hhi : (n:ℝ)≤2*(lower b:ℝ) := by exact_mod_cast (owns_bounds ho).2
    have hf := logFactor_norm_le (logRole r) (lower_one_le b) ⟨hlo,hhi⟩
    unfold alpha profiledSelectedCoefficient retainedProfile
    simp only [one_mul,norm_mul]
    simpa only [one_mul] using mul_le_mul (selectedCoefficient_norm_le b (muRole r) Z Y τ n)
      hf (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  · simp [alpha,profiledSelectedCoefficient,selectedCoefficient,blockValue,ho]

theorem alpha_rough {b : Block} {Z Y : ℝ} {r : Role} {τ : ℝ} {n : ℕ}
    (h : alpha b Z Y r τ n≠0) : ∀ p : ℕ,p.Prime → p∣n → Z<(p:ℝ) := by
  apply P5Z.ActualHBAuxiliaryPrefixes.actual_rough_support Z Y r n
  intro hz
  have he : source b Z Y r τ n=0 := by simp [source,blockValue,hz]
  rw [restores] at he
  exact h ((mul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr (scalar_pos b r).ne'))

theorem source_product {t : ℕ} (bs : Fin t→Block) (Z : ℝ) (ys : Fin t→ℝ)
    (rs : Fin t→Role) (ξ : Fin t→ℝ) {n : Fin t→ℕ} (hn : n∈rectangle bs) :
    hbSlots Z ys rs n*occurrenceMode (blockScales bs) n ξ =
      ∏ j,source (bs j) Z (ys j) (rs j) (ξ j) (n j) := by
  unfold hbSlots occurrenceMode
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [source,blockValue,if_pos ((mem_rectangle bs n).mp hn j),phase,logOccurrence,
    blockScales,Complex.ofReal_mul]
  apply congrArg (fun z : ℂ => actual Z (ys j) (rs j) (n j)*z)
  apply congrArg Complex.exp
  ring

theorem normalized_product {t : ℕ} (bs : Fin t→Block) (Z : ℝ) (ys : Fin t→ℝ)
    (rs : Fin t→Role) (ξ : Fin t→ℝ) {n : Fin t→ℕ} (hn : n∈rectangle bs) :
    hbSlots Z ys rs n*occurrenceMode (blockScales bs) n ξ =
      ((∏ j,scalar (bs j) (rs j):ℝ):ℂ) *
        ∏ j,alpha (bs j) Z (ys j) (rs j) (ξ j) (n j) := by
  rw [source_product bs Z ys rs ξ hn]
  simp_rw [restores]
  rw [Finset.prod_mul_distrib]
  push_cast <;> rfl

end
end ImbalancedChen.P4BOriginalMediumHBHead
