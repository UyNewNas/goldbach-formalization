import ImbalancedChen.Part5OriginalH430ClassicalProperPayment
import ImbalancedChen.Part5OriginalH430ClassicalPowerTrim
import ImbalancedChen.Part5OriginalH430ClassicalRoughFloor

/-! The original untrimmed prime error and the original rough Lambda/log
HB atlas, compared with the true signed coefficient and physical centre.
The prime-power correction enters with its subtraction sign. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalPowerTransport
noncomputable section
open Finset Filter Real
open P5Z.AdmissibleAllRankIntegerGeometricFamily (Family licence originalWeight)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches (allGroup_actual_branch_split
  mediumAtlas noMediumAtlas originalMediumLow originalMediumHigh)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open Part5OriginalH430ClassicalSmoothNativeSignedSum (nativeResidual)
open Part5OriginalH430ClassicalRoughFloor (all_prime_cutoffs)
open Part5OriginalH430ClassicalProperPayment (proper_paid)
open Part5OriginalH430ClassicalPowerTrim (trim_paid)
open scoped Classical BigOperators

def roughAtlas (A : Family 200) (N : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (ρ : ℕ→ℝ) : ℂ :=
  ∑ k : Fin 201,∑ js∈chartBank (2*N) k.val,
    allGroupAtlas (licence A N k) 200 (2*N) N κ₀ Q (fun d => (ρ d:ℂ)) js

theorem remaining_branches (A : Family 200) (N : ℕ) (κ₀ ζ : ℝ) (Q : Finset ℕ) (ρ : ℕ→ℝ) :
    roughAtlas A N κ₀ Q ρ=∑ k : Fin 201,∑ js∈chartBank (2*N) k.val,
      (mediumAtlas (licence A N k) 200 (2*N) N κ₀ (originalMediumLow ζ js) (originalMediumHigh ζ js)
       Q (fun d => (ρ d:ℂ)) js+
       noMediumAtlas (licence A N k) 200 (2*N) N κ₀ (originalMediumLow ζ js) (originalMediumHigh ζ js)
       Q (fun d => (ρ d:ℂ)) js) := by
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro js _
  exact allGroup_actual_branch_split _ _ _ _ _ _ _ _ _ _

variable (μ : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
local notation "F₀" => family μ hd hh hh' hc hc'

theorem original_prime_to_rough {κ₀ ε : ℝ} (hk : 0<κ₀) (hk' : κ₀<1) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (ρ : ℕ→ℝ),(∀ d∈Q,0<d) → (∀ d,|ρ d|≤1) →
      (∀ d,ρ d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖(nativeResidual N μ hd hh hh' hc hc' Q ρ:ℂ)-roughAtlas F₀ N κ₀ Q ρ‖≤
        ε*singularNormalization N := by
  filter_upwards [proper_paid μ hd hh hh' hc hc' (half_pos hε),
    trim_paid μ hd hh hh' hc hc' hk hk' (half_pos hε),all_prime_cutoffs] with N hp ht hz
  intro Q ρ hQ hρ hr
  let rc := fun d => (ρ d:ℂ)
  let L := fun k : Fin 201 => licence F₀ N k
  let T := fun k : Fin 201 => trimReserve (L k) (2*N) N κ₀ Q rc
  let A := fun (k : Fin 201) js => allGroupAtlas (L k) 200 (2*N) N κ₀ Q rc js
  let P := fun (k : Fin 201) js => properPowerReserve (L k) 200 (2*N) N κ₀ Q rc js
  have hRank (k : Fin 201) :
      (Part3.primeProductSignedError k.val (2*N) N Q ρ
        (fun u => originalWeight F₀ N k (fun i => (u i).val)):ℂ)=
      T k+((∑ js∈chartBank (2*N) k.val,A k js)-(∑ js∈chartBank (2*N) k.val,P k js)) := by
    rw [original_prime_allGroup_discrepancy (L k) 200 (2*N) N κ₀ Q ρ,←sum_sub_distrib]
    apply congrArg (T k+·)
    apply sum_congr rfl
    intro js hjs
    rw [hz μ hd hh hh' hc hc' k κ₀ Q rc js hjs,add_zero]
  have heq : (nativeResidual N μ hd hh hh' hc hc' Q ρ:ℂ)-roughAtlas F₀ N κ₀ Q ρ=
      (∑ k : Fin 201,T k) - (∑ k : Fin 201,∑ js∈chartBank (2*N) k.val,P k js) := by
    have hn : (nativeResidual N μ hd hh hh' hc hc' Q ρ:ℂ)=
        ∑ k : Fin 201,(T k+((∑ js∈chartBank (2*N) k.val,A k js)-
          (∑ js∈chartBank (2*N) k.val,P k js))) := by
      unfold nativeResidual
      rw [Complex.ofReal_sum]
      exact sum_congr rfl (fun k _ => hRank k)
    rw [hn,sum_add_distrib,sum_sub_distrib]
    change ((∑ k : Fin 201,T k)+(_-_))-(∑ k : Fin 201,∑ js∈chartBank (2*N) k.val,A k js)=_
    abel
  rw [heq]
  apply (norm_sub_le _ _).trans
  have h1 := (norm_sum_le univ T).trans (ht Q ρ hQ hρ hr)
  have h2 := ((norm_sum_le univ (fun k : Fin 201 => ∑ js∈chartBank (2*N) k.val,P k js)).trans
    (sum_le_sum (s:=univ) (fun (k : Fin 201) _ => norm_sum_le (chartBank (2*N) k.val) (P k)))).trans
    (hp κ₀ Q ρ hQ hρ hr)
  linarith only [h1,h2]

/-- A physical relative error for the complete positive-width clamp family. -/
theorem fine_clamp {κ₀ ε : ℝ} (hk : 0<κ₀) (hk' : κ₀<1) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ (root : ℕ) (t₀ : ℝ),0≤t₀ → t₀≤1/12 → 1/((root:ℝ)+1)≤11/384 →
    ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a ν β : ℝ) (k : ℕ),
      let Q := P4AOriginalFiniteAll22FineDensity.modulusFamily ν β 0 N
      let ρ := P4AOriginalFiniteAll22FineDensity.coefficientFamily m r n e q a ν β k 0 N
      (∀ d,ρ d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) →
      ‖(nativeResidual N μ hd hh hh' hc hc' Q ρ:ℂ)-roughAtlas F₀ N κ₀ Q ρ‖≤
        ε*Part5OriginalH430RootIntervalTheta.clampMass N root t₀ := by
  let I := Part5OriginalH430RootIntervalTheta.intervalMass Part5UpperTables.OriginalU34.clampStart
    (1/3) (1/2)
  obtain ⟨hi,hw⟩ := Part5OriginalH430ClassicalRootThetaPayment.uniform_clamp_witness
  have hI : 0<I := hi
  filter_upwards [original_prime_to_rough μ hd hh hh' hc hc' hk hk' (mul_pos he (half_pos hI)),hw] with N H Hθ
  intro root t₀ ht ht' hn m r n e q a ν β k
  dsimp only
  intro hr
  let Q := P4AOriginalFiniteAll22FineDensity.modulusFamily ν β 0 N
  let ρ := P4AOriginalFiniteAll22FineDensity.coefficientFamily m r n e q a ν β k 0 N
  have hQ (d) (hl : d∈Q) : 0<d :=
    Nat.pos_of_ne_zero (P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hl).ne_zero
  have hry (d) : |ρ d|≤1 := P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d
  exact (H Q ρ hQ hry hr).trans ((mul_assoc _ _ _).le.trans
    (mul_le_mul_of_nonneg_left (Hθ root t₀ ht ht' hn) he.le))

end
end ImbalancedChen.Part5OriginalH430ClassicalPowerTransport

