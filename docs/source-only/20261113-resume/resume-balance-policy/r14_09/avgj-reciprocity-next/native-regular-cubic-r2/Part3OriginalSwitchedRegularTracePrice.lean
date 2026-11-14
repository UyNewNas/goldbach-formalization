import ImbalancedChen.Part3OriginalSwitchedCubicSingle

/-! The actual two regular remainders of the original and reflected traces
on one common interval, summed over a complete positive level dyad. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRegularTracePrice20261113
noncomputable section
open Finset Complex
open scoped Classical BigOperators
open OriginalSwitchedCubicSingle20261113 (first original)
open OriginalSwitchedCubicReflected20261113 (reflected)
open OriginalSwitchedRegularMarkExchange20261113 (principal incoming)
open OriginalSwitchedRegularBlockExchange20261113 (principalBlock incomingBlock)
open OriginalSwitchedRegularRows20261113 (amplitude)
open OriginalSwitchedTraceProjection20261113 (R C)
open OriginalSwitchedProjectionMask20261113 (mask regular_mask)
open OriginalSwitchedHolTraceError20261113 (test)
open OriginalSwitchedLevelIdentity20261113 (single)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels)
open OriginalRegularPacketTest20261113 (energy energy_nonneg)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open private masked short_mass from ImbalancedChen.Part3OriginalSwitchedProjectionMask
open private sum_levels from ImbalancedChen.Part3OriginalSwitchedHolomorphicInitial

theorem regular_dyad {ε : ℝ} (ep : 0<ε) :
    ∃ K : ℝ,0≤K ∧ ∀ (s : Bool) (j a b : ℕ) (lo : 2^j≤a),b≤2^(j+1) →
    ∀ (Y Q B ω : ℝ),1≤Y → 0<Q → 0<B →
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    let M := classicalMScale j
    (∑ d∈classicalLevels B,(‖R s d ap b Y Q ω‖+‖C s d ap b Y Q ω‖))≤
      K*(1+Real.log (2*Y)^2)*(B+M^(1+ε))*M := by
  obtain ⟨A,ap,P⟩ := original ep
  obtain ⟨D,dp,G⟩ := reflected ep
  let K := max A D
  have kp := ap.trans (le_max_left A D)
  refine ⟨8*K,by positivity,fun s j a b lo hi Y Q B ω y1 qp bp => ?_⟩
  let h := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let M := classicalMScale j
  let u := mask a b
  let E := energy (dyadicWindow j) u
  let L := 1+Real.log (2*Y)^2
  have en : 0≤E := energy_nonneg _ _
  have ln : 0≤L := by dsimp [L];positivity
  have mn : 0≤M := (by norm_num : (0:ℝ)≤1/2).trans (classicalMScale_bounds j).1
  let t := fun d : ℕ+ => 1+M^(1+ε)/(d.val:ℝ)
  have tn (d : ℕ+) : 0≤t d := add_nonneg zero_le_one (div_nonneg (Real.rpow_nonneg mn _) (Nat.cast_nonneg _))
  have up {v : ℝ} (hv : v≤K) (d : ℕ+) : v*L*t d*E≤K*L*t d*E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv ln) (tn d)) en
  have both (d : ℕ+) :
      ‖R s d h b Y Q ω‖≤K*L*t d*E ∧ ‖C s d h b Y Q ω‖≤K*L*t d*E := by
    cases s
    · have z (f : ℕ+→ℕ+→(ℝ→ℂ)→ℂ) :
          first f d j Y ω u=OriginalSwitchedTraceProjection20261113.pair h b ω
            (fun m n => f m n (single Y)) := masked j a b lo hi ω (fun m n => f m n (single Y))
      obtain ⟨p,q⟩ := P d j u Y ω y1
      rw [z] at p q
      exact ⟨p.trans (up (le_max_left A D) d),q.trans (up (le_max_left A D) d)⟩
    · obtain ⟨p,q⟩ := G d j u Y Q ω y1 qp
      obtain ⟨rr,cc⟩ := regular_mask d j a b lo hi Y Q ω
      change ‖principalBlock d j Y Q ω (mask a b)‖≤_ at p
      change ‖incomingBlock d j Y Q ω (mask a b)‖≤_ at q
      rw [rr] at p
      rw [cc] at q
      exact ⟨p.trans (up (le_max_right A D) d),q.trans (up (le_max_right A D) d)⟩
  have sum := sum_levels (ε:=ε) bp mn (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) kp) ln) en)
    (fun d => (add_le_add (both d).1 (both d).2).trans_eq (show (K*L*t d*E)+(K*L*t d*E)=(2*K*L*E)*t d by ring))
  have es : E≤2*M := short_mass j a b
  apply sum.trans
  change 2*(2*K*L*E)*(B+M^(1+ε))≤(8*K)*L*(B+M^(1+ε))*M
  have mp := mul_le_mul_of_nonneg_left es (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) kp) ln)
    (add_nonneg bp.le (Real.rpow_nonneg mn _)))
  linarith only [show (4*K*L*(B+M^(1+ε)))*E≤(4*K*L*(B+M^(1+ε)))*(2*M) from mp,
    show 2*(2*K*L*E)*(B+M^(1+ε))=4*K*L*(B+M^(1+ε))*E by ring,
    show 4*K*L*(B+M^(1+ε))*(2*M)=8*K*L*(B+M^(1+ε))*M by ring]

theorem log_allowance {ε : ℝ} (ep : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ Y : ℝ,1≤Y → 1+Real.log (2*Y)^2≤K*Y^ε := by
  let η := ε/2
  have hp : 0<η := half_pos ep
  let D := (2:ℝ)^η/η
  have dp : 0<D := div_pos (Real.rpow_pos_of_pos (by norm_num) _) hp
  refine ⟨1+D^2,by positivity,fun Y y1 => ?_⟩
  have yp := zero_lt_one.trans_le y1
  have ly : 0≤Real.log (2*Y) := Real.log_nonneg (by linarith only [y1])
  have h := Real.log_le_rpow_div (mul_nonneg (by norm_num : (0:ℝ)≤2) yp.le) hp
  rw [Real.mul_rpow (by norm_num) yp.le] at h
  have h' : Real.log (2*Y)≤D*Y^η := h.trans_eq (by dsimp only [D];ring)
  have squareBound := pow_le_pow_left₀ ly h' 2
  have ey : (Y^η)^2=Y^ε := by
    rw [sq,←Real.rpow_add yp,show η+η=ε by dsimp [η];ring]
  rw [mul_pow,ey] at squareBound
  nlinarith only [squareBound,Real.one_le_rpow y1 ep.le]

end
end ImbalancedChen.Part3.OriginalSwitchedRegularTracePrice20261113
