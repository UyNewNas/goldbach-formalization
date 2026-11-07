import ImbalancedChen.ActualThirdOriginalSixTentCandidates

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30. Direct selected-tent selector-guard
bridge. Integer coefficients are fixed by the selected TentSum; the original tests
imply the three semantic guards required by the existing tent supplier. -/
namespace ImbalancedChen.OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly

noncomputable section
open Set
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly

def literalTentX : TentSum → ℤ
  | .x => 1 | .y => 0 | .xy => 1 | .xz => 1 | .yz => 0 | .xyz => 1

def literalTentY : TentSum → ℤ
  | .x => 0 | .y => 1 | .xy => 1 | .xz => 0 | .yz => 1 | .xyz => 1

def literalTentZ : TentSum → ℤ
  | .x => 0 | .y => 0 | .xy => 0 | .xz => 1 | .yz => 1 | .xyz => 1

theorem literalTentX_cast (s : TentSum) : (literalTentX s : ℝ)=sumX s := by
  cases s <;> norm_num [literalTentX,sumX]

theorem literalTentY_cast (s : TentSum) : (literalTentY s : ℝ)=sumY s := by
  cases s <;> norm_num [literalTentY,sumY]

theorem literalTentZ_cast (s : TentSum) : (literalTentZ s : ℝ)=sumZ s := by
  cases s <;> norm_num [literalTentZ,sumZ]
/-- Exact integer-to-physical transport for the six original minorant planes.
Coefficient triples are definitional functions of the selected TentSum. hbranch is the
actual if/elif test on the cross-multiplied delta numerator (denominator128);
hroot and hres are the original root filter and positive residual test.
No desired active-plane, cap, mean, query, weight or integral bound is input.
The selected s and k remain explicit inputs; this transports their literal tests. -/
theorem original_selected_tent_guard_bridge
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ)
    (D T : ℤ) (a b : BoxPoint)
    (hD : D=48000*2^24) (hT : T=481573208064)
    (ha : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hb : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (hbranch : match k with
      | .rise => -50*D+256*((literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2)≤0
      | .fall => ¬(-50*D+256*((literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2)≤0) ∧
          0≤-50*D+256*((literalTentX s)*lo 0+(literalTentY s)*lo 1+(literalTentZ s)*lo 2))
    (hroot : match k with
      | .rise => D+(literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2≤2*T
      | .fall => 57*D-96*((literalTentX s)*lo 0+(literalTentY s)*lo 1+(literalTentZ s)*lo 2)≤64*T)
    (hres : match k with
      | .rise => 0<D+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1
      | .fall => 0<57*D+(-96*(literalTentX s)-64)*hi 0+(-96*(literalTentY s)-64)*hi 1) :
    sourceActive s k a b ∧ planeUpper s k a b≤thirdPrefixTheta ∧
      0<oldNumerator s k b := by
  have hDpos : (0:ℝ)<(D:ℝ) := by rw [hD]; norm_num
  have hDne : (D:ℝ)≠0 := hDpos.ne'
  have hTH : (T:ℝ)=(D:ℝ)*thirdPrefixTheta := by
    rw [hT,hD]
    norm_num [thirdPrefixTheta]
  have h128 : (0:ℝ)<128*(D:ℝ) := mul_pos (by norm_num) hDpos
  have hdelta (v : Fin 3 → ℤ) (p : BoxPoint)
      (hp : ∀ i, p i=(v i:ℝ)/(D:ℝ)) :
      ((-50*D+256*((literalTentX s)*v 0+(literalTentY s)*v 1+(literalTentZ s)*v 2):ℤ):ℝ)=
        128*(D:ℝ)*sourceDelta s p := by
    rw [sourceDelta_eq]
    unfold tentSum VariableEnvelope.mu
    rw [hp 0,hp 1,hp 2,←literalTentX_cast s,←literalTentY_cast s,←literalTentZ_cast s]
    push_cast
    field_simp [hDne]
    ring
  cases k with
  | rise =>
      have h2 : (0:ℝ)<2*(D:ℝ) := mul_pos (by norm_num) hDpos
      have htest : ((-50*D+256*((literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2):ℤ):ℝ)≤0 := by
        exact_mod_cast hbranch
      rw [hdelta hi b hb] at htest
      have hactive : sourceActive s .rise a b := by
        change sourceDelta s b≤0
        exact (mul_le_mul_left h128).mp (by simpa only [mul_zero] using htest)
      have hupperIdentity : ((D+(literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2:ℤ):ℝ)=
          2*(D:ℝ)*planeUpper s .rise a b := by
        unfold planeUpper tentPlane planeConst planeSlope tentSum
        rw [hb 0,hb 1,hb 2,←literalTentX_cast s,←literalTentY_cast s,←literalTentZ_cast s]
        push_cast
        field_simp [hDne]
        ring
      have hrootReal : ((D+(literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2:ℤ):ℝ)≤2*(T:ℝ) := by
        exact_mod_cast hroot
      have hupper : planeUpper s .rise a b≤thirdPrefixTheta := by
        apply (mul_le_mul_left h2).mp
        calc
          2*(D:ℝ)*planeUpper s .rise a b=
              ((D+(literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2:ℤ):ℝ) := hupperIdentity.symm
          _≤2*(T:ℝ) := hrootReal
          _=2*(D:ℝ)*thirdPrefixTheta := by rw [hTH]; ring
      have hresIdentity : ((D+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1:ℤ):ℝ)=
          2*(D:ℝ)*oldNumerator s .rise b := by
        unfold oldNumerator oldX oldY planeConst planeSlope
        rw [hb 0,hb 1,←literalTentX_cast s,←literalTentY_cast s]
        push_cast
        field_simp [hDne]
        ring
      have hresReal : (0:ℝ)<((D+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1:ℤ):ℝ) := by
        exact_mod_cast hres
      rw [hresIdentity] at hresReal
      have hresidual : 0<oldNumerator s .rise b :=
        (mul_lt_mul_left h2).mp (by simpa only [mul_zero] using hresReal)
      exact ⟨hactive,hupper,hresidual⟩
  | fall =>
      have h64 : (0:ℝ)<64*(D:ℝ) := mul_pos (by norm_num) hDpos
      have htestUpper : (0:ℝ)<
          ((-50*D+256*((literalTentX s)*hi 0+(literalTentY s)*hi 1+(literalTentZ s)*hi 2):ℤ):ℝ) := by
        exact_mod_cast (lt_of_not_ge hbranch.1)
      have htestLower : (0:ℝ)≤
          ((-50*D+256*((literalTentX s)*lo 0+(literalTentY s)*lo 1+(literalTentZ s)*lo 2):ℤ):ℝ) := by
        exact_mod_cast hbranch.2
      rw [hdelta hi b hb] at htestUpper
      rw [hdelta lo a ha] at htestLower
      have hactive : sourceActive s .fall a b := by
        change ¬sourceDelta s b≤0 ∧ 0≤sourceDelta s a
        have hpositive : 0<sourceDelta s b :=
          (mul_lt_mul_left h128).mp (by simpa only [mul_zero] using htestUpper)
        have hnonnegative : 0≤sourceDelta s a :=
          (mul_le_mul_left h128).mp (by simpa only [mul_zero] using htestLower)
        exact ⟨not_le_of_gt hpositive,hnonnegative⟩
      have hupperIdentity : ((57*D-96*((literalTentX s)*lo 0+(literalTentY s)*lo 1+(literalTentZ s)*lo 2):ℤ):ℝ)=
          64*(D:ℝ)*planeUpper s .fall a b := by
        unfold planeUpper tentPlane planeConst planeSlope tentSum
        rw [ha 0,ha 1,ha 2,←literalTentX_cast s,←literalTentY_cast s,←literalTentZ_cast s]
        push_cast
        field_simp [hDne]
        ring
      have hrootReal : ((57*D-96*((literalTentX s)*lo 0+(literalTentY s)*lo 1+(literalTentZ s)*lo 2):ℤ):ℝ)≤64*(T:ℝ) := by
        exact_mod_cast hroot
      have hupper : planeUpper s .fall a b≤thirdPrefixTheta := by
        apply (mul_le_mul_left h64).mp
        calc
          64*(D:ℝ)*planeUpper s .fall a b=
              ((57*D-96*((literalTentX s)*lo 0+(literalTentY s)*lo 1+(literalTentZ s)*lo 2):ℤ):ℝ) := hupperIdentity.symm
          _≤64*(T:ℝ) := hrootReal
          _=64*(D:ℝ)*thirdPrefixTheta := by rw [hTH]; ring
      have hresIdentity : ((57*D+(-96*(literalTentX s)-64)*hi 0+(-96*(literalTentY s)-64)*hi 1:ℤ):ℝ)=
          64*(D:ℝ)*oldNumerator s .fall b := by
        unfold oldNumerator oldX oldY planeConst planeSlope
        rw [hb 0,hb 1,←literalTentX_cast s,←literalTentY_cast s]
        push_cast
        field_simp [hDne]
        ring
      have hresReal : (0:ℝ)<
          ((57*D+(-96*(literalTentX s)-64)*hi 0+(-96*(literalTentY s)-64)*hi 1:ℤ):ℝ) := by
        exact_mod_cast hres
      rw [hresIdentity] at hresReal
      have hresidual : 0<oldNumerator s .fall b :=
        (mul_lt_mul_left h64).mp (by simpa only [mul_zero] using hresReal)
      exact ⟨hactive,hupper,hresidual⟩

end
end ImbalancedChen.OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
