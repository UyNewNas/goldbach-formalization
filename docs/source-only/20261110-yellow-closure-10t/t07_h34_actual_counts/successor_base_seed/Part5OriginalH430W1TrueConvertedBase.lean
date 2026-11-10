import ImbalancedChen.Part5OriginalH430W1PhysicalRoughDictionary

/-! All 70 W1 true marked integer masses reach their actual stored 430
base. Only the additive-prime to positive unsifted-product inequality is
left in the W1 switched source. -/
namespace ImbalancedChen.Part5OriginalH430W1TrueConvertedBase
noncomputable section
open Set Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound (W1Target W1Anchor)
open P2OriginalPositiveSameQMassLift P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedSwitchedTrueNormalization (trueAlpha thetaConversion rawMainAtom rawMainAtom_to_thetaAtom)
open P2EnhancedNonunitWordMass (rawScale)
open P2SeedOmegaLiteralFibre (omegaCap)
open P2N48TiedMomentPrimitives (moment11)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount original_W1_parameters)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430W1OriginalBaseEnclosure (currentK tableK all70_archived_base_vs_envelope)
open Part5OriginalH430W1SwitchedBuchstabIntegral (envelope)
open Part5OriginalH430W1ConvertedPrimeQuadrature (actual_triple_quadrature)
open Part5OriginalH430W1InclusiveRoughCounts (mass_to_prime_sum)
open Part5OriginalH430W1PhysicalRoughDictionary (integerMass actual_integer_mass_eq)
open Part5OriginalH430W1SignedOrdinaryBase (switchedDebt ordinaryBase)
open Part5OriginalH430FixedReadDictionary (baseValue)
open scoped Classical BigOperators Topology

private theorem envelope_eq (i : Fin 7) (j : Fin 10) :
    envelope i j=omegaCap*moment11 (1/W1Anchor j) (1/W1Target i) := by
  let s := W1Target i
  let a := W1Anchor j
  have h := original_W1_parameters i j
  have hs : 0<s := by linarith [h.1]
  have ha := hs.trans_le h.2.1
  have hd : (1/s)/(1/a)=a/s := by field_simp [hs.ne',ha.ne']
  change omegaCap*((a+s)*log (a/s)-2*(a-s))=omegaCap*moment11 (1/a) (1/s)
  rw [moment11,hd]
  field_simp [hs.ne',ha.ne'] <;> ring

private theorem fixed_rough_bound {η A ε : ℝ} (hη : 0<η) (hA : η≤A) (he : 0<ε)
    (i : Fin 7) (j : Fin 10) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q L : ℝ) (d : ℕ),
      L∈Icc η A → 0<d → Q=(d:ℝ)*(N:ℝ)^L → 2≤trueAlpha N Q d →
      thetaConversion N d*integerMass N Q d i j ≤ thetaAtom N Q d*(envelope i j+ε) := by
  let a := 1/W1Anchor j
  let b := 1/W1Target i
  let m := moment11 a b
  let C := omegaCap+2*|m|+2
  let τ := min 1 (ε/C)
  have hω := P2SeedOmegaGlobalEnvelope.omegaCap_positive
  have hC : 0<C := by dsimp [C]; positivity
  have hτ : 0<τ := lt_min (by norm_num) (div_pos he hC)
  have hτ1 : τ≤1 := min_le_left _ _
  have htpay : τ*C≤ε := (le_div_iff₀ hC).mp (min_le_right _ _)
  have hcost : (omegaCap+2*τ)*(m+τ)≤omegaCap*m+ε := by
    have hh : omegaCap+2*m+2*τ≤C := by dsimp [C]; linarith only [le_abs_self m,hτ1]
    linarith only [mul_le_mul_of_nonneg_left hh hτ.le,htpay]
  have hm := original_W1_parameters i j
  have hs : 0<W1Target i := by linarith [hm.1]
  have ha := hs.trans_le hm.2.1
  obtain ⟨Ta,hTa,hraw⟩ := mass_to_prime_sum hη hτ
  obtain ⟨Tb,hquad⟩ := actual_triple_quadrature hη hA
    (one_div_le_one_div_of_le ha hm.2.2) (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hm.1)
    (one_div_le_one_div_of_le hs hm.2.1) hτ
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN Q L d hL hd hQ hα
  have hNa := (le_max_left _ _).trans hN
  have h4 := hTa.trans hNa
  have hL' := hη.trans_le hL.1
  have hR := sameQ_residual_gt_one (by omega) hd hL' hQ
  have hraw' := hraw N hNa Q L d i j hL.1 hd hQ hα
  rw [←actual_integer_mass_eq (by omega) hd hL' hQ i j] at hraw'
  have hq := hquad N ((le_max_right _ _).trans hN) L hL
  have hsc : 0≤rawScale N Q d := div_nonneg (Nat.cast_nonneg N)
    (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  have hnum : integerMass N Q d i j ≤ rawScale N Q d*(envelope i j+ε) := by
    rw [envelope_eq]
    change integerMass N Q d i j≤rawScale N Q d*(omegaCap*m+ε)
    calc
      _ ≤ _ := hraw'
      _ ≤ rawScale N Q d*(omegaCap+2*τ)*(m+τ) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hsc (by positivity))
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcost hsc
  have hconv := P2EnhancedUnitSourceMass.thetaConversion_nonneg h4 hd hR
  have hmul := mul_le_mul_of_nonneg_left hnum hconv
  change thetaConversion N d*integerMass N Q d i j ≤
    thetaConversion N d*rawMainAtom N Q d (fun _ => envelope i j+ε) at hmul
  rwa [rawMainAtom_to_thetaAtom (by omega) hd Q hR] at hmul

theorem all70_rough_bound {η A ε : ℝ} (hη : 0<η) (hA : η≤A) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10),
      L∈Icc η A → 0<d → Q=(d:ℝ)*(N:ℝ)^L → 2≤trueAlpha N Q d →
      thetaConversion N d*integerMass N Q d i j ≤ thetaAtom N Q d*(envelope i j+ε) := by
  choose T h4 hT using (fun a : Fin 7 × Fin 10 => fixed_rough_bound hη hA he a.1 a.2)
  refine ⟨univ.sup T,(h4 (0,0)).trans (le_sup (mem_univ _)),?_⟩
  intro N hN Q L d i j
  exact hT (i,j) N ((le_sup (mem_univ _)).trans hN) Q L d

/-- The literal additive-prime discrepancy against the genuine converted
rough-integer mass for the same word and action. -/
def primeDebt (N : ℕ) (Q : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ((rawTripleCount N d (d*N) (receiver N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)):ℝ) -
    (currentK:ℝ)/4*(thetaConversion N d*integerMass N Q d i j))/2

theorem all70_true_converted_base {η A ε : ℝ} (hη : 0<η) (hA : η≤A) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10),
      L∈Icc η A → 0<d → Q=(d:ℝ)*(N:ℝ)^L → 2≤trueAlpha N Q d →
      switchedDebt N Q d i j ≤ primeDebt N Q d i j+ε*thetaAtom N Q d := by
  obtain ⟨T,hT,h⟩ := all70_rough_bound hη hA he
  refine ⟨T,hT,?_⟩
  intro N hN Q L d i j hL hd hQ hα
  have h4 := hT.trans hN
  have hR := sameQ_residual_gt_one (by omega) hd (hη.trans_le hL.1) hQ
  have hθ := thetaAtom_nonneg h4 hd hR
  have h₁ := mul_le_mul_of_nonneg_right (all70_archived_base_vs_envelope i j) hθ
  have h₂ := mul_le_mul_of_nonneg_left (h N hN Q L d i j hL hd hQ hα)
    (by norm_num [tableK] : 0≤(tableK:ℝ)/8)
  have hcost : 0≤thetaConversion N d*integerMass N Q d i j := by
    apply mul_nonneg (P2EnhancedUnitSourceMass.thetaConversion_nonneg h4 hd hR)
    exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have herr := mul_nonneg he.le hθ
  unfold switchedDebt primeDebt
  norm_num [tableK,currentK] at h₁ h₂ ⊢
  linarith only [h₁,h₂,hcost,herr]

end
end ImbalancedChen.Part5OriginalH430W1TrueConvertedBase
