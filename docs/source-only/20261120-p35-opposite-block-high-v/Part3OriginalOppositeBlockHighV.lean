import ImbalancedChen.Part3OriginalOppositeBlockTransport

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Eliminate the explicit 3/4 transport multiplier on both actual charts
in the restricted physical regime 2*S^2 <= 2^j. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeBlockHighV20261120
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalAllChartLossyPair20261119 (transportedPrice)
open OriginalOppositeBlockExceptionalBound20261120 (rawChartN)
open OriginalOppositeBlockTransport20261120
  (transportedChartJ transportedChartCost opposite_block_with_transported_exceptional)
open OriginalOppositeBlockSplit20261120 (blockCuspComplement blockContinuous)
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)

/-- Both physical Z scales are at least one, even for an empty chart. -/
theorem fixedZ_one_le (D : OriginalData) (upper : Bool) : 1 ≤ fixedZ D upper := by
  have hS : 1 ≤ scaleS D.key := scaleS_one_le D.key
  have hS2 : (1:ℝ) ≤ (scaleS D.key)^2 := by nlinarith only [hS]
  cases upper <;> simp only [fixedZ,Bool.false_eq_true,if_false,if_true] <;> linarith only [hS2]

theorem fixedZ_lower_le_upper (D : OriginalData) : fixedZ D false ≤ fixedZ D true := by
  simp only [fixedZ,Bool.false_eq_true,if_false,if_true]
  nlinarith only [sq_nonneg (scaleS D.key)]

/-- No transport loss when X is at most the positive baseline Q+m. -/
theorem transportedPrice_eq_initial (C ε Q m X : ℝ)
    (hden : 0 < Q+m) (hX : X ≤ Q+m) :
    transportedPrice C ε Q m X = C*((1+Q)*(1+m))^ε*(Q+m)*m := by
  have hr : X/(Q+m) ≤ 1 := (div_le_one hden).2 hX
  simp only [transportedPrice,max_eq_left hr,Real.one_rpow,one_mul]

/-- For Z <= V the original W is V; the two printed baseline ranges
cover W without a high-weight transport factor. -/
theorem highV_threshold_baselines (D : OriginalData) (upper : Bool) (j : ℕ)
    (hZV : fixedZ D upper ≤ (((2:ℕ)^j : ℕ):ℝ)) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
    threshold V Z = V ∧ threshold V Z ≤ Z/2 + classicalMScale j ∧
      threshold V Z ≤ Z + classicalMScale j := by
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  have hz : 1 ≤ Z := fixedZ_one_le D upper
  have hv : 0 < V := by dsimp [V]; positivity
  have hsq : Z^2 ≤ V^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hZV) (by linarith : 0 ≤ V+Z)
    nlinarith only [h]
  have hdiv : Z^2/V ≤ V := (div_le_iff₀ hv).2 (by nlinarith only [hsq])
  have hW : threshold V Z = V := max_eq_left hdiv
  have hm : classicalMScale j = V-1/2 := rfl
  refine ⟨hW, ?_, ?_⟩ <;> rw [hW,hm] <;> linarith only [hz]

def initialPrice (C ε Q m : ℝ) : ℝ := C*((1+Q)*(1+m))^ε*(Q+m)*m

def initialChartJ (C ε : ℝ) (D : OriginalData) (upper : Bool) (j : ℕ) : ℝ :=
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  (2+Real.log (4*V+1))^2 *
    ((initialPrice C ε (Z/2) (classicalMScale j) +
      initialPrice C ε Z (classicalMScale j))/4)

def initialChartCost (C ε : ℝ) (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (j : ℕ) (M B : ℝ) : ℝ :=
  (M^2*fixedZ D upper) * (B^2 * (initialChartJ C ε D upper j *
    rawChartN D r k upper))

/-- The loss-free price is exactly the prior transported price in this
regime, including the lower interval's endpoint correction. -/
theorem transportedChartCost_eq_initial (C ε : ℝ) (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (j : ℕ) (M B : ℝ) (hZV : fixedZ D upper ≤ (((2:ℕ)^j : ℕ):ℝ)) :
    transportedChartCost C ε D r k upper j M B = initialChartCost C ε D r k upper j M B := by
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  have hz : 1 ≤ Z := fixedZ_one_le D upper
  have hm : 0 < classicalMScale j := (by norm_num : (0:ℝ) < 1/2).trans_le
    (classicalMScale_bounds j).1
  obtain ⟨_,h₁,h₂⟩ := highV_threshold_baselines D upper j hZV
  have hd₁ : 0 < Z/2 + classicalMScale j := by linarith only [hz,hm]
  have hd₂ : 0 < Z + classicalMScale j := by linarith only [hz,hm]
  have hp₁ := transportedPrice_eq_initial C ε (Z/2) (classicalMScale j) W hd₁ h₁
  have hp₂ := transportedPrice_eq_initial C ε Z (classicalMScale j) W hd₂ h₂
  simp only [transportedChartCost,initialChartCost,transportedChartJ,initialChartJ,
    initialPrice,← hp₁,← hp₂]

/-- In the restricted high-V region, the actual opposite block uses the
initial prices on both charts. The actual nonexceptional and continuous
contributions, raw n cost and test budgets remain in the conclusion. -/
theorem opposite_block_highV_initial_price {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (k : BlockKey) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ),
      0 < N → D.block.atom.residue ≠ 0 →
      fixedZ D true ≤ (((2:ℕ)^j : ℕ):ℝ) →
      ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∃ B₁ : ℝ, 0 ≤ B₁ ∧
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
        traceNegative D k negativeM = true →
        ‖fullBlockMode D r k J j negativeM M N ell‖^2 ≤
          3 * (2 * ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
            (initialChartCost C ε D r k false j M B₀ +
              initialChartCost C ε D r k true j M B₁) +
            ‖blockCuspComplement D r k negativeM J j M N ell‖^2 +
            ‖blockContinuous D r k negativeM J j M N ell‖^2) := by
  obtain ⟨C,hC,hblock⟩ := opposite_block_with_transported_exceptional hε
  refine ⟨C,hC,?_⟩
  intro D k J j M N ell hN ha hupper
  have hlower : fixedZ D false ≤ (((2:ℕ)^j : ℕ):ℝ) :=
    (fixedZ_lower_le_upper D).trans hupper
  obtain ⟨B₀,hB₀,B₁,hB₁,h⟩ := hblock D k J j M N ell hN ha
  refine ⟨B₀,hB₀,B₁,hB₁,?_⟩
  intro r negativeM hs
  have hh := h r negativeM hs
  rw [transportedChartCost_eq_initial C ε D r k false j M B₀ hlower,
    transportedChartCost_eq_initial C ε D r k true j M B₁ hupper] at hh
  exact hh

end ImbalancedChen.Part3.OriginalOppositeBlockHighV20261120
end
