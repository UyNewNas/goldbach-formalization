import ImbalancedChen.P4ASixTentRange32Moments
import ImbalancedChen.P4ASixTentRange32OldWeight
import ImbalancedChen.P4AOriginalRange32MassCeil
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryEarlyReturnLeaf

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.
Complete ordinary six-tent low>=2 strict-chord consumer of the real original
range32 operations. H<=lo<hi<=R supplies logarithm domains and positive raw
divisors internally. Literal selector active/root/residual guards, exact
Fraction endpoints, same-reader queries, signed meanHigh, Mass32 and final
original UP are all joined without a query or whole-leaf bound premise.
The three sibling arithmetic suppliers are imported, not rewritten.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinarySixTentRange32Leaf
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdCompactPartitionSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdP4ASixTentRange32Moments OriginalThirdP4ASixTentRange32OldWeight
open P4AOriginalRange32MassCeil20261024zSourceOnly
open OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "T₀" => (481573208064:ℤ)

def sourceBranch32 (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) : Prop :=
  match k with
  | .rise => -50*sourceD+256*(literalTentX s*hi 0+literalTentY s*hi 1+literalTentZ s*hi 2)≤0
  | .fall => ¬(-50*sourceD+256*(literalTentX s*hi 0+literalTentY s*hi 1+literalTentZ s*hi 2)≤0) ∧
      0≤-50*sourceD+256*(literalTentX s*lo 0+literalTentY s*lo 1+literalTentZ s*lo 2)
def sourceRoot32 (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) : Prop :=
  match k with
  | .rise => sourceD+literalTentX s*hi 0+literalTentY s*hi 1+literalTentZ s*hi 2≤2*T₀
  | .fall => 57*sourceD-96*(literalTentX s*lo 0+literalTentY s*lo 1+literalTentZ s*lo 2)≤64*T₀
def sourceResidual32 (s : TentSum) (k : TentSide) (hi : Fin 3 → ℤ) : Prop :=
  match k with
  | .rise => 0<sourceD+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1
  | .fall => 0<57*sourceD+(-96*literalTentX s-64)*hi 0+(-96*literalTentY s-64)*hi 1

/-- The source b>q/d>q rejection tests always fail for these literal twelve
tuples. This is independent of the selected cell and is not an input gate. -/
theorem literal_coefficient_guards32 (s : TentSum) (k : TentSide) :
    (match k with
    | .rise => literalTentX s≤2 ∧ literalTentY s≤2
    | .fall => -96*literalTentX s≤64 ∧ -96*literalTentY s≤64) := by
  cases s <;> cases k <;> norm_num [literalTentX,literalTentY]

def savedLow32 (s : TentSum) (k : TentSide) (hi : Fin 3 → ℤ) : ℚ :=
  literalTentEndpoint s k hi sourceD
def savedHigh32 (s : TentSum) (k : TentSide) (lo : Fin 3 → ℤ) : ℚ :=
  literalTentEndpoint s k lo sourceD
def savedFl32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (hi : Fin 3 → ℤ) : ℤ :=
  readQueryLo160 (assembledRead table.blocks) (savedLow32 s k hi).num ((savedLow32 s k hi).den:ℤ)
def savedFh32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo : Fin 3 → ℤ) : ℤ :=
  readQueryLo160 (assembledRead table.blocks) (savedHigh32 s k lo).num ((savedHigh32 s k lo).den:ℤ)
def savedOut32 (table : CheckedBlockTable) (a b : Fin 3 → ℚ) : ℤ :=
  readQueryHi160 (assembledRead table.blocks) (ordinaryNew32 (realBox a) (realBox b)).hi P160
def ordinaryMeanHigh32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) : ℤ :=
  meanHigh
    (tentWeight32 s k (realBox a) (realBox b) (savedLow32 s k hi) (savedHigh32 s k lo)).lo
    (tentWeight32 s k (realBox a) (realBox b) (savedLow32 s k hi) (savedHigh32 s k lo)).hi
    (savedFl32 table s k hi) (savedFh32 table s k lo) (savedOut32 table a b)
def ordinaryCost32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) : ℤ :=
  up (ordinaryMeanHigh32 table s k lo hi a b*(ordinaryMass32 lo hi).hi) P160

/-- Literal saved-grid final mean integer. NEW and OLD/wt are the siblings'
proved original integer operation trees, rather than ideal real means. -/
def gridMeanHigh32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) : ℤ :=
  meanHigh
    (gridTentWeight32 s k lo hi (savedLow32 s k hi) (savedHigh32 s k lo)).lo
    (gridTentWeight32 s k lo hi (savedLow32 s k hi) (savedHigh32 s k lo)).hi
    (savedFl32 table s k hi) (savedFh32 table s k lo)
    (readQueryHi160 (assembledRead table.blocks) (gridNew32 lo hi).hi P160)

theorem ordinaryMeanHigh32_grid_abi
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i) :
    ordinaryMeanHigh32 table s k lo hi a b=gridMeanHigh32 table s k lo hi := by
  unfold ordinaryMeanHigh32 gridMeanHigh32 savedOut32
  rw [tentWeight32_grid_abi s k lo hi a b (savedLow32 s k hi) (savedHigh32 s k lo)
    haBind hbBind hH hwidth,ordinaryNew32_grid_abi lo hi a b haBind hbBind hH hwidth]

theorem ordinaryCost32_grid_abi
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i) :
    ordinaryCost32 table s k lo hi a b=
      up (gridMeanHigh32 table s k lo hi*(ordinaryMass32 lo hi).hi) P160 := by
  unfold ordinaryCost32
  rw [ordinaryMeanHigh32_grid_abi table s k lo hi a b haBind hbBind hH hwidth]

theorem real_grid_binding32 (v : Fin 3 → ℤ) (p : Fin 3 → ℚ)
    (hp : ∀ i,p i=(v i:ℚ)/(sourceD:ℚ)) (i : Fin 3) :
    realBox p i=(v i:ℝ)/(sourceD:ℝ) := by
  dsimp only [realBox]
  rw [hp i]
  simp only [Rat.cast_div,Rat.cast_intCast]

/-- Only the primitive raw integer geometry of the actual ordinary full
box is transported here. Positivity/width comes from the sibling grid API. -/
theorem ordinary_grid_geometry32
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i)
    (hxy : hi 1≤lo 0) (hzy : hi 2≤lo 1)
    (hmu : 128*hi 0≤25*sourceD) (hfull : hi 0+hi 1+3*hi 2≤T₀) :
    (∀ i,0<realBox a i) ∧ (∀ i,realBox a i<realBox b i) ∧
    (1:ℝ)/100≤realBox a 2 ∧ realBox b 1≤realBox a 0 ∧
    realBox b 2≤realBox a 1 ∧ realBox b 0≤VariableEnvelope.mu ∧
    realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta := by
  have hg := stored_global_geometry lo hi a b haBind hbBind hH hwidth
  have hal := real_grid_binding32 lo a haBind
  have hbu := real_grid_binding32 hi b hbBind
  have hD : (0:ℝ)<(sourceD:ℝ) := by norm_num [sourceD]
  refine ⟨hg.1,hg.2,?_,?_,?_,?_,?_⟩
  · rw [hal 2,←original_grid_cutoffs_exact.1]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hH 2) hD.le
  · rw [hbu 1,hal 0]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hxy) hD.le
  · rw [hbu 2,hal 1]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hzy) hD.le
  · rw [hbu 0]
    apply (div_le_iff₀ hD).2
    have hm : (128:ℝ)*(hi 0:ℝ)≤25*(sourceD:ℝ) := by exact_mod_cast hmu
    dsimp [VariableEnvelope.mu]
    linarith only [hm]
  · calc
      realBox b 0+realBox b 1+3*realBox b 2=
          ((hi 0:ℝ)+(hi 1:ℝ)+3*(hi 2:ℝ))/(sourceD:ℝ) := by
        rw [hbu 0,hbu 1,hbu 2]
        ring
      _≤(T₀:ℝ)/(sourceD:ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hfull) hD.le
      _=thirdPrefixTheta := by norm_num [sourceD,thirdPrefixTheta]

theorem stored_ratios32 (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i) (hR : ∀ i,hi i≤sourceR) :
    ∀ i,realBox b i/realBox a i≤32 := by
  intro i
  have hlo : 0<lo i := lt_of_lt_of_le (by norm_num [sourceH]) (hH i)
  change (b i:ℝ)/(a i:ℝ)≤32
  rw [grid_ratio_eq _ _ _ _ (haBind i) (hbBind i) hlo.ne']
  exact (global_ratio32 _ _ (hH i) (hwidth i) (hR i)).2

/-- Canonical OLD Fractions and the unreduced NEW (new.hi,P160) are queried
on ONE reader. No compact-domain or endpoint-order query gate remains. -/
theorem ordinary_three_queries32 (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) :
    value (savedFl32 table s k hi)≤actualExtendedThirdLowerFactor (savedLow32 s k hi:ℝ) ∧
    value (savedFh32 table s k lo)≤actualExtendedThirdLowerFactor (savedHigh32 s k lo:ℝ) ∧
    actualExtendedThirdLowerFactor (ordinaryNewQuery32 (realBox a) (realBox b):ℝ)≤
      value (savedOut32 table a b) := by
  have hl := (CheckedBlockTable.rational_query_encloses_all table (savedLow32 s k hi)).1
  have hh := (CheckedBlockTable.rational_query_encloses_all table (savedHigh32 s k lo)).1
  have hn := (CheckedBlockTable.query_encloses_all table
    (ordinaryNew32 (realBox a) (realBox b)).hi P160 P160_pos).2
  refine ⟨?_,?_,?_⟩
  · simpa only [savedFl32,value,P160,Int.cast_pow,Int.cast_ofNat] using hl
  · simpa only [savedFh32,value,P160,Int.cast_pow,Int.cast_ofNat] using hh
  · simpa only [savedOut32,ordinaryNewQuery32,Rat.cast_div,Rat.cast_intCast,value,
      P160,Int.cast_pow,Int.cast_ofNat] using hn

/-- The actual ordinary selected-plane leaf and its exact source strict
tail, before mass/UP. Every analytic, arithmetic and reader supply is invoked
internally; all remaining inputs are original integer geometry/source tests. -/
theorem ordinary_tent_range32_mean_upper
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i) (hR : ∀ i,hi i≤sourceR)
    (hxy : hi 1≤lo 0) (hzy : hi 2≤lo 1)
    (hmu : 128*hi 0≤25*sourceD) (hfull : hi 0+hi 1+3*hi 2≤T₀)
    (hbranch : sourceBranch32 s k lo hi) (hroot : sourceRoot32 s k lo hi)
    (hres : sourceResidual32 s k hi) (hlow : (2:ℚ)≤savedLow32 s k hi) :
    originalMeanUpperTail (savedLow32 s k hi) (savedHigh32 s k lo)
      (tentWeight32 s k (realBox a) (realBox b) (savedLow32 s k hi) (savedHigh32 s k lo)).lo
      (tentWeight32 s k (realBox a) (realBox b) (savedLow32 s k hi) (savedHigh32 s k lo)).hi
      (savedFl32 table s k hi) (savedFh32 table s k lo) (savedOut32 table a b)=
        some (ordinaryMeanHigh32 table s k lo hi a b) ∧
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*value (ordinaryMeanHigh32 table s k lo hi a b) := by
  obtain ⟨ha,hab,hcut,hyx,hzyR,hmuR,hfullR⟩ :=
    ordinary_grid_geometry32 lo hi a b haBind hbBind hH hwidth hxy hzy hmu hfull
  have hal := real_grid_binding32 lo a haBind
  have hbu := real_grid_binding32 hi b hbBind
  have hg := original_selected_tent_guard_bridge s k lo hi sourceD T₀
    (realBox a) (realBox b) rfl rfl hal hbu
    (by simpa only [sourceBranch32] using hbranch)
    (by simpa only [sourceRoot32] using hroot)
    (by simpa only [sourceResidual32] using hres)
  have hcoef := literal_coefficient_guards32 s k
  have hD : (sourceD:ℝ)≠0 := by norm_num [sourceD]
  have hlo : 0<lo 2 := lt_of_lt_of_le (by norm_num [sourceH]) (hH 2)
  have hhi : 0<hi 2 := hlo.trans (hwidth 2)
  have hloR : (lo 2:ℝ)≠0 := by exact_mod_cast hlo.ne'
  have hhiR : (hi 2:ℝ)≠0 := by exact_mod_cast hhi.ne'
  have lowCast : (savedLow32 s k hi:ℝ)=tentOldLow s k (realBox b) :=
    literalTentEndpoint_cast s k hi sourceD (realBox b) hD hhiR hbu
  have highCast : (savedHigh32 s k lo:ℝ)=tentOldHigh s k (realBox a) :=
    literalTentEndpoint_cast s k lo sourceD (realBox a) hD hloR hal
  have hspan := original_tent_old_span s k (realBox a) (realBox b) ha hab hg.2.2
  have hspanQ : savedLow32 s k hi<savedHigh32 s k lo := by
    have hr : (savedLow32 s k hi:ℝ)<(savedHigh32 s k lo:ℝ) := by
      simpa only [lowCast,highCast] using hspan
    exact_mod_cast hr
  have hdispatch := strict_chord_tail (savedLow32 s k hi) (savedHigh32 s k lo)
    (tentWeight32 s k (realBox a) (realBox b) (savedLow32 s k hi) (savedHigh32 s k lo)).lo
    (tentWeight32 s k (realBox a) (realBox b) (savedLow32 s k hi) (savedHigh32 s k lo)).hi
    (savedFl32 table s k hi) (savedFh32 table s k lo) (savedOut32 table a b) hlow hspanQ
  refine ⟨hdispatch,?_⟩
  obtain ⟨hfl,hfh,hquery⟩ := ordinary_three_queries32 table s k lo hi a b
  have hm := (stored_global_moments_new lo hi a b haBind hbBind hH hwidth hR).2.2.2
  rw [ordinary_new_probability_mean (realBox a) (realBox b) ha hab] at hm
  have hmean :
      (thirdPrefixTheta-boxEX (realBox a) (realBox b)-boxEY (realBox a) (realBox b))*
        boxEZInv (realBox a) (realBox b)-1≤
      (ordinaryNewQuery32 (realBox a) (realBox b):ℝ) := by
    simpa only [ordinaryNewQuery32,Rat.cast_div,Rat.cast_intCast,value] using hm.2
  have hout := actual_new_mean_upper_of_query (realBox a) (realBox b) _ _ hmean hquery
  have hloFactor : (2:ℝ)≤tentOldLow s k (realBox b) := by
    have hr : (2:ℝ)≤(savedLow32 s k hi:ℝ) := by exact_mod_cast hlow
    simpa only [lowCast] using hr
  have hrho : realBox b 0≤thirdPrefixRho := hmuR.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hleaf := ordinary_full_leaf_old_chord_upper (realBox a) (realBox b) ha hab
    hcut hyx hzyR hrho hfullR (planeConst k) (oldX s k) (oldY s k) (oldZ s k)
    (tentOldLow s k (realBox b)) (tentOldHigh s k (realBox a))
    (value (savedFl32 table s k hi)) (value (savedFh32 table s k lo))
    (value (savedOut32 table a b)) hloFactor hspan
    (fun t ht => original_tent_old_range s k (realBox a) (realBox b) ha hg.2.2 ht)
    (fun t ht => original_tent_old_minorant s k (realBox a) (realBox b)
      ha hyx hzyR hmuR hg.1 hg.2.1 ht)
    (by simpa only [lowCast] using hfl) (by simpa only [highCast] using hfh) hout
  have hround := stored_global_tentMeanHigh32_sound s k lo hi a b
    (savedLow32 s k hi) (savedHigh32 s k lo)
    (savedFl32 table s k hi) (savedFh32 table s k lo) (savedOut32 table a b)
    haBind hbBind hH hwidth hR ha hab hg.2.2 lowCast highCast
  have hround' : max 0 (value (savedOut32 table a b)-oldChordMean (realBox a) (realBox b)
      (planeConst k) (oldX s k) (oldY s k) (oldZ s k)
      (tentOldLow s k (realBox b)) (tentOldHigh s k (realBox a))
      (value (savedFl32 table s k hi)) (value (savedFh32 table s k lo)))≤
      value (ordinaryMeanHigh32 table s k lo hi a b) := by
    simpa only [ordinaryMeanHigh32,oldChordMean,oldAffineMean,tentOldChord,tentOldMean] using hround
  exact hleaf.trans (mul_le_mul_of_nonneg_left hround'
    (mul_nonneg (by norm_num) (boxMass_pos (realBox a) (realBox b) ha hab).le))

/-- Final true original ordinary six-tent range32 integer leaf charge.
There is no unit-ratio<=2, log-positive, hquery, mean, weight or leaf-bound
premise. The SAME range32 meanHigh is multiplied by the literal Mass32.hi
and rounded by the one original UP, preserving P160 and factor4. -/
theorem ordinary_tent_range32_integer_upper
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i) (hR : ∀ i,hi i≤sourceR)
    (hxy : hi 1≤lo 0) (hzy : hi 2≤lo 1)
    (hmu : 128*hi 0≤25*sourceD) (hfull : hi 0+hi 1+3*hi 2≤T₀)
    (hbranch : sourceBranch32 s k lo hi) (hroot : sourceRoot32 s k lo hi)
    (hres : sourceResidual32 s k hi) (hlow : (2:ℚ)≤savedLow32 s k hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (ordinaryCost32 table s k lo hi a b) := by
  have hleaf := (ordinary_tent_range32_mean_upper table s k lo hi a b
    haBind hbBind hH hwidth hR hxy hzy hmu hfull hbranch hroot hres hlow).2
  have hg := stored_global_geometry lo hi a b haBind hbBind hH hwidth
  have hr := stored_ratios32 lo hi a b haBind hbBind hH hwidth hR
  have hm := (ordinary_stored_mass32_encloses lo hi a b haBind hbBind hg.1 hg.2
    (hr 0) (hr 1)).2
  have hh : 0≤value (ordinaryMeanHigh32 table s k lo hi a b) := by
    rw [ordinaryMeanHigh32,meanHigh,value_max,value_zero]
    exact le_max_left _ _
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (ordinaryMeanHigh32 table s k lo hi a b) := hleaf
    _≤value (ordinaryMass32 lo hi).hi*value (ordinaryMeanHigh32 table s k lo hi a b) :=
      mul_le_mul_of_nonneg_right hm hh
    _=value (ordinaryMeanHigh32 table s k lo hi a b)*value (ordinaryMass32 lo hi).hi := by ring
    _≤value (ordinaryCost32 table s k lo hi a b) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

end
end ImbalancedChen.OriginalThirdP4AOrdinarySixTentRange32Leaf
