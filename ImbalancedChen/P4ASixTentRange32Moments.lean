import ImbalancedChen.ActualThirdOriginalBelowMuBRounded
import ImbalancedChen.ActualThirdOriginalPositive256LogRange32IntegerGuard
import ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf

/-!
SOURCEONLY / UNCOMPILED. Additive range32 operands for all six tents.
The ex, ey, invz and NEW operations are independent of the selected tent.
They reuse the B operation tree with originalLn32 in both divisors.
The unit branch is not substituted for the full range-reduced logarithm.
The original global grid bounds are H=480*2^24, R=9500*2^24, D=48000*2^24.
No positive-log output, semantic mean or ratio<=2 is a final caller premise.
The imported B-rounded and range32 modules denote their frozen source drafts.
-/

namespace ImbalancedChen.OriginalThirdP4ASixTentRange32Moments

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdSymmetricJensenSourceOnly

def ordinaryLog32 (a b : BoxPoint) (i : Fin 3) : IV := originalLn32 (b i/a i)
def ordinaryEx32 (a b : BoxPoint) : IV := ex a b (ordinaryLog32 a b 0)
def ordinaryEy32 (a b : BoxPoint) : IV := ey a b (ordinaryLog32 a b 1)
def ordinaryInvZ32 (a b : BoxPoint) : IV := ofReal (boxEZInv a b)
def ordinaryNew32 (a b : BoxPoint) : IV :=
  roundedNew a b (ordinaryLog32 a b 0) (ordinaryLog32 a b 1)
def ordinaryNewQuery32 (a b : BoxPoint) : ℚ := ((ordinaryNew32 a b).hi:ℚ)/(P160:ℚ)

theorem ordinary_source_tree_abi (a b : BoxPoint) :
    ordinaryNew32 a b =
      sub (mul (sub (sub (ofReal thirdPrefixTheta) (ordinaryEx32 a b))
        (ordinaryEy32 a b)) (ordinaryInvZ32 a b)) (ofReal 1) := by rfl

theorem ordinaryEx32_encloses {a b : BoxPoint}
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) :
    Encloses (ordinaryEx32 a b) (boxEX a b) := by
  exact divide_sound (ofReal_sound (b 0-a 0)) hlx hpx

theorem ordinaryEy32_encloses {a b : BoxPoint}
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpy : 0<(ordinaryLog32 a b 1).lo) :
    Encloses (ordinaryEy32 a b) (boxEY a b) := by
  exact divide_sound (ofReal_sound (b 1-a 1)) hly hpy

theorem ordinaryInvZ32_encloses (a b : BoxPoint) :
    Encloses (ordinaryInvZ32 a b) (boxEZInv a b) := by
  exact ofReal_sound _

theorem ordinaryNew32_encloses {a b : BoxPoint}
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) (hpy : 0<(ordinaryLog32 a b 1).lo) :
    Encloses (ordinaryNew32 a b)
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1) := by
  exact roundedNew_encloses hlx hly hpx hpy

theorem ordinaryLog32_sound {a b : BoxPoint} (i : Fin 3)
    (hratio : b i/a i∈Icc (1:ℝ) 32) :
    Encloses (ordinaryLog32 a b i) (Real.log (b i/a i)) := by
  exact originalLn32_sound hratio.1 hratio.2

/-- The three enclosures are of the actual normalized box expectations. -/
theorem moment_enclosures {a b : BoxPoint}
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i)
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) (hpy : 0<(ordinaryLog32 a b 1).lo) :
    Encloses (ordinaryEx32 a b) (∫ t, t 0 ∂boxProbability a b) ∧
    Encloses (ordinaryEy32 a b) (∫ t, t 1 ∂boxProbability a b) ∧
    Encloses (ordinaryInvZ32 a b) (∫ t, 1/t 2 ∂boxProbability a b) := by
  have hm := boxProbability_moments a b ha hab
  rw [hm.1,hm.2.1,hm.2.2.1]
  exact ⟨ordinaryEx32_encloses hlx hpx,ordinaryEy32_encloses hly hpy,
    ordinaryInvZ32_encloses a b⟩

theorem ordinary_new_probability_mean (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) :
    (∫ t, (thirdPrefixTheta-t 0-t 1)/t 2-1 ∂boxProbability a b)=
      (thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1 := by
  have heq : (fun t : BoxPoint => (thirdPrefixTheta-t 0-t 1)/t 2-1)=
      affineArgument thirdPrefixTheta (-1) (-1) (-1) := by
    funext t
    simp only [affineArgument]
    ring
  rw [heq,boxProbability_affine_mean a b ha hab]
  ring

theorem ordinaryNew32_encloses_probability_mean {a b : BoxPoint}
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i)
    (hlx : Encloses (ordinaryLog32 a b 0) (Real.log (b 0/a 0)))
    (hly : Encloses (ordinaryLog32 a b 1) (Real.log (b 1/a 1)))
    (hpx : 0<(ordinaryLog32 a b 0).lo) (hpy : 0<(ordinaryLog32 a b 1).lo) :
    Encloses (ordinaryNew32 a b)
      (∫ t, (thirdPrefixTheta-t 0-t 1)/t 2-1 ∂boxProbability a b) := by
  rw [ordinary_new_probability_mean a b ha hab]
  exact ordinaryNew32_encloses hlx hly hpx hpy

theorem symmetric_scalar_new_mean_eq (a b c d : ℝ) :
    (thirdPrefixTheta-boxEX (![a,a,c]) (![b,b,d])-boxEY (![a,a,c]) (![b,b,d]))*
        boxEZInv (![a,a,c]) (![b,b,d])-1 = newMean a b c d := by
  simp only [boxEX,boxEY,boxEZInv,newMean,sumMean,invZMean,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  ring

theorem ordinaryNew32_symmetric_encloses {a b c d : ℝ}
    (hlx : Encloses (ordinaryLog32 (![a,a,c]) (![b,b,d]) 0) (Real.log (b/a)))
    (hly : Encloses (ordinaryLog32 (![a,a,c]) (![b,b,d]) 1) (Real.log (b/a)))
    (hpx : 0<(ordinaryLog32 (![a,a,c]) (![b,b,d]) 0).lo)
    (hpy : 0<(ordinaryLog32 (![a,a,c]) (![b,b,d]) 1).lo) :
    Encloses (ordinaryNew32 (![a,a,c]) (![b,b,d])) (newMean a b c d) := by
  rw [←symmetric_scalar_new_mean_eq]
  exact ordinaryNew32_encloses hlx hly hpx hpy

def sourceD : ℤ := 48000*2^24
def sourceH : ℤ := 480*2^24
def sourceR : ℤ := 9500*2^24

theorem original_grid_cutoffs_exact :
    (sourceH:ℝ)/(sourceD:ℝ)=(1:ℝ)/100 ∧
      (sourceR:ℝ)/(sourceD:ℝ)=thirdPrefixRho := by
  norm_num [sourceH,sourceR,sourceD,thirdPrefixRho]

theorem global_ratio32 (u v : ℤ) (hH : sourceH≤u) (huv : u<v) (hR : v≤sourceR) :
    (v:ℝ)/(u:ℝ)∈Icc (1:ℝ) 32 := by
  have hu : 0<u := lt_of_lt_of_le (by norm_num [sourceH]) hH
  have huR : (0:ℝ)<(u:ℝ) := by exact_mod_cast hu
  have hlow : (u:ℝ)≤(v:ℝ) := by exact_mod_cast huv.le
  have hcross : v≤32*u := by
    have hc : sourceR≤32*sourceH := by norm_num [sourceR,sourceH]
    linarith
  have hcrossR : (v:ℝ)≤32*(u:ℝ) := by exact_mod_cast hcross
  exact ⟨(le_div_iff₀ huR).2 (by simpa only [one_mul] using hlow),
    (div_le_iff₀ huR).2 hcrossR⟩

/-- Public below-mu single-ratio wrapper, usable on a symmetric square too. -/
theorem symmetric_source_log32_guard (x0 x1 : ℤ) (a b : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hapos : (0:ℝ)<(a:ℝ)) (hwidth : (a:ℝ)<(b:ℝ))
    (hmu : (b:ℝ)≤(25:ℝ)/128) (h32 : (b:ℝ)/(a:ℝ)≤32) :
    0<(originalLn32 ((b:ℝ)/(a:ℝ))).lo := by
  exact original_stored_below_mu_log32_guard x0 x1 a b ha hb hapos hwidth hmu h32

private theorem unit_log_lo_nonneg {x : ℝ} (h1 : 1≤x) (h2 : x≤2) :
    0≤(unitLog x 256).lo := by
  have hz := (rounded_z_upper h1 h2).1
  have hfloor : 0≤(ofReal (1-1/x)).lo :=
    Int.floor_nonneg.mpr (mul_nonneg hz P160_real_pos.le)
  have hfirst := originalLnUnit_lo_ge_first h1 h2
  rw [originalLnUnit_eq] at hfirst
  exact hfloor.trans hfirst

private theorem log_two_multiple_lo_pos (k : ℕ) (hk : 0<k) :
    0<(mul (unitLog 2 256) (ofReal (k:ℝ))).lo := by
  have hfirst := originalLnUnit_lo_ge_first (x:=2) (by norm_num : (1:ℝ)≤2) le_rfl
  rw [originalLnUnit_eq] at hfirst
  have hfloor : (1:ℤ)≤(ofReal (1-1/(2:ℝ))).lo := by
    change (1:ℤ)≤⌊(1-1/(2:ℝ))*(P160:ℝ)⌋
    apply Int.le_floor.mpr
    norm_num [P160]
  have hlo : (1:ℤ)≤(unitLog 2 256).lo := hfloor.trans hfirst
  have hlog := unitLog_sound (by norm_num : (1:ℝ)≤2) le_rfl 256
  have hhi : (1:ℤ)≤(unitLog 2 256).hi := hlo.trans (value_le_iff.mp (hlog.1.trans hlog.2))
  have hkReal : (1:ℝ)≤(k:ℝ) := by exact_mod_cast (show 1≤k by omega)
  have hklo : P160≤(ofReal (k:ℝ)).lo := by
    change P160≤⌊(k:ℝ)*(P160:ℝ)⌋
    apply Int.le_floor.mpr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hkReal P160_real_pos.le
  have hkhi : P160≤(ofReal (k:ℝ)).hi := hklo.trans
    (value_le_iff.mp ((ofReal_sound (k:ℝ)).1.trans (ofReal_sound (k:ℝ)).2))
  have hprod (a b : ℤ) (ha : 1≤a) (hb : P160≤b) : P160≤a*b := by
    simpa only [one_mul] using mul_le_mul ha hb P160_pos.le ((by norm_num : (0:ℤ)≤1).trans ha)
  have hfour : P160≤fourLo (unitLog 2 256) (ofReal (k:ℝ)) :=
    le_min (le_min (hprod _ _ hlo hklo) (hprod _ _ hlo hkhi))
      (le_min (hprod _ _ hhi hklo) (hprod _ _ hhi hkhi))
  have hdiv : (1:ℤ)≤fourLo (unitLog 2 256) (ofReal (k:ℝ))/P160 :=
    (Int.le_ediv_iff_mul_le P160_pos).mpr (by simpa only [one_mul] using hfour)
  change 0<fourLo (unitLog 2 256) (ofReal (k:ℝ))/P160
  omega

private theorem positive_branch_lo_pos {x : ℝ} (h1 : 1≤x) (h2 : x≤2)
    (k : ℕ) (hk : 0<k) : 0<(originalLogBranch x k).lo := by
  have hn := unit_log_lo_nonneg h1 h2
  have hp := log_two_multiple_lo_pos k hk
  change 0<(unitLog x 256).lo+(mul (unitLog 2 256) (ofReal (k:ℝ))).lo
  omega

private theorem log32_gt_two_lo_pos {x : ℝ} (hx : 2<x) (h32 : x≤32) :
    0<(originalLn32 x).lo := by
  rw [originalLn32,if_neg (not_le.mpr hx)]
  by_cases h2 : x/2≤2
  · rw [if_pos h2]
    exact positive_branch_lo_pos ((le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
      (by simpa using hx.le)) h2 1 (by norm_num)
  · rw [if_neg h2]
    by_cases h4 : x/(2:ℝ)^2≤2
    · rw [if_pos h4]
      refine positive_branch_lo_pos ?_ h4 2 (by norm_num)
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^2)).2
      have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).1 (lt_of_not_ge h2)
      norm_num at h ⊢
      exact h.le
    · rw [if_neg h4]
      by_cases h8 : x/(2:ℝ)^3≤2
      · rw [if_pos h8]
        refine positive_branch_lo_pos ?_ h8 3 (by norm_num)
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^3)).2
        have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^2)).1 (lt_of_not_ge h4)
        norm_num at h ⊢
        exact h.le
      · rw [if_neg h8]
        refine positive_branch_lo_pos ?_ ?_ 4 (by norm_num)
        · apply (le_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^4)).2
          have h := (lt_div_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^3)).1 (lt_of_not_ge h8)
          norm_num at h ⊢
          exact h.le
        · apply (div_le_iff₀ (by norm_num : (0:ℝ)<(2:ℝ)^4)).2
          simpa only [show 2*(2:ℝ)^4=32 by norm_num] using h32

/-- Original global integer bounds replace the narrower mu-bound in the
unit first-term proof. Positive range-reduction counts retain rounded ln2. -/
theorem integer_global_log32_guard (u v : ℤ)
    (hH : sourceH≤u) (huv : u<v) (hR : v≤sourceR) :
    0<(originalLn32 ((v:ℝ)/(u:ℝ))).lo := by
  have hr := global_ratio32 u v hH huv hR
  have hu : (0:ℝ)<(u:ℝ) := by exact_mod_cast
    (lt_of_lt_of_le (by norm_num [sourceH] : (0:ℤ)<sourceH) hH)
  have huvR : (u:ℝ)<(v:ℝ) := by exact_mod_cast huv
  have hv : (0:ℝ)<(v:ℝ) := hu.trans huvR
  by_cases h2 : (v:ℝ)/(u:ℝ)≤2
  · have hgap : (1:ℤ)≤v-u := by omega
    have hvP : v≤P160 := hR.trans (by norm_num [sourceR,P160])
    have hscaled : v≤(v-u)*P160 := hvP.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap P160_pos.le)
    have hscaledR : (v:ℝ)≤((v:ℝ)-(u:ℝ))*(P160:ℝ) := by exact_mod_cast hscaled
    have hfirstR : (1:ℝ)≤(1-1/((v:ℝ)/(u:ℝ)))*(P160:ℝ) := by
      calc
        (1:ℝ)≤((v:ℝ)-(u:ℝ))*(P160:ℝ)/(v:ℝ) :=
          (le_div_iff₀ hv).2 (by simpa only [one_mul] using hscaledR)
        _=(1-1/((v:ℝ)/(u:ℝ)))*(P160:ℝ) := by field_simp [hu.ne',hv.ne'] <;> ring
    have hfloor : (1:ℤ)≤(ofReal (1-1/((v:ℝ)/(u:ℝ)))).lo := Int.le_floor.mpr hfirstR
    have hlo := hfloor.trans (originalLnUnit_lo_ge_first hr.1 h2)
    rw [originalLn32,if_pos h2]
    change 0<(originalLnUnit ((v:ℝ)/(u:ℝ))).lo
    omega
  · exact log32_gt_two_lo_pos (lt_of_not_ge h2) hr.2

theorem grid_ratio_eq (u v : ℤ) (a b : ℚ)
    (ha : a=(u:ℚ)/(sourceD:ℚ)) (hb : b=(v:ℚ)/(sourceD:ℚ)) (hu : u≠0) :
    (b:ℝ)/(a:ℝ)=(v:ℝ)/(u:ℝ) := by
  have hD : (sourceD:ℝ)≠0 := by norm_num [sourceD]
  have huR : (u:ℝ)≠0 := by exact_mod_cast hu
  rw [ha,hb]
  simp only [Rat.cast_div,Rat.cast_intCast]
  field_simp [hD,huR]

theorem stored_global_log32_guards (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀i,sourceH≤lower i) (hwidth : ∀i,lower i<upper i)
    (hR : ∀i,upper i≤sourceR) :
    0<(ordinaryLog32 (realBox a) (realBox b) 0).lo ∧
      0<(ordinaryLog32 (realBox a) (realBox b) 1).lo := by
  have hguard (i : Fin 3) : 0<(ordinaryLog32 (realBox a) (realBox b) i).lo := by
    have hl : 0<lower i := lt_of_lt_of_le (by norm_num [sourceH]) (hH i)
    change 0<(originalLn32 ((b i:ℝ)/(a i:ℝ))).lo
    rw [grid_ratio_eq _ _ _ _ (haBind i) (hbBind i) hl.ne']
    exact integer_global_log32_guard _ _ (hH i) (hwidth i) (hR i)
  exact ⟨hguard 0,hguard 1⟩

theorem stored_global_log32_sound (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀i,sourceH≤lower i) (hwidth : ∀i,lower i<upper i)
    (hR : ∀i,upper i≤sourceR) :
    ∀i,Encloses (ordinaryLog32 (realBox a) (realBox b) i) (Real.log ((b i:ℝ)/(a i:ℝ))) := by
  intro i
  have hl : 0<lower i := lt_of_lt_of_le (by norm_num [sourceH]) (hH i)
  apply ordinaryLog32_sound i
  change (b i:ℝ)/(a i:ℝ)∈Icc (1:ℝ) 32
  rw [grid_ratio_eq _ _ _ _ (haBind i) (hbBind i) hl.ne']
  exact global_ratio32 _ _ (hH i) (hwidth i) (hR i)

theorem stored_global_geometry (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀i,sourceH≤lower i) (hwidth : ∀i,lower i<upper i) :
    (∀i,0<realBox a i) ∧ (∀i,realBox a i<realBox b i) := by
  have hD : (0:ℝ)<(sourceD:ℝ) := by norm_num [sourceD]
  constructor
  · intro i
    have hl : 0<lower i := lt_of_lt_of_le (by norm_num [sourceH]) (hH i)
    have hlR : (0:ℝ)<(lower i:ℝ) := by exact_mod_cast hl
    change (0:ℝ)<(a i:ℝ)
    rw [haBind i]
    simpa only [Rat.cast_div,Rat.cast_intCast] using div_pos hlR hD
  · intro i
    have hw : (lower i:ℝ)<(upper i:ℝ) := by exact_mod_cast hwidth i
    change (a i:ℝ)<(b i:ℝ)
    rw [haBind i,hbBind i]
    simpa only [Rat.cast_div,Rat.cast_intCast] using
      (div_lt_div_iff_of_pos_right hD).2 hw

/-- Final source-grid supplier: actual moments and NEW expectation, with
all logarithm, integer-divisor and probability inputs supplied internally. -/
theorem stored_global_moments_new (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀i,sourceH≤lower i) (hwidth : ∀i,lower i<upper i)
    (hR : ∀i,upper i≤sourceR) :
    Encloses (ordinaryEx32 (realBox a) (realBox b))
      (∫ t, t 0 ∂boxProbability (realBox a) (realBox b)) ∧
    Encloses (ordinaryEy32 (realBox a) (realBox b))
      (∫ t, t 1 ∂boxProbability (realBox a) (realBox b)) ∧
    Encloses (ordinaryInvZ32 (realBox a) (realBox b))
      (∫ t, 1/t 2 ∂boxProbability (realBox a) (realBox b)) ∧
    Encloses (ordinaryNew32 (realBox a) (realBox b))
      (∫ t, (thirdPrefixTheta-t 0-t 1)/t 2-1 ∂boxProbability (realBox a) (realBox b)) := by
  have hg := stored_global_geometry lower upper a b haBind hbBind hH hwidth
  have hl := stored_global_log32_sound lower upper a b haBind hbBind hH hwidth hR
  have hp := stored_global_log32_guards lower upper a b haBind hbBind hH hwidth hR
  have hm := moment_enclosures hg.1 hg.2 (hl 0) (hl 1) hp.1 hp.2
  exact ⟨hm.1,hm.2.1,hm.2.2,
    ordinaryNew32_encloses_probability_mean hg.1 hg.2 (hl 0) (hl 1) hp.1 hp.2⟩

def gridWidth32 (u v : ℤ) : IV :=
  ⟨(v-u)*P160/sourceD,up ((v-u)*P160) sourceD⟩
def gridCoordinateEx32 (lower upper : Fin 3 → ℤ) (i : Fin 3) : IV :=
  divide (gridWidth32 (lower i) (upper i))
    (originalLn32 ((upper i:ℝ)/(lower i:ℝ)))
def gridInvZ32 (lower upper : Fin 3 → ℤ) : IV :=
  ⟨(sourceD*(lower 2+upper 2))*P160/(2*lower 2*upper 2),
    up ((sourceD*(lower 2+upper 2))*P160) (2*lower 2*upper 2)⟩
def gridNew32 (lower upper : Fin 3 → ℤ) : IV :=
  sub (mul (sub (sub (ofReal thirdPrefixTheta) (gridCoordinateEx32 lower upper 0))
    (gridCoordinateEx32 lower upper 1)) (gridInvZ32 lower upper)) (ofReal 1)

theorem grid_width_cast (u v : ℤ) (a b : ℚ)
    (ha : a=(u:ℚ)/(sourceD:ℚ)) (hb : b=(v:ℚ)/(sourceD:ℚ)) :
    (b:ℝ)-(a:ℝ)=((v-u:ℤ):ℝ)/(sourceD:ℝ) := by
  rw [ha,hb]
  simp only [Rat.cast_div,Rat.cast_intCast,Int.cast_sub]
  ring

theorem ordinaryEx32_grid_abi (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ)) (hl : lower 0≠0) :
    ordinaryEx32 (realBox a) (realBox b)=gridCoordinateEx32 lower upper 0 := by
  change divide (ofReal ((b 0:ℝ)-(a 0:ℝ))) (originalLn32 ((b 0:ℝ)/(a 0:ℝ)))=
    divide (gridWidth32 (lower 0) (upper 0)) (originalLn32 ((upper 0:ℝ)/(lower 0:ℝ)))
  rw [grid_width_cast _ _ _ _ (haBind 0) (hbBind 0),
    grid_ratio_eq _ _ _ _ (haBind 0) (hbBind 0) hl,
    ofReal_int_div_source (upper 0-lower 0) sourceD (by norm_num [sourceD])] <;> rfl

theorem ordinaryEy32_grid_abi (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ)) (hl : lower 1≠0) :
    ordinaryEy32 (realBox a) (realBox b)=gridCoordinateEx32 lower upper 1 := by
  change divide (ofReal ((b 1:ℝ)-(a 1:ℝ))) (originalLn32 ((b 1:ℝ)/(a 1:ℝ)))=
    divide (gridWidth32 (lower 1) (upper 1)) (originalLn32 ((upper 1:ℝ)/(lower 1:ℝ)))
  rw [grid_width_cast _ _ _ _ (haBind 1) (hbBind 1),
    grid_ratio_eq _ _ _ _ (haBind 1) (hbBind 1) hl,
    ofReal_int_div_source (upper 1-lower 1) sourceD (by norm_num [sourceD])] <;> rfl

theorem ordinaryInvZ32_grid_abi (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hl : 0<lower 2) (hu : 0<upper 2) :
    ordinaryInvZ32 (realBox a) (realBox b)=gridInvZ32 lower upper := by
  have hD : (sourceD:ℝ)≠0 := by norm_num [sourceD]
  have hlR : (lower 2:ℝ)≠0 := by exact_mod_cast hl.ne'
  have huR : (upper 2:ℝ)≠0 := by exact_mod_cast hu.ne'
  have harg : boxEZInv (realBox a) (realBox b)=
      ((sourceD*(lower 2+upper 2):ℤ):ℝ)/((2*lower 2*upper 2:ℤ):ℝ) := by
    unfold boxEZInv realBox
    rw [haBind 2,hbBind 2]
    simp only [Rat.cast_div,Rat.cast_intCast]
    push_cast
    field_simp [hD,hlR,huR] <;> ring
  unfold ordinaryInvZ32
  rw [harg]
  exact ofReal_int_div_source _ _ (by positivity)

theorem ordinaryNew32_grid_abi (lower upper : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀i,a i=(lower i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀i,b i=(upper i:ℚ)/(sourceD:ℚ))
    (hH : ∀i,sourceH≤lower i) (hwidth : ∀i,lower i<upper i) :
    ordinaryNew32 (realBox a) (realBox b)=gridNew32 lower upper := by
  have hl (i : Fin 3) : 0<lower i := lt_of_lt_of_le (by norm_num [sourceH]) (hH i)
  have hu : 0<upper 2 := (hl 2).trans (hwidth 2)
  unfold gridNew32
  rw [ordinary_source_tree_abi,
    ordinaryEx32_grid_abi lower upper a b haBind hbBind (hl 0).ne',
    ordinaryEy32_grid_abi lower upper a b haBind hbBind (hl 1).ne',
    ordinaryInvZ32_grid_abi lower upper a b haBind hbBind (hl 2) hu]

end
end ImbalancedChen.OriginalThirdP4ASixTentRange32Moments
