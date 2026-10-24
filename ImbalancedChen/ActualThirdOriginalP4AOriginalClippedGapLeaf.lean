import ImbalancedChen.ActualThirdOriginalP4AOrdinaryEarlyReturnLeaf

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.
Original clipped fallback, with signed ao and start=max(2*z1,ao).
Only a primitive literal cap floor, ca<=T, original positive residual,
coordinate bindings and mass-log domain are inputs. The actual OLD lower
argument, actual NEW-OLD gap and factor-difference bound are proved here.
No whole-integral, target difference, query enclosure or K/C bound is input.
-/
namespace ImbalancedChen.OriginalThirdP4AOriginalClippedGapSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdCompactPartitionSourceOnly OriginalThirdClippedChordSourceOnly
open OriginalThirdRoundedNewSourceOnly OriginalThirdPositiveLogSourceOnly
open OriginalThirdSixTentOrdinaryMassCeilSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

/-- The pure concavity argument is the genuine actual-factor proof already
written in the frozen shifted-increment draft, isolated from its old cap
data ancestry. It uses concavity only on [2,infinity), including endpoint2. -/
theorem fixed_increment_antitone {a b d : ℝ}
    (ha : 2≤a) (hab : a≤b) (hd : 0≤d) :
    actualExtendedThirdLowerFactor (b+d)-actualExtendedThirdLowerFactor b≤
      actualExtendedThirdLowerFactor (a+d)-actualExtendedThirdLowerFactor a := by
  by_cases he : a=b
  · subst b
    exact le_rfl
  have hablt : a<b := lt_of_le_of_ne hab he
  have hden : 0<b+d-a := by linarith only [hablt,hd]
  let u : ℝ := (b-a)/(b+d-a)
  let v : ℝ := d/(b+d-a)
  have hu : 0≤u := div_nonneg (sub_nonneg.mpr hab) hden.le
  have hv : 0≤v := div_nonneg hd hden.le
  have huv : u+v=1 := by
    dsimp [u,v]
    field_simp [hden.ne'] <;> ring
  have hvu : v+u=1 := by linarith only [huv]
  have harg1 : u*a+v*(b+d)=a+d := by
    dsimp [u,v]
    field_simp [hden.ne'] <;> ring
  have harg2 : v*a+u*(b+d)=b := by
    dsimp [u,v]
    field_simp [hden.ne'] <;> ring
  have hbd : 2≤b+d := by linarith only [ha,hab,hd]
  have hleft := actual_lower_concaveOn_Ici_two.2 ha hbd hu hv huv
  have hright := actual_lower_concaveOn_Ici_two.2 ha hbd hv hu hvu
  simp only [smul_eq_mul] at hleft hright
  rw [harg1] at hleft
  rw [harg2] at hright
  have hsum :
      (u*actualExtendedThirdLowerFactor a+v*actualExtendedThirdLowerFactor (b+d))+
        (v*actualExtendedThirdLowerFactor a+u*actualExtendedThirdLowerFactor (b+d))=
      actualExtendedThirdLowerFactor a+actualExtendedThirdLowerFactor (b+d) := by
    calc
      _=(u+v)*actualExtendedThirdLowerFactor a+
        (u+v)*actualExtendedThirdLowerFactor (b+d) := by ring
      _=_ := by rw [huv]; ring
  linarith only [hleft,hright,hsum]

/-- The old<=2 branch is handled by the actual zero clamp, not by global
concavity of the extension across2. -/
theorem shifted_gap_of_old_le_two {q s t d : ℝ}
    (hqs : q≤s) (hs : s≤2) (hd : 0≤d) (ht : t≤s+d) :
    actualExtendedThirdLowerFactor t-actualExtendedThirdLowerFactor s≤
      actualExtendedThirdLowerFactor (max 2 q+d)-
        actualExtendedThirdLowerFactor (max 2 q) := by
  have hq : q≤2 := hqs.trans hs
  rw [max_eq_left hq,actualExtendedThirdLowerFactor_of_le_two hs,
    actualExtendedThirdLowerFactor_of_le_two le_rfl,sub_zero,sub_zero]
  exact monotone_actualExtendedThirdLowerFactor (ht.trans (add_le_add_right hs d))

theorem shifted_gap_of_two_le_old {q s t d : ℝ}
    (hqs : q≤s) (hs : 2≤s) (hd : 0≤d) (ht : t≤s+d) :
    actualExtendedThirdLowerFactor t-actualExtendedThirdLowerFactor s≤
      actualExtendedThirdLowerFactor (max 2 q+d)-
        actualExtendedThirdLowerFactor (max 2 q) := by
  have hbase : max 2 q≤s := max_le hs hqs
  have hanti := fixed_increment_antitone (le_max_left 2 q) hbase hd
  exact (sub_le_sub_right (monotone_actualExtendedThirdLowerFactor ht)
    (actualExtendedThirdLowerFactor s)).trans hanti

theorem shifted_gap {q s t d : ℝ}
    (hqs : q≤s) (hd : 0≤d) (ht : t≤s+d) :
    actualExtendedThirdLowerFactor t-actualExtendedThirdLowerFactor s≤
      actualExtendedThirdLowerFactor (max 2 q+d)-
        actualExtendedThirdLowerFactor (max 2 q) := by
  by_cases hs : s≤2
  · exact shifted_gap_of_old_le_two hqs hs hd ht
  · exact shifted_gap_of_two_le_old hqs (le_of_not_ge hs) hd ht

def clippedAo (hi : Fin 3 → ℤ) (ca : ℤ) : ℤ := ca-hi 0-hi 1-hi 2
def clippedStart (hi : Fin 3 → ℤ) (ca : ℤ) : ℤ := max (2*hi 2) (clippedAo hi ca)
def clippedUpperNumerator (lo hi : Fin 3 → ℤ) (ca : ℤ) : ℤ :=
  clippedStart hi ca*lo 2+(T₀-ca)*hi 2
def clippedHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (ca : ℤ) : ℤ :=
  max 0 (readQueryHi160 (assembledRead table.blocks)
      (clippedUpperNumerator lo hi ca) (hi 2*lo 2)-
    readQueryLo160 (assembledRead table.blocks) (clippedStart hi ca) (hi 2))
def clippedCost (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (ca : ℤ) : ℤ :=
  literalOrdinaryUpper lo hi (clippedHigh table lo hi ca)
def newArgument (t : BoxPoint) : ℝ := (thirdPrefixTheta-t 0-t 1-t 2)/t 2

private theorem raw_positive (v : Fin 3 → ℤ) (p : BoxPoint)
    (hp : ∀ i, p i=(v i:ℝ)/(D₀:ℝ)) (hpos : ∀ i, 0<p i) (i : Fin 3) : 0<v i := by
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hv : (0:ℝ)<(v i:ℝ) := (div_pos_iff_of_pos_right hD).1
    (by simpa only [← hp i] using hpos i)
  exact_mod_cast hv

theorem clipped_query_arguments (lo hi : Fin 3 → ℤ) (ca : ℤ)
    (hz0 : 0<lo 2) (hz1 : 0<hi 2) :
    (clippedStart hi ca:ℝ)/(hi 2:ℝ)=max 2 ((clippedAo hi ca:ℝ)/(hi 2:ℝ)) ∧
    (clippedUpperNumerator lo hi ca:ℝ)/((hi 2*lo 2:ℤ):ℝ)=
      (clippedStart hi ca:ℝ)/(hi 2:ℝ)+((T₀-ca:ℤ):ℝ)/(lo 2:ℝ) := by
  have hz0R : (0:ℝ)<(lo 2:ℝ) := by exact_mod_cast hz0
  have hz1R : (0:ℝ)<(hi 2:ℝ) := by exact_mod_cast hz1
  constructor
  · simp only [clippedStart,Int.cast_max,Int.cast_mul,Int.cast_ofNat]
    rw [← max_div_div_right hz1R.le,mul_div_cancel_right₀ 2 hz1R.ne']
  · unfold clippedUpperNumerator
    push_cast
    field_simp [hz0R.ne',hz1R.ne'] <;> ring

/-- The source assert is ca>x1+y1, not ao>=0. It proves the true OLD
lower endpoint even when the original signed ao is negative. -/
theorem old_argument_lower_of_cap_floor
    (lo hi : Fin 3 → ℤ) (ca : ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hres : hi 0+hi 1<ca) {t : BoxPoint} (ht : t∈Icc a b)
    (hcap : (ca:ℝ)/(D₀:ℝ)≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)) :
    (clippedAo hi ca:ℝ)/(hi 2:ℝ)≤actualOldArgument t := by
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hz1 : 0<hi 2 := raw_positive hi b hbBind (fun i => (ha i).trans (hab i)) 2
  have hz1R : (0:ℝ)<(hi 2:ℝ) := by exact_mod_cast hz1
  have hN : (0:ℝ)<((ca-hi 0-hi 1:ℤ):ℝ)/(D₀:ℝ) := by
    apply div_pos _ hD
    have h : (0:ℤ)<ca-hi 0-hi 1 := by omega
    exact_mod_cast h
  have hx := (ht.2 0).trans_eq (hbBind 0)
  have hy := (ht.2 1).trans_eq (hbBind 1)
  have hcapN : ((ca-hi 0-hi 1:ℤ):ℝ)/(D₀:ℝ)≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1 := by
    simp only [Int.cast_sub,sub_div]
    linarith only [hcap,hx,hy]
  have hfrac := div_le_div₀ (hN.le.trans hcapN) hcapN hz (ht.2 2)
  have hqeq : (clippedAo hi ca:ℝ)/(hi 2:ℝ)=
      (((ca-hi 0-hi 1:ℤ):ℝ)/(D₀:ℝ))/b 2-1 := by
    rw [hbBind 2]
    unfold clippedAo
    push_cast
    field_simp [hD.ne',hz1R.ne'] <;> ring
  have hseq : actualOldArgument t=
      (actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1)/t 2-1 := by
    unfold actualOldArgument
    rw [sub_div,div_self hz.ne']
  rw [hqeq,hseq]
  linarith only [hfrac]

/-- The actual NEW-minus-OLD argument increment is bounded by the exact
original rational (T-ca)/z0, without a rounded or guessed gap premise. -/
theorem argument_gap_le_original_delta
    (lo hi : Fin 3 → ℤ) (ca : ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (ha : ∀ i, 0<a i) (hca : ca≤T₀) {t : BoxPoint} (ht : t∈Icc a b)
    (hcap : (ca:ℝ)/(D₀:ℝ)≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)) :
    newArgument t-actualOldArgument t≤((T₀-ca:ℤ):ℝ)/(lo 2:ℝ) := by
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hz0 : 0<lo 2 := raw_positive lo a haBind ha 2
  have hz0R : (0:ℝ)<(lo 2:ℝ) := by exact_mod_cast hz0
  have hscale : (T₀:ℝ)/(D₀:ℝ)=thirdPrefixTheta := by norm_num [thirdPrefixTheta]
  have htop : (0:ℝ)≤((T₀-ca:ℤ):ℝ) := by exact_mod_cast sub_nonneg.mpr hca
  have hnum : thirdPrefixTheta-actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)≤
      ((T₀-ca:ℤ):ℝ)/(D₀:ℝ) := by
    simp only [Int.cast_sub,sub_div,hscale]
    linarith only [hcap]
  have hstep := (div_le_div_of_nonneg_right hnum hz.le).trans
    (div_le_div_of_nonneg_left (div_nonneg htop hD.le) (ha 2) (ht.1 2))
  calc
    newArgument t-actualOldArgument t=
        (thirdPrefixTheta-actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2))/t 2 := by
      unfold newArgument actualOldArgument
      ring
    _≤(((T₀-ca:ℤ):ℝ)/(D₀:ℝ))/a 2 := hstep
    _=((T₀-ca:ℤ):ℝ)/(lo 2:ℝ) := by
      rw [haBind 2]
      field_simp [hD.ne',hz0R.ne'] <;> ring

theorem clippedHigh_nonneg (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (ca : ℤ) :
    0≤value (clippedHigh table lo hi ca) := by
  rw [clippedHigh,value_max,value_zero]
  exact le_max_left _ _

/-- Complete actual pointwise clipped candidate. The only cap input is the
primitive literal floor ca/D<=actualCap; neither target gap nor target factor
difference is a premise. The exact same reader pays both original queries. -/
theorem original_clipped_gap_pointwise
    (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (ca : ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hca : ca≤T₀) (hres : hi 0+hi 1<ca)
    {t : BoxPoint} (ht : t∈Icc a b)
    (hcap : (ca:ℝ)/(D₀:ℝ)≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)) :
    actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t)≤value (clippedHigh table lo hi ca) := by
  have hz0 : 0<lo 2 := raw_positive lo a haBind ha 2
  have hz1 : 0<hi 2 := raw_positive hi b hbBind (fun i => (ha i).trans (hab i)) 2
  have hz0R : (0:ℝ)<(lo 2:ℝ) := by exact_mod_cast hz0
  have hd : (0:ℝ)≤((T₀-ca:ℤ):ℝ)/(lo 2:ℝ) :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hca) hz0R.le
  have hold := old_argument_lower_of_cap_floor lo hi ca a b haBind hbBind ha hab hres ht hcap
  have hgap := argument_gap_le_original_delta lo hi ca a b haBind ha hca ht hcap
  have hs := shifted_gap (t := newArgument t) hold hd (by linarith only [hgap])
  have hargs := clipped_query_arguments lo hi ca hz0 hz1
  have hqh := (CheckedBlockTable.query_encloses_all table
    (clippedUpperNumerator lo hi ca) (hi 2*lo 2) (mul_pos hz1 hz0)).2
  have hql := (CheckedBlockTable.query_encloses_all table (clippedStart hi ca) (hi 2) hz1).1
  rw [hargs.2,hargs.1] at hqh
  rw [hargs.1] at hql
  have hqh' : actualExtendedThirdLowerFactor
      (max 2 ((clippedAo hi ca:ℝ)/(hi 2:ℝ))+((T₀-ca:ℤ):ℝ)/(lo 2:ℝ))≤
      value (readQueryHi160 (assembledRead table.blocks)
        (clippedUpperNumerator lo hi ca) (hi 2*lo 2)) := by
    simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using hqh
  have hql' : value (readQueryLo160 (assembledRead table.blocks) (clippedStart hi ca) (hi 2))≤
      actualExtendedThirdLowerFactor (max 2 ((clippedAo hi ca:ℝ)/(hi 2:ℝ))) := by
    simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using hql
  rw [clippedHigh,value_max,value_zero,value_sub]
  exact (hs.trans (sub_le_sub hqh' hql')).trans (le_max_right _ _)

theorem compactKernel_eq_weighted_gap (t : BoxPoint) :
    compactKernel t=4*(boxWeight t*(actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t))) := by
  dsimp only [compactKernel,actualExtendedThirdOrderedKernel,newArgument,actualOldArgument]
  simp only [mul_zero,sub_zero,boxWeight,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem clipped_boxWeight_nonneg (a b : BoxPoint) (ha : ∀ i, 0<a i)
    {t : BoxPoint} (ht : t∈Icc a b) : 0≤boxWeight t := by
  have hx := (ha 0).trans_le (ht.1 0)
  have hy := (ha 1).trans_le (ht.1 1)
  have hz := (ha 2).trans_le (ht.1 2)
  unfold boxWeight
  positivity

private theorem clipped_continuousOn_boxWeight (a b : BoxPoint) (ha : ∀ i, 0<a i) :
    ContinuousOn boxWeight (Icc a b) := by
  have hcoord (i : Fin 3) : ContinuousOn (fun t : BoxPoint => t i) (Icc a b) :=
    (continuous_apply i).continuousOn
  have hn (i : Fin 3) (t : BoxPoint) (ht : t∈Icc a b) : t i≠0 :=
    ((ha i).trans_le (ht.1 i)).ne'
  exact ((continuousOn_const.div (hcoord 0) (hn 0)).mul
    (continuousOn_const.div (hcoord 1) (hn 1))).mul
    (continuousOn_const.div ((hcoord 2).pow 2) (fun t ht => pow_ne_zero 2 (hn 2 t ht)))

/-- Integration on the actual compact intersection, valid also for a
boundary box. The positive full-box mass is only a measure majorant here. -/
theorem original_clipped_gap_integral
    (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (ca : ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hca : ca≤T₀) (hres : hi 0+hi 1<ca)
    (hcap : ∀ t∈compactRegion ∩ Icc a b,
      (ca:ℝ)/(D₀:ℝ)≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)) :
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
      4*boxMass a b*value (clippedHigh table lo hi ca) := by
  let g : BoxPoint → ℝ := fun t => 4*(boxWeight t*value (clippedHigh table lo hi ca))
  have hc : ContinuousOn g (Icc a b) :=
    continuousOn_const.mul ((clipped_continuousOn_boxWeight a b ha).mul continuousOn_const)
  have hg : IntegrableOn g (Icc a b) := hc.integrableOn_compact isCompact_Icc
  have hk : IntegrableOn compactKernel (compactRegion ∩ Icc a b) :=
    integrableOn_compactKernel.mono_set inter_subset_left
  have hmono : (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
      ∫ t in compactRegion ∩ Icc a b,g t := by
    apply integral_mono_ae hk (hg.mono_set inter_subset_right)
    filter_upwards [ae_restrict_mem (measurableSet_compactRegion.inter measurableSet_Icc)] with t ht
    rw [compactKernel_eq_weighted_gap]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (original_clipped_gap_pointwise table lo hi ca a b haBind hbBind ha hab
          hca hres ht.2 (hcap t ht)) (clipped_boxWeight_nonneg a b ha ht.2)) (by norm_num)
  have hgnonneg : 0≤ᵐ[volume.restrict (Icc a b)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (by norm_num) (mul_nonneg (clipped_boxWeight_nonneg a b ha ht)
      (clippedHigh_nonneg table lo hi ca))
  have hsubset : compactRegion ∩ Icc a b≤ᵐ[volume] Icc a b :=
    Filter.Eventually.of_forall (fun t ht => ht.2)
  have hlarge := setIntegral_mono_set hg hgnonneg hsubset
  have hfull : (∫ t in Icc a b,g t)=4*boxMass a b*value (clippedHigh table lo hi ca) := by
    have heq : g=(fun t : BoxPoint => (4*value (clippedHigh table lo hi ca))*boxWeight t) := by
      funext t
      dsimp [g]
      ring
    rw [heq,integral_const_mul,integral_boxWeight a b ha (fun i => (hab i).le)]
    ring
  exact hmono.trans (hlarge.trans_eq hfull)

/-- Exact original full ordinary mass.hi and UP for the clipped high.
The unit-log mass branch retains its existing ratio<=2 domain. -/
theorem original_clipped_gap_integer_upper
    (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (ca : ℤ) (a b : BoxPoint)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D₀:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D₀:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)
    (hca : ca≤T₀) (hres : hi 0+hi 1<ca)
    (hcap : ∀ t∈compactRegion ∩ Icc a b,
      (ca:ℝ)/(D₀:ℝ)≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)) :
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤value (clippedCost table lo hi ca) := by
  have hleaf := original_clipped_gap_integral table lo hi ca a b haBind hbBind ha hab hca hres hcap
  have hm := (literal_ordinary_mass_encloses lo hi D₀ a b rfl haBind hbBind ha hab hratio).2
  have hh := clippedHigh_nonneg table lo hi ca
  calc
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
        4*boxMass a b*value (clippedHigh table lo hi ca) := hleaf
    _≤value (literalOrdinaryMass lo hi).hi*value (clippedHigh table lo hi ca) :=
      mul_le_mul_of_nonneg_right hm hh
    _=value (clippedHigh table lo hi ca)*value (literalOrdinaryMass lo hi).hi := by ring
    _≤value (clippedCost table lo hi ca) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

end
end ImbalancedChen.OriginalThirdP4AOriginalClippedGapSourceOnly
