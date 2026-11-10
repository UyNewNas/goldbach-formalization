import ImbalancedChen.Part5OriginalH430W1SwitchedBuchstabIntegral
import ImbalancedChen.P2SeedOriginalQ80Darboux

/-! Direct outward bound for the 70 original W1 Q80 base integers of the
430 arm. Historical 6.761767 and the current smaller K keep their distinct
values. Cell validity and integer-only comparisons await remote evaluation. -/
namespace ImbalancedChen.Part5OriginalH430W1OriginalBaseEnclosure
noncomputable section
open Set MeasureTheory Real
open P5OriginalActionMassBound (W1Anchor W1Target)
open P2Selected430LiteralActionData (rows)
open P2SeedOriginalQ80Darboux
open Certificates.P2HistoricQ80DefectLookup (I80)
open Part5OriginalH430BankSlotTargets Part5OriginalH430FixedReadDictionary
open Part5OriginalH430W1SwitchedBuchstabIntegral (envelope switchedIntegral original_switched_integral_le)
open Part5OriginalH430OrdinarySingletonKernel (ordinaryLowerIntegral canonical_lower_log clippedLower anchor_correction)
open Part5OriginalH430BankOrdinarySingletons (integral)
open Part5OriginalH430W1SignedOrdinaryBase (ordinaryBase)
open P5CanonicalUpperCancellation (upperA lowerBar)
open scoped Classical BigOperators Interval

def tableK : ℚ := 6761767/1000000
def currentK : ℚ := 8452171/1250000
def target (i : Fin 7) : ℚ := 12/5+(i.val:ℚ)/10
def anchor (j : Fin 10) : ℚ := 16/5+(j.val:ℚ)/5
def left (j : Fin 10) : ℚ := 1/anchor j
def right (i : Fin 7) (j : Fin 10) : ℚ := min (1/target i) (1-2/anchor j)

private def corr : Expr := .div (.log (.sub .var (.rat 1))) .var
private def neg (j : Fin 10) : Expr := .div
  (.log (.sub (.mul (.rat (anchor j)) (.sub (.rat 1) .var)) (.rat 1)))
  (.mul .var (.sub (.rat 1) .var))

private def corrBound (j : Fin 10) : I80 := darboux corr 2 (anchor j-1) 32768
private def negBound (i : Fin 7) (j : Fin 10) : I80 := darboux (neg j) (left j) (right i j) 32768
private def massHi (i : Fin 7) (j : Fin 10) : ℚ :=
  (70893/125000)*((anchor j+target i)*Certificates.logSeriesUpper (anchor j/target i) 48
    -2*(anchor j-target i))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem corr_checked (j : Fin 10) : CellsValid corr 2 (anchor j-1) 32768 := by
  fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem ordinary_checked (i : Fin 7) (j : Fin 10) :
    CellsValid (neg j) (left j) (right i j) 32768 ∧
    ((rows (slotOfAction (.inl (i,j)))).base:ℚ)/(2^80:ℚ) ≤
      -(corrBound j).decodeHi+(negBound i j).decodeLo/2-tableK*massHi i j/8 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem geometry (i : Fin 7) (j : Fin 10) :
    2<target i ∧ target i≤3 ∧ 3<anchor j ∧ anchor j≤5 ∧
      left j<right i j ∧ right i j≤1/target i ∧ right i j≤1-2/anchor j := by
  fin_cases i <;> fin_cases j <;> norm_num [target,anchor,left,right]

private theorem names (i : Fin 7) (j : Fin 10) :
    (target i:ℝ)=W1Target i ∧ (anchor j:ℝ)=W1Anchor j := by
  simp [target,anchor,W1Target,W1Anchor]

private theorem mass_hi (i : Fin 7) (j : Fin 10) : envelope i j ≤ (massHi i j:ℝ) := by
  let x := anchor j/target i
  have hg := geometry i j
  have hx : 1≤x := (one_le_div (by linarith [hg.1] : 0<target i)).mpr
    (by linarith [hg.2.1,hg.2.2.1])
  let c : Certificates.RationalLogCertificate :=
    ⟨x,48,Certificates.logSeriesLower x 48,Certificates.logSeriesUpper x 48⟩
  have hv : c.Valid := ⟨hx,le_rfl,le_rfl⟩
  have hh := (c.check_sound (decide_eq_true hv)).2
  change log (x:ℝ) ≤ (Certificates.logSeriesUpper x 48:ℝ) at hh
  have hpos : 0≤((anchor j+target i : ℚ):ℝ) := by
    exact_mod_cast (by linarith [hg.1,hg.2.2.1] : 0≤anchor j+target i)
  have h := mul_le_mul_of_nonneg_left hh hpos
  unfold envelope massHi
  rw [←(names i j).1,←(names i j).2]
  dsimp only [x] at h
  push_cast at h ⊢
  unfold P2SeedOmegaLiteralFibre.omegaCap
  linarith only [h]

private theorem truncated_ordinary_lower (i : Fin 7) (j : Fin 10) :
    (∫ u in (left j:ℝ)..(right i j:ℝ),(neg j).real u) ≤ integral (.inl (i,j)) := by
  let a : ℝ := anchor j
  let s : ℝ := target i
  let l : ℝ := left j
  let r : ℝ := right i j
  let f := fun u : ℝ => clippedLower (a*(1-u))/(u*(1-u))
  have hg := geometry i j
  have hs : 2<s := by exact_mod_cast hg.1
  have ha : 3<a := by exact_mod_cast hg.2.2.1
  have ha' : a≤5 := by exact_mod_cast hg.2.2.2.1
  have hl : l=1/a := by simp [l,a,left]
  have hl' : 0<l := by rw [hl]; exact one_div_pos.mpr (by linarith)
  have hlt : l<r := by exact_mod_cast hg.2.2.2.2.1
  have hr : r≤1/s := by exact_mod_cast hg.2.2.2.2.2.1
  have haCut : r≤1-2/a := by exact_mod_cast hg.2.2.2.2.2.2
  have hs1 : 1/s<1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hf : ContinuousOn f (Icc l (1/s)) := by
    dsimp only [f,clippedLower]
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · fun_prop
      · exact fun u _ => (zero_lt_one.trans_le (le_max_left _ _)).ne'
    · fun_prop
    · exact fun u hu => mul_ne_zero (hl'.trans_le hu.1).ne' (by linarith [hu.2])
  have h4 (u : ℝ) (hu : u∈Ioo l (1/s)) : a*(1-u)≤4 := by
    have h := mul_le_mul_of_nonneg_left hu.1.le (show 0≤a by linarith)
    rw [hl] at h
    have hh : a*(1/a)=1 := by field_simp [(by linarith : a≠0)]
    linarith only [h,hh,ha']
  have hsmall : (∫ u in l..r,(neg j).real u)=∫ u in Ioo l r,f u := by
    rw [intervalIntegral.integral_of_le hlt.le,←integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    have hu' : u∈Ioo l (1/s) := ⟨hu.1,hu.2.trans_le hr⟩
    have hcut := hu.2.le.trans haCut
    have hh := mul_le_mul_of_nonneg_left hcut (show 0≤a by linarith)
    have htwo : a*(2/a)=2 := by field_simp [(by linarith : a≠0)]
    have hge : 2≤a*(1-u) := by linarith only [hh,htwo]
    dsimp only [neg,Expr.real,f,clippedLower]
    rw [min_eq_right (by linarith only [h4 u hu'] : a*(1-u)-1≤3),
      max_eq_right (by linarith : 1≤a*(1-u)-1)]
  have htotal : integral (.inl (i,j))=∫ u in Ioo l (1/s),f u := by
    unfold integral ordinaryLowerIntegral
    change (∫ u in Ioo (1/W1Anchor j) (1/W1Target i),lowerBar (W1Anchor j*(1-u))/(u*(1-u)))=_
    rw [←(names i j).1,←(names i j).2,←hl]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    rw [canonical_lower_log (h4 u hu)]
  rw [hsmall,htotal]
  have hi := (hf.integrableOn_compact isCompact_Icc).mono_set
    (Ioo_subset_Icc_self : Ioo l (1/s) ⊆ Icc l (1/s))
  apply setIntegral_mono_set hi _ (Filter.Eventually.of_forall (fun u hu => ⟨hu.1,hu.2.trans_le hr⟩))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  apply div_nonneg (log_nonneg (le_max_left _ _))
  exact mul_nonneg (hl'.trans hu.1).le (by linarith [hu.2])

/-- The full actual switched integral plus the Q80 base is covered by
the canonical ordinary part at the original 430 arm's positive K. -/
theorem all70_archived_base_vs_envelope (i : Fin 7) (j : Fin 10) :
    baseValue (.inl (i,j))+(tableK:ℝ)*envelope i j/8 ≤ ordinaryBase i j := by
  have hg := geometry i j
  have hc := darboux_contains corr 2 (anchor j-1) 32768
    (by linarith [hg.2.2.1]) (by norm_num) (corr_checked j)
  have hn := darboux_contains (neg j) (left j) (right i j) 32768
    hg.2.2.2.2.1 (by norm_num) (ordinary_checked i j).1
  have hdp : P2SeedOmegaLiteralFunctional.correction (W1Anchor j) ≤ ((corrBound j).decodeHi:ℝ) := by
    rw [←(names i j).2]
    simpa [corrBound,corr,Expr.real,P2SeedOmegaLiteralFunctional.correction] using hc.2
  have hneg := hn.1.trans (truncated_ordinary_lower i j)
  have hnum : baseValue (.inl (i,j)) ≤ -((corrBound j).decodeHi:ℝ)+((negBound i j).decodeLo:ℝ)/2-
      (tableK:ℝ)*(massHi i j:ℝ)/8 := by
    unfold baseValue
    exact_mod_cast (ordinary_checked i j).2
  have hI := mass_hi i j
  have hmul := mul_le_mul_of_nonneg_left hI (by norm_num [tableK] : 0≤(tableK:ℝ))
  have htarget := P5CanonicalUpperCancellation.upperA_eq_one
    (by rw [←(names i j).1]; exact_mod_cast (by linarith [hg.1] : (0:ℚ)<target i))
    (by rw [←(names i j).1]; exact_mod_cast hg.2.1)
  have hanchor := anchor_correction (s:=W1Anchor j)
    (by rw [←(names i j).2]; exact_mod_cast hg.2.2.1.le)
    (by rw [←(names i j).2]; exact_mod_cast hg.2.2.2.1)
  unfold ordinaryBase
  rw [htarget,hanchor]
  change ((negBound i j).decodeLo:ℝ)≤integral (.inl (i,j)) at hneg
  linarith only [hdp,hneg,hnum,hmul]

theorem all70_archived_base_vs_true_integral (i : Fin 7) (j : Fin 10) {α : ℝ} (hα : 2≤α) :
    baseValue (.inl (i,j))+(tableK:ℝ)*switchedIntegral i j α/8 ≤ ordinaryBase i j := by
  calc
    _ ≤ baseValue (.inl (i,j))+(tableK:ℝ)*envelope i j/8 := by
      exact add_le_add_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (original_switched_integral_le i j hα)
          (by norm_num [tableK])) (by norm_num)) _
    _ ≤ _ := all70_archived_base_vs_envelope i j

end
end ImbalancedChen.Part5OriginalH430W1OriginalBaseEnclosure
