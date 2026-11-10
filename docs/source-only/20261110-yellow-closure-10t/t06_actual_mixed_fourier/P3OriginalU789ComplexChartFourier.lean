import ImbalancedChen.P3OriginalU789AffinePhaseBudget

/-!
SUPPLEMENT / SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
Actual six U789 geometric sources through their literal HB owner products,
per-original-group reciprocal logarithms, complete eta, grouped psi,
fixed plateau and shifted original smooth HB children. Complex phases are
real cos plus imaginary sin of the same affine logarithmic phase.
No abstract Family, final chart norm, representation or PP premise.
-/
namespace ImbalancedChen.P3OriginalU789ComplexChartFourier
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open P3OriginalU789AffinePhaseBudget P3ActualHBChildMixedFourier
open P5OriginalU789SmoothLogSources P5OriginalU789SmoothChartRoughOne
open P5Z.GroupedOccurrenceLogShift P5Z.AllWordAmbientOccurrenceBound
open P5Z.OccurrenceWordFourFactorLeibniz P5Z.ActualOccurrencePlateauWordBudget
open P5Z.ActualEtaPsiOccurrenceBudget P5Z.ActualIndependentGroupLogNormalization
open P5Z.ActualAllRankOccurrenceFourierBridge P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.ActualEuclideanPhysicalFourier P5Z.AllRankCauchyKernelIntegral
open P5Z.AllRankCauchyCubeTail

theorem source_rank_le_four (s : Source) : rank s ≤ 4 := by cases s <;> norm_num [rank]

def numerator {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ)
    (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) (z : Fin d → ℝ) : ℝ :=
  phaseProfile s N width (fun i => Real.log (groupBase owner U i)) owner
      phaseOffset frequency part z *
    groupLogProduct (fun i => groupProduct owner U i z) * shiftedChildTensor offset child z

def chart {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) (z : Fin d → ℝ) : ℝ :=
  numerator s N width owner U offset child phaseOffset frequency part z *
    actualEta N owner U κ₀ z * actualPsi owner U R z * plateau d z

theorem numerator_smooth {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ)
    (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) :
    ContDiff ℝ ∞ (numerator s N width owner U offset child phaseOffset frequency part) := by
  have hG : ContDiff ℝ ∞ (fun z => groupLogProduct (fun i => groupProduct owner U i z)) :=
    (groupLogProduct_smooth (rank s)).comp
      (contDiff_pi.mpr (fun i => groupProduct_smooth owner U i))
  exact ((phaseProfile_smooth s N width _ owner phaseOffset frequency part).mul hG).mul
    (shiftedChildTensor_smooth offset child)

theorem chart_smooth {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) :
    ContDiff ℝ ∞ (chart s N width owner U R κ₀ offset child phaseOffset frequency part) :=
  (((numerator_smooth s N width owner U offset child phaseOffset frequency part).mul
    (actualEta_smooth N owner U κ₀)).mul (actualPsi_smooth owner U R)).mul (plateau_smooth d)

theorem chart_tsupport_box {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) :
    tsupport (chart s N width owner U R κ₀ offset child phaseOffset frequency part) ⊆ plateauBox d :=
  window_tsupport d (fun z => numerator s N width owner U offset child phaseOffset frequency part z *
    actualEta N owner U κ₀ z * actualPsi owner U R z)

theorem chart_compact {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) :
    HasCompactSupport (chart s N width owner U R κ₀ offset child phaseOffset frequency part) :=
  HasCompactSupport.of_support_subset_isCompact (plateauBox_compact d)
    ((subset_tsupport _).trans (chart_tsupport_box s N width owner U R κ₀ offset child
      phaseOffset frequency part))

/-- Six actual source families, no guessed mixed-Euler envelope for W.
All derivative costs are proved from their actual margins and factors. -/
theorem exists_chart_word_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Source) (N d : ℕ) (width P : ℝ),
      1 ≤ Real.log (N : ℝ) → 0 < width → width ≤ 1 → 0 ≤ P →
      ∀ (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
        (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
        (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2),
      (∀ a, 0 < U a) → (∀ i, 0 < R i) → (∀ a, |frequency a| ≤ P) → d ≤ 24 →
      ∀ (w : List (Fin d)) (z : Fin d → ℝ), w.length ≤ 48 →
      |occWord w (chart s N width owner U R κ₀ offset child phaseOffset frequency part) z| ≤
        C*(1/width+P)^48 := by
  obtain ⟨CA,hCA,bA⟩ := exists_actual_phase_word_budget
  obtain ⟨CG,hCG,bG⟩ := groupLogProduct_word_budget 4 48
  obtain ⟨MC,hMC,bC⟩ := exists_childLog_global_budget 48
  obtain ⟨ME,hME,bE⟩ := finite_order_constants etaLog exists_etaLog_order_bound 48
  obtain ⟨MP,hMP,bP⟩ := finite_order_constants psiLog exists_psiLog_order_bound 48
  obtain ⟨MT,hMT,bT⟩ := exists_uniform_plateau_word_budget 4
  let CN : ℝ := (4 : ℝ)^48*CA*CG*MC^24
  let C : ℝ := (4 : ℝ)^48*CN*ME*MP^4*MT
  refine ⟨C,by dsimp [C,CN]; positivity,?_⟩
  intro s N d width P hell hw hwOne hP owner U R κ₀ offset child phaseOffset frequency part
    hU hR hf hd w z hword
  have hN : 0 < (N : ℝ) := by
    by_contra hn
    have hz : (N : ℝ)=0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg N)
    simp [hz] at hell
  have bnum (v : List (Fin d)) (hv : v.length ≤ 48) :
      |occWord v (numerator s N width owner U offset child phaseOffset frequency part) z| ≤
        CN*(1/width+P)^48 := by
    have hG : ContDiff ℝ ∞ (fun y => groupLogProduct (fun i => groupProduct owner U i y)) :=
      (groupLogProduct_smooth (rank s)).comp
        (contDiff_pi.mpr (fun i => groupProduct_smooth owner U i))
    have hraw := occWord_four_bound
      (phaseProfile s N width (fun i => Real.log (groupBase owner U i)) owner
        phaseOffset frequency part)
      (fun y => groupLogProduct (fun i => groupProduct owner U i y))
      (shiftedChildTensor offset child) (fun _ => 1)
      (phaseProfile_smooth s N width _ owner phaseOffset frequency part)
      hG (shiftedChildTensor_smooth offset child) contDiff_const v z
      (CA*(1/width+P)^48) CG (MC^24) 1
      (by positivity) (zero_le_one.trans hCG) (by positivity) zero_le_one
      (fun q hq => bA s N d width P hell hw hwOne hP _ owner phaseOffset frequency part
        hf hd q z (hq.trans hv))
      (fun q hq => bG (rank s) (source_rank_le_four s) d owner U hU q z (hq.trans hv))
      (fun q hq => (shiftedChildTensor_word_bound offset child q z MC
        (zero_le_one.trans hMC) (fun n hn a u => bC n a u (hn.trans (hq.trans hv)))).trans
          (pow_le_pow_right₀ hMC hd))
      (fun q hq => P3ActualHBChildMixedFourier.occurrence_one_bound q z)
    have heq : (fun y => phaseProfile s N width (fun i => Real.log (groupBase owner U i))
        owner phaseOffset frequency part y * groupLogProduct (fun i => groupProduct owner U i y) *
        shiftedChildTensor offset child y * 1) =
        numerator s N width owner U offset child phaseOffset frequency part := by
      funext y; simp [numerator]
    rw [heq] at hraw
    simp only [mul_one] at hraw
    calc
      _ ≤ (4 : ℝ)^v.length*((CA*(1/width+P)^48)*CG*MC^24) := hraw
      _ ≤ (4 : ℝ)^48*((CA*(1/width+P)^48)*CG*MC^24) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hv) (by positivity)
      _ = CN*(1/width+P)^48 := by dsimp [CN]; ring
  have bEta (v : List (Fin d)) (hv : v.length ≤ w.length) :
      |occWord v (actualEta N owner U κ₀) z| ≤ ME := by
    rw [actualEta_eq_scalarLift N owner U κ₀ hN hU,occWord_scalarLift]
    exact bE v.length (hv.trans hword) _
  have bPsi (v : List (Fin d)) (hv : v.length ≤ w.length) :
      |occWord v (actualPsi owner U R) z| ≤ MP^4 := by
    rw [actualPsi_eq_groupTensor owner U R hU hR]
    exact (groupTensor_word_bound owner _ psiLog v z MP (zero_le_one.trans hMP)
      (fun n hn x => bP n (hn.trans (hv.trans hword)) x)).trans
        (pow_le_pow_right₀ hMP (source_rank_le_four s))
  have hraw := occWord_four_bound
    (numerator s N width owner U offset child phaseOffset frequency part)
    (actualEta N owner U κ₀) (actualPsi owner U R) (plateau d)
    (numerator_smooth s N width owner U offset child phaseOffset frequency part)
    (actualEta_smooth N owner U κ₀) (actualPsi_smooth owner U R) (plateau_smooth d)
    w z (CN*(1/width+P)^48) ME (MP^4) MT
    (by dsimp [CN]; positivity) (zero_le_one.trans hME) (by positivity) (zero_le_one.trans hMT)
    (fun v hv => bnum v (hv.trans hword)) bEta bPsi
    (fun v hv => bT d (by omega) v (hv.trans hword) z)
  change |occWord w (chart s N width owner U R κ₀ offset child phaseOffset frequency part) z| ≤ _ at hraw
  calc
    _ ≤ (4 : ℝ)^w.length*((CN*(1/width+P)^48)*ME*MP^4*MT) := hraw
    _ ≤ (4 : ℝ)^48*((CN*(1/width+P)^48)*ME*MP^4*MT) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hword) (by dsimp [CN]; positivity)
    _ = C*(1/width+P)^48 := by dsimp [C]; ring

def realChart {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) : V d → ℂ :=
  euclideanLift d (chart s N width owner U R κ₀ offset child phaseOffset frequency part)

def complexChart {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (z : V d) : ℂ :=
  realChart s N width owner U R κ₀ offset child phaseOffset frequency 0 z+
    Complex.I*realChart s N width owner U R κ₀ offset child phaseOffset frequency 1 z

theorem complexChart_smooth {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) :
    ContDiff ℝ ∞ (complexChart s N width owner U R κ₀ offset child phaseOffset frequency) := by
  have h (part : Fin 2) : ContDiff ℝ ∞
      (realChart s N width owner U R κ₀ offset child phaseOffset frequency part) :=
    euclideanLift_smooth d _ (chart_smooth s N width owner U R κ₀ offset child phaseOffset frequency part)
  exact (h 0).add ((h 1).const_smul Complex.I)

theorem complexChart_compact {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) :
    HasCompactSupport (complexChart s N width owner U R κ₀ offset child phaseOffset frequency) := by
  let g := realChart s N width owner U R κ₀ offset child phaseOffset frequency 0
  let h := realChart s N width owner U R κ₀ offset child phaseOffset frequency 1
  have hc (part : Fin 2) : HasCompactSupport
      (realChart s N width owner U R κ₀ offset child phaseOffset frequency part) :=
    euclideanLift_compact d _ (chart_compact s N width owner U R κ₀ offset child phaseOffset frequency part)
  apply HasCompactSupport.of_support_subset_isCompact ((hc 0).isCompact.union (hc 1).isCompact)
  intro z hz
  by_cases hg : g z=0
  · right
    apply subset_tsupport h
    intro hh
    have heq : complexChart s N width owner U R κ₀ offset child phaseOffset frequency z =
        g z+Complex.I*h z := rfl
    exact hz (by rw [heq,hg,hh]; simp)
  · exact Or.inl (subset_tsupport g hg)

def geometry {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3) (z : Fin d → ℝ) : ℝ :=
  originalProfile s N width
      (logCoordinates s (Real.log (N : ℝ)) (fun i => Real.log (groupBase owner U i)) owner z) *
    groupLogProduct (fun i => groupProduct owner U i z) * shiftedChildTensor offset child z *
    actualEta N owner U κ₀ z * actualPsi owner U R z * plateau d z

theorem complexChart_toLp {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (z : Fin d → ℝ) :
    complexChart s N width owner U R κ₀ offset child phaseOffset frequency (WithLp.toLp 2 z) =
      (geometry s N width owner U R κ₀ offset child z : ℂ) *
        Complex.exp (((phaseOffset+∑ a,frequency a*z a : ℝ) : ℂ)*Complex.I) := by
  have hr (part : Fin 2) :
      chart s N width owner U R κ₀ offset child phaseOffset frequency part z =
      geometry s N width owner U R κ₀ offset child z *
        trig part (phaseOffset+∑ a,frequency a*z a) := by
    unfold chart numerator phaseProfile geometry
    ring
  simp only [complexChart,realChart,euclideanLift_toLp,hr,Complex.ofReal_mul,
    Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
  norm_num only [trig,if_pos rfl,show (1 : Fin 2) ≠ 0 by norm_num,if_false]
  ring

/-- Independent integer geometric weight, with one reciprocal logarithm
for EACH ORIGINAL group, not for each HB occurrence. -/
def integerGeometry {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (n : Fin d → ℕ) : ℝ :=
  originalProfile s N width (fun i => Real.log (integerGroupProduct owner n i : ℝ)/Real.log (N : ℝ)) /
      (∏ i,Real.log (integerGroupProduct owner n i : ℝ)) *
    eta (((∏ i,integerGroupProduct owner n i : ℕ) : ℝ)/(N : ℝ)^(1-κ₀)) *
    ∏ i,psi ((integerGroupProduct owner n i : ℝ)/R i)

theorem logCoordinates_groupProducts {d : ℕ} (s : Source) (ell : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (hU : ∀ a,0<U a)
    (z : Fin d → ℝ) :
    logCoordinates s ell (fun i => Real.log (groupBase owner U i)) owner z =
      fun i => Real.log (groupProduct owner U i z)/ell := by
  funext i
  rw [logCoordinates,groupProduct,Real.log_mul (groupBase_pos owner U hU i).ne'
    (Real.exp_pos _).ne',Real.log_exp]

/-- Closed atoms include the actual unit blocks at log-coordinate0. -/
theorem plateau_closed_atom {d : ℕ} (U : Fin d → ℝ) (n : Fin d → ℕ)
    (hU : ∀ a,0<U a) (hlo : ∀ a,U a≤(n a : ℝ))
    (hhi : ∀ a,(n a : ℝ)≤2*U a) : plateau d (logOccurrence U n)=1 := by
  unfold plateau
  apply Finset.prod_eq_one
  intro a ha
  apply c_eq_one
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ (hU a)).mpr (by simpa using hlo a))
  · exact Real.log_le_log (div_pos ((hU a).trans_le (hlo a)) (hU a))
      ((div_le_iff₀ (hU a)).mpr (hhi a))

/-- Exact actual original U789 HB integer identification and physical
complex Mellin phase. The lower bases, labels and original group owner
products are all literal; no abstract representation premise occurs. -/
theorem complexChart_integer_atom {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
    (κ₀ : ℝ) (label : Fin d → ℕ) (child : Fin d → Fin 3)
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (n : Fin d → ℕ)
    (hU : ∀ a,0<U a) (hlo : ∀ a,U a≤(n a : ℝ))
    (hhi : ∀ a,(n a : ℝ)≤2*U a) :
    complexChart s N width owner U R κ₀
      (fun a => Real.log (U a/(2 : ℝ)^(label a))) child phaseOffset frequency
      (WithLp.toLp 2 (logOccurrence U n)) =
      (integerGeometry s N width owner R κ₀ n : ℂ) *
        Complex.exp ((phaseOffset : ℂ)*Complex.I) * occurrenceMode U n frequency *
        ∏ a : Fin d,P3HBSmoothThreeWayRatioTwo.smoothCoord (fun t => (chi t : ℂ))
          (n a : ℝ) (label a) (child a) := by
  let z := logOccurrence U n
  have hn : ∀ a,0<n a := fun a => by exact_mod_cast (hU a).trans_le (hlo a)
  have hgroup := groupProduct_logOccurrence owner U n hU hn
  have hG := normalize_nat (fun _ : Fin (rank s) → ℝ => (1 : ℝ)) (integerGroupProduct owner n)
  simp only [normalize,one_mul] at hG
  have hchild := shiftedChildTensor_physical label child U hU z
  have hcoord (a : Fin d) : U a*Real.exp (z a)=(n a : ℝ) := by
    rw [show z a=Real.log ((n a : ℝ)/U a) from rfl,
      Real.exp_log (div_pos (by exact_mod_cast hn a) (hU a))]
    field_simp [(hU a).ne']
  simp_rw [hcoord] at hchild
  have hgeometry : (geometry s N width owner U R κ₀
      (fun a => Real.log (U a/(2 : ℝ)^(label a))) child z : ℂ) =
      (integerGeometry s N width owner R κ₀ n : ℂ) *
        ∏ a : Fin d,P3HBSmoothThreeWayRatioTwo.smoothCoord (fun t => (chi t : ℂ))
          (n a : ℝ) (label a) (child a) := by
    unfold geometry
    rw [logCoordinates_groupProducts s _ owner U hU]
    simp_rw [hgroup]
    rw [plateau_closed_atom U n hU hlo hhi]
    simp only [actualEta,actualPsi,hgroup,hG,mul_one,Nat.cast_prod]
    push_cast
    rw [hchild]
    unfold integerGeometry
    push_cast
    ring
  have hphase : Complex.exp (((phaseOffset+∑ a,frequency a*z a : ℝ) : ℂ)*Complex.I) =
      Complex.exp ((phaseOffset : ℂ)*Complex.I)*occurrenceMode U n frequency := by
    simp only [Complex.ofReal_add,add_mul,Complex.exp_add,Complex.ofReal_sum,
      Finset.sum_mul,Complex.exp_sum,occurrenceMode,z]
  rw [complexChart_toLp,hgeometry,hphase]
  ring

/-- The actual retained physical H-box supplies the phase licence.
There is no extra unproved uniform bound on admitted frequencies. -/
theorem retained_frequency_bound {d : ℕ} {H : ℝ} {frequency : Fin d → ℝ}
    (hf : frequency ∈ (outsideCube d H)ᶜ) : ∀ a,|frequency a|≤H := by
  intro a
  apply le_of_not_gt
  intro ha
  exact hf ⟨a,ha⟩

/-- The original group Mellin phase has one exponent per ORIGINAL
coordinate. Repeated HB owners receive precisely that same exponent. -/
theorem original_group_phase {d : ℕ} (s : Source)
    (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (hU : ∀ a,0<U a)
    (t : Fin (rank s) → ℝ) (z : Fin d → ℝ) :
    (∑ i,t i*Real.log (groupProduct owner U i z)) =
      (∑ i,t i*Real.log (groupBase owner U i))+∑ a,t (owner a)*z a := by
  simp_rw [groupProduct,Real.log_mul (groupBase_pos owner U hU _).ne'
    (Real.exp_pos _).ne',Real.log_exp,mul_add,Finset.sum_add_distrib]
  congr 1
  simp only [groupLog,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [mul_ite,mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- Necessary real/imaginary conversion for actual complex geometric
profiles. It uses the genuine Frechet derivative's linearity only. -/
theorem coordWord_realImag {d : ℕ} (g h : V d → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (w : List (Fin d)) :
    coordWord d w (fun z => g z+Complex.I*h z) =
      fun z => coordWord d w g z+Complex.I*coordWord d w h z := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change coordDeriv d i (coordWord d w (fun z => g z+Complex.I*h z)) = _
      rw [ih]
      funext z
      have hdg := (((coordWord_smooth d w g hg).differentiable (by simp)) z).hasFDerivAt
      have hdh := (((coordWord_smooth d w h hh).differentiable (by simp)) z).hasFDerivAt
      have hd := hdg.add (hdh.const_smul Complex.I)
      change fderiv ℝ (fun z => coordWord d w g z+Complex.I*coordWord d w h z) z
        (unit d i) = _
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      rfl

theorem mixedD_realImag_le {d : ℕ} (g h : V d → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    mixedD d (fun z => g z+Complex.I*h z) ≤ mixedD d g+mixedD d h := by
  have hpair : ContDiff ℝ ∞ (fun z => g z+Complex.I*h z) := hg.add (hh.const_smul Complex.I)
  have hpc : HasCompactSupport (fun z => g z+Complex.I*h z) := by
    apply HasCompactSupport.of_support_subset_isCompact (hgc.isCompact.union hhc.isCompact)
    intro z hz
    by_cases hgz : g z=0
    · right
      apply subset_tsupport h
      intro hhz
      exact hz (by simp [hgz,hhz])
    · exact Or.inl (subset_tsupport g hgz)
  unfold mixedD
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S hS
  rw [coordWord_realImag g h hg hh]
  have hgi := mixedD_term_integrable d g hg hgc S
  have hhi := mixedD_term_integrable d h hh hhc S
  have hpi := mixedD_term_integrable d (fun z => g z+Complex.I*h z) hpair hpc S
  rw [coordWord_realImag g h hg hh] at hpi
  calc
    _ ≤ ∫ z : V d, ‖coordWord d (twoWord d S) g z‖+‖coordWord d (twoWord d S) h z‖ := by
      apply integral_mono hpi (hgi.add hhi)
      intro z
      simpa only [norm_mul,Complex.norm_I,one_mul] using
        norm_add_le (coordWord d (twoWord d S) g z) (Complex.I*coordWord d (twoWord d S) h z)
    _ = _ := integral_add hgi hhi

/-- Actual complex U789 (F) supplier. P is retained explicitly until
the actual phase is licensed by retained-box membership below. -/
theorem exists_actual_complex_fourier_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Source) (N d : ℕ) (width P : ℝ),
      1 ≤ Real.log (N : ℝ) → 0 < width → width ≤ 1 → 0 ≤ P →
      ∀ (owner : Fin d → Fin (rank s)) (U : Fin d → ℝ) (R : Fin (rank s) → ℝ)
        (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
        (phaseOffset : ℝ) (frequency : Fin d → ℝ),
      (∀ a, 0 < U a) → (∀ i, 0 < R i) → (∀ a, |frequency a| ≤ P) → d ≤ 24 →
      let f := complexChart s N width owner U R κ₀ offset child phaseOffset frequency
      mixedD d f ≤ C*(1/width+P)^48 ∧
      (∀ ξ : Fin d → ℝ, ‖physicalFourier d f ξ‖ ≤
        (C*(1/width+P)^48)*productCauchy d ξ) ∧
      (∫ ξ : Fin d → ℝ, ‖physicalFourier d f ξ‖)/frequencyScale^d ≤
        (C*(1/width+P)^48)/2^d ∧
      ∀ H : ℝ, 0 < H → ∀ z : V d,
        ‖f z-truncatedPhysical d f H z‖ ≤ (d : ℝ)*(C*(1/width+P)^48)/H := by
  obtain ⟨C₀,hC₀,hword⟩ := exists_chart_word_budget
  let C : ℝ := 2*dimensionBudget 4*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s N d width P hell hw hwOne hP owner U R κ₀ offset child phaseOffset frequency hU hR hf hd
  let g := realChart s N width owner U R κ₀ offset child phaseOffset frequency 0
  let h := realChart s N width owner U R κ₀ offset child phaseOffset frequency 1
  let f := complexChart s N width owner U R κ₀ offset child phaseOffset frequency
  have hsmooth (part : Fin 2) : ContDiff ℝ ∞
      (realChart s N width owner U R κ₀ offset child phaseOffset frequency part) :=
    euclideanLift_smooth d _ (chart_smooth s N width owner U R κ₀ offset child phaseOffset frequency part)
  have hcompact (part : Fin 2) : HasCompactSupport
      (realChart s N width owner U R κ₀ offset child phaseOffset frequency part) :=
    euclideanLift_compact d _ (chart_compact s N width owner U R κ₀ offset child phaseOffset frequency part)
  have hD (part : Fin 2) : mixedD d
      (realChart s N width owner U R κ₀ offset child phaseOffset frequency part) ≤
        (dimensionBudget 4*C₀)*(1/width+P)^48 := by
    have hlocal := mixedD_euclideanLift_le d
      (chart s N width owner U R κ₀ offset child phaseOffset frequency part)
      (chart_smooth s N width owner U R κ₀ offset child phaseOffset frequency part)
      (chart_compact s N width owner U R κ₀ offset child phaseOffset frequency part)
      (chart_tsupport_box s N width owner U R κ₀ offset child phaseOffset frequency part)
      (C₀*(1/width+P)^48) (by positivity)
      (fun w hlen z => hword s N d width P hell hw hwOne hP owner U R κ₀ offset child
        phaseOffset frequency part hU hR hf hd w z (by omega))
    apply hlocal.trans
    calc
      _ ≤ dimensionBudget 4*(C₀*(1/width+P)^48) :=
        mul_le_mul_of_nonneg_right (dimension_factor_le (by omega : d ≤ 6*4)) (by positivity)
      _ = _ := by ring
  have hbound : mixedD d f ≤ C*(1/width+P)^48 := by
    apply (mixedD_realImag_le g h (hsmooth 0) (hsmooth 1) (hcompact 0) (hcompact 1)).trans
    have hh := add_le_add (hD 0) (hD 1)
    dsimp [C]
    nlinarith
  have hfs : ContDiff ℝ ∞ f := (hsmooth 0).add ((hsmooth 1).const_smul Complex.I)
  have hfc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact ((hcompact 0).isCompact.union (hcompact 1).isCompact)
    intro z hz
    by_cases hg : g z=0
    · right
      apply subset_tsupport h
      intro hh
      have heq : f z=g z+Complex.I*h z := rfl
      exact hz (by rw [heq,hg,hh]; simp)
    · exact Or.inl (subset_tsupport g hg)
  have hp (ξ : Fin d → ℝ) : ‖physicalFourier d f ξ‖ ≤
      (C*(1/width+P)^48)*productCauchy d ξ := by
    apply (physicalFourier_pointwise d f hfs hfc ξ).trans
    apply mul_le_mul_of_nonneg_right hbound
    unfold productCauchy cauchy
    exact Finset.prod_nonneg (fun i hi => by positivity)
  refine ⟨hbound,hp,(physicalFourier_normalized_l1_le d f hfs hfc).trans
    (div_le_div_of_nonneg_right hbound (by positivity)),?_⟩
  intro H hH z
  exact (actual_uniform_truncation_error d f hfs hfc H hH z).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg d)) hH.le)

end
end ImbalancedChen.P3OriginalU789ComplexChartFourier
