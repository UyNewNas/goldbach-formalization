import ImbalancedChen.P3ActualHBChildMixedFourier
import ImbalancedChen.P3SmoothScalarJets
import ImbalancedChen.P5OriginalU789SmoothChartRoughOne
import ImbalancedChen.P5ActualIndependentGroupLogNormalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
SUPPLEMENT / SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
Frozen T06 checkpoint files and metadata are not modified.

Concrete original U7 prime / U7 semiprime / U8 / three U9 source labels.
Their actual margins, productUpper, positive floor, complete support,
source plateau and pre-HB rough insertion are reused from S24 unchanged.
This supplies missing ordinary occurrence derivative bounds, including
real/imaginary affine phases. It adds no abstract Family licence.
The physical productUpper wall retains its log(N) factor; after the HB
log chart this factor cancels the coordinate normalization exactly.

Pins: manuscript9731290e8f53cffda44129906cde6a965eaa869b §§2,4(F),
P3 snapshot5bf9a3b41cdfdb85eb0edabe925ed448a8e3ab3e,
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/
namespace ImbalancedChen.P3OriginalU789AffinePhaseBudget
noncomputable section
open Classical
open scoped BigOperators
open P4B P3AffineTransitionJets P3SmoothScalarJets
open P5OriginalU789SmoothLogSources P5OriginalU789SmoothChartRoughOne
open P5Z.GroupedOccurrenceLogShift P5Z.AllWordAmbientOccurrenceBound
open P5Z.OccurrenceWordFourFactorLeibniz

/-- Padded original wall list; the first eight entries contain precisely
the old margins and zero padding. Entry8 is the complete-product wall. -/
def margins : (s : Source) → (Fin (rank s) → ℝ) → Fin 9 → ℝ
  | .u7Prime, v => ![margin7Three v 0, margin7Three v 1, margin7Three v 2,
      margin7Three v 3, margin7Three v 4, 0, 0, 0, 1-∑ i, v i]
  | .u7Semiprime, v => ![margin7Four v 0, margin7Four v 1, margin7Four v 2,
      margin7Four v 3, margin7Four v 4, margin7Four v 5, 0, 0, 1-∑ i, v i]
  | .u8, v => ![margin8 v 0, margin8 v 1, margin8 v 2, margin8 v 3,
      margin8 v 4, margin8 v 5, 0, 0, 1-∑ i, v i]
  | .u9 b, v => ![margin9 b v 0, margin9 b v 1, margin9 b v 2, margin9 b v 3,
      margin9 b v 4, margin9 b v 5, margin9 b v 6, margin9 b v 7, 1-∑ i, v i]

def row (s : Source) (j : Fin 9) (i : Fin (rank s)) : ℝ :=
  margins s (Pi.single i 1) j-margins s 0 j

/-- The affine identity is derived for the literal original margins,
including all U9 branch permutations, rather than supplied as a field. -/
theorem margins_affine (s : Source) (v : Fin (rank s) → ℝ) (j : Fin 9) :
    margins s v j = margins s 0 j+∑ i, row s j i*v i := by
  cases s with
  | u7Prime =>
      fin_cases j <;> simp [row, margins, rank, margin7Three, Fin.sum_univ_succ] <;> ring
  | u7Semiprime =>
      fin_cases j <;> simp [row, margins, rank, margin7Four, Fin.sum_univ_succ] <;> ring
  | u8 =>
      fin_cases j <;> simp [row, margins, rank, margin8, Fin.sum_univ_succ] <;> ring
  | u9 b =>
      fin_cases b <;> fin_cases j <;>
        simp [row, margins, rank, margin9, original9Log, branch9Margins,
          Fin.sum_univ_succ] <;> ring

theorem row_bound (s : Source) (j : Fin 9) (i : Fin (rank s)) : |row s j i| ≤ 2 := by
  cases s with
  | u7Prime =>
      fin_cases j <;> fin_cases i <;>
        norm_num [row, margins, rank, margin7Three, Fin.sum_univ_succ]
  | u7Semiprime =>
      fin_cases j <;> fin_cases i <;>
        norm_num [row, margins, rank, margin7Four, Fin.sum_univ_succ]
  | u8 =>
      fin_cases j <;> fin_cases i <;>
        norm_num [row, margins, rank, margin8, Fin.sum_univ_succ]
  | u9 b =>
      fin_cases b <;> fin_cases j <;> fin_cases i <;>
        norm_num [row, margins, rank, margin9, original9Log, branch9Margins,
          Fin.sum_univ_succ]

def wallScale (ell : ℝ) (j : Fin 9) : ℝ := if j=8 then ell else 1

def originalProfile : (s : Source) → ℕ → ℝ → (Fin (rank s) → ℝ) → ℝ
  | .u7Prime, N, width => physicalOuter7Three N width
  | .u7Semiprime, N, width => physicalOuter7Four N width
  | .u8, N, width => physicalOuter8 N width
  | .u9 b, N, width => physicalOuter9 b N width

theorem originalProfile_existing_source (s : Source) (N : ℕ) (width : ℝ)
    (u : Fin (rank s) → Fin (N+1)) :
    originalProfile s N width (logPoint u)=sourceWeight s N width u := by
  cases s <;> rfl

theorem originalProfile_smooth (s : Source) (N : ℕ) (width : ℝ) :
    ContDiff ℝ ∞ (originalProfile s N width) := by
  have h := contDiff_physicalOuters N width
  cases s with
  | u7Prime => exact h.1
  | u7Semiprime => exact h.2.1
  | u8 => exact h.2.2.1
  | u9 b => exact h.2.2.2 b

/-- Exact original profile; zero padding contributes one, and only the
physical complete-product wall has the original log(N) scale. -/
theorem originalProfile_eq_gates (s : Source) (N : ℕ) (width : ℝ)
    (hw : 0 < width) (v : Fin (rank s) → ℝ) :
    originalProfile s N width v =
      ∏ j : Fin 9, smoothGateUpperStep width
        (wallScale (Real.log (N : ℝ)) j*margins s v j) := by
  have hz : smoothGateUpperStep width 0 = 1 := smoothGateUpperStep_eq_one hw le_rfl
  cases s <;>
    simp [originalProfile, physicalOuter7Three, physicalOuter7Four, physicalOuter8,
      physicalOuter9, outer7Three, outer7Four, outer8, outer9, productUpper,
      margins, wallScale, Fin.prod_univ_succ, hz, mul_comm]

/-- Genuine HB occurrence-to-original-coordinate logarithmic map. -/
def logCoordinates {d : ℕ} (s : Source) (ell : ℝ) (base : Fin (rank s) → ℝ)
    (owner : Fin d → Fin (rank s)) (z : Fin d → ℝ) : Fin (rank s) → ℝ :=
  fun i => (base i+groupLog owner i z)/ell

theorem margins_logCoordinates {d : ℕ} (s : Source) (ell : ℝ)
    (base : Fin (rank s) → ℝ) (owner : Fin d → Fin (rank s))
    (z : Fin d → ℝ) (j : Fin 9) :
    margins s (logCoordinates s ell base owner z) j =
      margins s (fun i => base i/ell) j+
        ∑ a : Fin d, (row s j (owner a)/ell)*z a := by
  rw [margins_affine, margins_affine]
  simp only [logCoordinates, add_div, mul_add, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin (rank s), row s j i*(groupLog owner i z/ell)) =
        ∑ i : Fin (rank s), ∑ a : Fin d,
          row s j i*((if owner a=i then z a else 0)/ell) := by
      simp only [groupLog, Finset.sum_div, Finset.mul_sum]
    _ = ∑ a : Fin d, ∑ i : Fin (rank s),
          row s j i*((if owner a=i then z a else 0)/ell) := Finset.sum_comm
    _ = ∑ a : Fin d, (row s j (owner a)/ell)*z a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [ite_div, zero_div, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      ring

def trig (part : Fin 2) : ℝ → ℝ := if part=0 then Real.cos else Real.sin

def phaseProfile {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (base : Fin (rank s) → ℝ) (owner : Fin d → Fin (rank s))
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) (z : Fin d → ℝ) : ℝ :=
  originalProfile s N width (logCoordinates s (Real.log (N : ℝ)) base owner z) *
    trig part (phaseOffset+∑ a, frequency a*z a)

theorem phaseProfile_smooth {d : ℕ} (s : Source) (N : ℕ) (width : ℝ)
    (base : Fin (rank s) → ℝ) (owner : Fin d → Fin (rank s))
    (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2) :
    ContDiff ℝ ∞ (phaseProfile s N width base owner phaseOffset frequency part) := by
  have hg : ContDiff ℝ ∞ (fun z => logCoordinates s (Real.log (N : ℝ)) base owner z) := by
    unfold logCoordinates groupLog
    fun_prop
  have hp : ContDiff ℝ ∞ (fun z : Fin d → ℝ =>
      trig part (phaseOffset+∑ a, frequency a*z a)) := by
    fin_cases part <;> simp only [trig, if_true, if_false] <;> fun_prop
  exact ((originalProfile_smooth s N width).comp hg).mul hp

/-- Only the EXISTING scalar jet interpretation is used. -/
def scalar (kind : Fin 3) : ℝ → ℝ :=
  if kind=0 then Real.smoothTransition else if kind=1 then Real.cos else Real.sin

theorem scalar_smooth (kind : Fin 3) : ContDiff ℝ ∞ (scalar kind) := by
  fin_cases kind <;> simp only [scalar, if_true, if_false] <;> fun_prop

theorem scalar_global_budget (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ kind u, |iteratedDeriv n (scalar kind) u| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_smoothTransition_global_derivative_bound n
  refine ⟨C, hC, ?_⟩
  intro kind u
  fin_cases kind
  · simpa [scalar] using hb u
  · simpa [scalar] using (Real.abs_iteratedDeriv_cos_le_one n u).trans hC
  · simpa [scalar] using (Real.abs_iteratedDeriv_sin_le_one n u).trans hC

def expression (d : ℕ) : Expr (Fin 10) d :=
  .mul (.step 0 0) (.mul (.step 1 0) (.mul (.step 2 0) (.mul (.step 3 0)
    (.mul (.step 4 0) (.mul (.step 5 0) (.mul (.step 6 0) (.mul (.step 7 0)
      (.mul (.step 8 0) (.step 9 0))))))))

def kinds (part : Fin 2) (j : Fin 10) : Fin 3 :=
  if j=9 then if part=0 then 1 else 2 else 0

def offsets (s : Source) (ell width : ℝ) (base : Fin (rank s) → ℝ)
    (phaseOffset : ℝ) (j : Fin 10) : ℝ :=
  if h : j.val<9 then
    1+wallScale ell ⟨j.val,h⟩*margins s (fun i => base i/ell) ⟨j.val,h⟩/width
  else phaseOffset

def slopes {d : ℕ} (s : Source) (ell width S : ℝ)
    (owner : Fin d → Fin (rank s)) (frequency : Fin d → ℝ)
    (j : Fin 10) (a : Fin d) : ℝ :=
  if h : j.val<9 then
    (wallScale ell ⟨j.val,h⟩*row s ⟨j.val,h⟩ (owner a)/ell)/(width*S)
  else frequency a/S

/-- Exact expression conversion, retaining every original wall and the
actual affine complex phase through its real/imaginary parts. -/
theorem phaseProfile_eq_expression {d : ℕ} (s : Source) (N : ℕ) (width P : ℝ)
    (hell : 1 ≤ Real.log (N : ℝ)) (hw : 0 < width) (hP : 0 ≤ P) (base : Fin (rank s) → ℝ)
    (owner : Fin d → Fin (rank s)) (phaseOffset : ℝ)
    (frequency : Fin d → ℝ) (part : Fin 2) :
    phaseProfile s N width base owner phaseOffset frequency part =
      evalS (scalar ∘ kinds part)
        (offsets s (Real.log (N : ℝ)) width base phaseOffset)
        (slopes s (Real.log (N : ℝ)) width (1/width+P) owner frequency)
        (1/width+P) (expression d) := by
  have hS : 1/width+P ≠ 0 := (add_pos_of_pos_of_nonneg (one_div_pos.mpr hw) hP).ne'
  have hlogne : Real.log (N : ℝ) ≠ 0 := (zero_lt_one.trans_le hell).ne'
  have hgate (j : Fin 9) (z : Fin d → ℝ) :
      affine (offsets s (Real.log (N : ℝ)) width base phaseOffset)
        (slopes s (Real.log (N : ℝ)) width (1/width+P) owner frequency)
        (1/width+P) ⟨j.val,by omega⟩ z =
      1+(wallScale (Real.log (N : ℝ)) j*
        margins s (logCoordinates s (Real.log (N : ℝ)) base owner z) j)/width := by
    rw [margins_logCoordinates]
    simp only [affine, offsets, slopes, j.isLt, dite_true]
    simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    field_simp [hw.ne', hS, hlogne]
    ring
  have hphase (z : Fin d → ℝ) :
      affine (offsets s (Real.log (N : ℝ)) width base phaseOffset)
        (slopes s (Real.log (N : ℝ)) width (1/width+P) owner frequency)
        (1/width+P) 9 z = phaseOffset+∑ a, frequency a*z a := by
    simp only [affine, offsets, slopes, show ¬((9 : Fin 10).val<9) by omega,
      dite_false]
    simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.sum_mul]
    field_simp [hS]
  funext z
  rw [phaseProfile, originalProfile_eq_gates s N width hw]
  simp only [expression, evalS, iteratedDeriv_zero, Function.comp_apply]
  have hg (j : Fin 9) :
      scalar (kinds part ⟨j.val,by omega⟩)
        (affine (offsets s (Real.log (N : ℝ)) width base phaseOffset)
          (slopes s (Real.log (N : ℝ)) width (1/width+P) owner frequency)
          (1/width+P) ⟨j.val,by omega⟩ z) =
      smoothGateUpperStep width (wallScale (Real.log (N : ℝ)) j*
        margins s (logCoordinates s (Real.log (N : ℝ)) base owner z) j) := by
    rw [hgate]
    simp [kinds, scalar, smoothGateUpperStep, show (⟨j.val,by omega⟩ : Fin 10) ≠ 9 by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega]
  have hp : scalar (kinds part 9)
      (affine (offsets s (Real.log (N : ℝ)) width base phaseOffset)
        (slopes s (Real.log (N : ℝ)) width (1/width+P) owner frequency)
        (1/width+P) 9 z) = trig part (phaseOffset+∑ a, frequency a*z a) := by
    rw [hphase]
    fin_cases part <;> simp [kinds, scalar, trig]
  simp only [Fin.prod_univ_succ]
  rw [← hg 0, ← hg 1, ← hg 2, ← hg 3, ← hg 4, ← hg 5, ← hg 6, ← hg 7, ← hg 8, ← hp]
  ring

theorem slopes_bound {d : ℕ} (s : Source) (ell width P : ℝ)
    (hell : 1 ≤ ell) (hw : 0 < width) (hP : 0 ≤ P)
    (owner : Fin d → Fin (rank s)) (frequency : Fin d → ℝ)
    (hf : ∀ a, |frequency a| ≤ P) (j : Fin 10) (a : Fin d) :
    |slopes s ell width (1/width+P) owner frequency j a| ≤ 2 := by
  have hell0 : 0 < ell := zero_lt_one.trans_le hell
  have hS : 0 < 1/width+P := add_pos_of_pos_of_nonneg (one_div_pos.mpr hw) hP
  by_cases hj : j.val<9
  · have hscale0 : 0 ≤ wallScale ell ⟨j.val,hj⟩ := by
      unfold wallScale; split_ifs <;> positivity
    have hscale : wallScale ell ⟨j.val,hj⟩ ≤ ell := by
      unfold wallScale; split_ifs <;> first | exact le_rfl | exact hell
    have hr := row_bound s ⟨j.val,hj⟩ (owner a)
    have hnum : |wallScale ell ⟨j.val,hj⟩*row s ⟨j.val,hj⟩ (owner a)/ell| ≤ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hscale0, abs_of_pos hell0]
      apply (div_le_iff₀ hell0).mpr
      have h := mul_le_mul hscale hr (abs_nonneg _) hell0.le
      nlinarith
    have hden : 1 ≤ width*(1/width+P) := by
      rw [mul_add, mul_one_div_cancel hw.ne']
      nlinarith [mul_nonneg hw.le hP]
    simp only [slopes, hj, dite_true, abs_div, abs_of_pos (mul_pos hw hS)]
    apply (div_le_iff₀ (mul_pos hw hS)).mpr
    nlinarith
  · simp only [slopes, hj, dite_false, abs_div, abs_of_pos hS]
    apply (div_le_iff₀ hS).mpr
    have h := hf a
    linarith [(one_div_pos.mpr hw)]

/-- Necessary conversion between the two existing coordinate APIs.
No derivative theorem is re-created: their coordinate curves coincide. -/
theorem mixed_eq_occWord {d : ℕ} (w : List (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    mixed w f = occWord w f := by
  have hs (x : Fin d → ℝ) (i : Fin d) (t : ℝ) : shift x i t=x+Pi.single i t := by
    funext a
    by_cases h : a=i <;> simp [shift, h, Pi.single_apply]
  induction w with
  | nil => rfl
  | cons i w ih =>
      change coordinateDeriv i (mixed w f) = occOne i (occWord w f)
      rw [ih]
      funext x
      simp only [coordinateDeriv, occOne, hs]

/-- One genuine pre-N/source/width/phase constant. The six original
source labels and every actual owner map through24 slots are included.
The phase radius P remains visible; it is not a Fourier-volume charge. -/
theorem exists_actual_phase_word_budget :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : Source) (N d : ℕ) (width P : ℝ),
      1 ≤ Real.log (N : ℝ) → 0 < width → width ≤ 1 → 0 ≤ P →
      ∀ (base : Fin (rank s) → ℝ) (owner : Fin d → Fin (rank s))
        (phaseOffset : ℝ) (frequency : Fin d → ℝ) (part : Fin 2),
      (∀ a, |frequency a| ≤ P) → d ≤ 24 →
      ∀ (w : List (Fin d)) (z : Fin d → ℝ), w.length ≤ 48 →
      |occWord w (phaseProfile s N width base owner phaseOffset frequency part) z| ≤
        C*(1/width+P)^48 := by
  have hh (p : Fin 25 × Fin 49) := exists_family_mixed_boundS scalar scalar_smooth
    scalar_global_budget (fun _ : Unit => expression p.1.val) p.2.val 2 (by norm_num)
  choose c hc hb using hh
  let C : ℝ := 1+∑ p : Fin 25 × Fin 49, c p
  have hc0 (p : Fin 25 × Fin 49) : 0 ≤ c p := zero_le_one.trans (hc p)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s N d width P hell hw hwOne hP base owner phaseOffset frequency part hf hd w z hword
  let p : Fin 25 × Fin 49 := (⟨d,by omega⟩,⟨w.length,by omega⟩)
  have hlist : List.ofFn (fun i : Fin w.length => w[i])=w := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'; simp
  have h := hb p (kinds part) (offsets s (Real.log (N : ℝ)) width base phaseOffset)
    (slopes s (Real.log (N : ℝ)) width (1/width+P) owner frequency)
    (slopes_bound s _ width P hell hw hP owner frequency hf)
    (1/width+P) (by positivity) () (fun i : Fin w.length => w[i]) z
  rw [hlist, mixed_eq_occWord, ← phaseProfile_eq_expression s N width P hell hw hP] at h
  have hS : 1 ≤ 1/width+P := by
    have hi : 1 ≤ 1/width := (le_div_iff₀ hw).mpr (by simpa using hwOne)
    linarith
  have hconst : c p ≤ C :=
    (Finset.single_le_sum (fun q _ => hc0 q) (Finset.mem_univ p)).trans
      (by dsimp [C]; linarith)
  exact h.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS hword) (hc0 p)).trans
    (mul_le_mul_of_nonneg_right hconst (by positivity)))

end
end ImbalancedChen.P3OriginalU789AffinePhaseBudget
