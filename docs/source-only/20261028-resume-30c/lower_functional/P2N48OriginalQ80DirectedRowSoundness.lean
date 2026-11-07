import ImbalancedChen.P2N48ActualGeometricKeyDecoder
import ImbalancedChen.P2N48TermOneAllPatternClosedVolumes

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

Original n48 Q80 method-zero row soundness. The same true ordered-parent
mass Z is used in the baseline and switched upper cost. The exact I-class
operation order is retained: floor(I(K*C).lo * Z.lo / Q), and two ceilings
for (I(K) * raw(omegaHi) * Z).hi. No new numerical endpoints are invented.

The original producer and independent replay save max(0, baselineLo-costHi).
This max matters for zero-floor rows. The earlier un-clamped Phase5 predicate
is a sufficient stronger check, not the literal source predicate.

Actual row massLower soundness is obtained from the real decoded archive
and the existing four tied-volume patterns. The concrete directed log-moment
endpoints, Buchstab mesh-query enclosures and the true omega<=C cap remain
explicit unproved internal/analytic obligations. No large checker is run here.
-/

namespace ImbalancedChen.P2N48OriginalQ80DirectedRowSoundness

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48TiedParentMassReduction P2N48TermOneAllPatternClosedVolumes
open P5Z.U11Integral P5Z.U11Canonical
open P5Z.U1011OriginalSixteenAnchorFeedback
open OriginalPairedN48ArchiveData

def q80 : ℕ := 2 ^ 80

def value (x : ℤ) : ℝ := (x : ℝ) / (q80 : ℝ)

def sourceK : ℚ := 67619 / 10000

def sourceC : ℚ := 70893 / 125000

def roundLo (x : ℚ) : ℤ := ⌊x * (q80 : ℚ)⌋

def roundHi (x : ℚ) : ℤ := ⌈x * (q80 : ℚ)⌉

/-- Original signed integer floor/ceil multiplication at scale Q. -/
def mulLo (x y : ℤ) : ℤ := ⌊((x * y : ℤ) : ℚ) / (q80 : ℚ)⌋

def mulHi (x y : ℤ) : ℤ := ⌈((x * y : ℤ) : ℚ) / (q80 : ℚ)⌉

private theorem q80_pos : (0 : ℝ) < q80 := by norm_num [q80]

private theorem q80_pos_int : (0 : ℤ) < q80 := by norm_num [q80]

private theorem q80_eq_floorScale : (q80 : ℝ) = floorScale := by
  norm_num [q80, floorScale]

/-- The four actual I.__mul__ corner products, before outward rounding. -/
def cornerMin (a b c d : ℤ) : ℤ :=
  min (min (a*c) (a*d)) (min (b*c) (b*d))

def cornerMax (a b c d : ℤ) : ℤ :=
  max (max (a*c) (a*d)) (max (b*c) (b*d))

theorem cornerMin_eq_nonnegative (a b c d : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    cornerMin a b c d = a*c := by
  have hb := ha.trans hab
  rw [cornerMin, min_eq_left (mul_le_mul_of_nonneg_left hcd ha),
    min_eq_left (mul_le_mul_of_nonneg_left hcd hb),
    min_eq_left (mul_le_mul_of_nonneg_right hab hc)]

theorem cornerMax_eq_nonnegative (a b c d : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    cornerMax a b c d = b*d := by
  have hb := ha.trans hab
  have hd := hc.trans hcd
  rw [cornerMax, max_eq_right (mul_le_mul_of_nonneg_left hcd ha),
    max_eq_right (mul_le_mul_of_nonneg_left hcd hb),
    max_eq_right (mul_le_mul_of_nonneg_right hab hd)]

/-- These equations identify the specialized chain below with the source
four-corner interval product; they are not new numerical enclosures. -/
theorem original_I_low_product (a b c d : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    ⌊(cornerMin a b c d : ℚ) / (q80 : ℚ)⌋ = mulLo a c := by
  rw [cornerMin_eq_nonnegative a b c d ha hab hc hcd]
  rfl

theorem original_I_high_product (a b c d : ℤ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    ⌈(cornerMax a b c d : ℚ) / (q80 : ℚ)⌉ = mulHi b d := by
  rw [cornerMax_eq_nonnegative a b c d ha hab hc hcd]
  rfl

/-- The rational floors are exactly Python's signed integer // operator. -/
theorem mulLo_eq_original_ediv (x y : ℤ) :
    mulLo x y = (x * y) / (q80 : ℤ) := by
  unfold mulLo
  simpa using Int.floor_div_cast_of_nonneg (k := ℚ) q80_pos_int.le
    (((x * y : ℤ) : ℚ))

/-- Original ceildiv is -((-n)//Q), also for signed n. -/
theorem mulHi_eq_original_ceildiv (x y : ℤ) :
    mulHi x y = - (-(x * y) / (q80 : ℤ)) := by
  have hceil : ⌈((x * y : ℤ) : ℚ) / (q80 : ℚ)⌉ =
      -⌊-(((x * y : ℤ) : ℚ) / (q80 : ℚ))⌋ := by
    have h := Int.floor_neg (a := ((x * y : ℤ) : ℚ) / (q80 : ℚ))
    omega
  unfold mulHi
  rw [hceil]
  congr 1
  rw [show -(((x * y : ℤ) : ℚ) / (q80 : ℚ)) =
    ((-(x * y) : ℤ) : ℚ) / (q80 : ℚ) by simp only [Int.cast_neg, neg_div]]
  simpa using Int.floor_div_cast_of_nonneg (k := ℚ) q80_pos_int.le
    (((-(x * y) : ℤ) : ℚ))

theorem roundLo_sound (x : ℚ) : value (roundLo x) ≤ (x : ℝ) := by
  have hq := Int.floor_le (x * (q80 : ℚ))
  have hr : (roundLo x : ℝ) ≤ (x : ℝ) * (q80 : ℝ) := by
    exact_mod_cast hq
  apply (div_le_iff₀ q80_pos).2
  exact hr

theorem roundHi_sound (x : ℚ) : (x : ℝ) ≤ value (roundHi x) := by
  have hq := Int.le_ceil (x * (q80 : ℚ))
  have hr : (x : ℝ) * (q80 : ℝ) ≤ (roundHi x : ℝ) := by
    exact_mod_cast hq
  apply (le_div_iff₀ q80_pos).2
  exact hr

theorem mulLo_sound (x y : ℤ) : value (mulLo x y) ≤ value x * value y := by
  have hq := Int.floor_le (((x * y : ℤ) : ℚ) / (q80 : ℚ))
  have hr : (mulLo x y : ℝ) ≤ (x : ℝ) * (y : ℝ) / (q80 : ℝ) := by
    exact_mod_cast hq
  have hd := div_le_div_of_nonneg_right hr q80_pos.le
  calc
    value (mulLo x y) ≤ ((x : ℝ) * (y : ℝ) / q80) / q80 := hd
    _ = value x * value y := by unfold value; ring

theorem mulHi_sound (x y : ℤ) : value x * value y ≤ value (mulHi x y) := by
  have hq := Int.le_ceil (((x * y : ℤ) : ℚ) / (q80 : ℚ))
  have hr : (x : ℝ) * (y : ℝ) / (q80 : ℝ) ≤ (mulHi x y : ℝ) := by
    exact_mod_cast hq
  have hd := div_le_div_of_nonneg_right hr q80_pos.le
  calc
    value x * value y = ((x : ℝ) * (y : ℝ) / q80) / q80 := by
      unfold value
      ring
    _ ≤ value (mulHi x y) := hd

/-- Directed endpoints must be attached to the identical original row,
including its original ordinal and its geometric key. This structure is
an interface for a future literal endpoint payload, not asserted data. -/
structure DirectedPayload where
  originalOrdinal : ℕ
  originalKey : GeometricKey
  massLo : ℤ
  massHi : ℤ
  omegaHi : ℤ

def baselineLo (p : DirectedPayload) : ℤ :=
  mulLo (roundLo (sourceK * sourceC)) p.massLo

def omegaCostHi (p : DirectedPayload) : ℤ :=
  mulHi (mulHi (roundHi sourceK) p.omegaHi) p.massHi

/-- Exact original max(0, sw.lo-omcost.hi), in Q80 units. -/
def literalSavingLo (p : DirectedPayload) : ℤ :=
  max 0 (baselineLo p - omegaCostHi p)

def rowPayloadCheck (r : SourceRow) (p : DirectedPayload) : Bool :=
  decide (p.originalOrdinal = r.ordinal ∧ p.originalKey = rowKey r ∧
    0 ≤ p.massLo ∧ p.massLo ≤ p.massHi ∧ 0 ≤ p.omegaHi ∧
      (r.floorQ : ℤ) ≤ literalSavingLo p)

theorem rowPayloadCheck_sound (r : SourceRow) (p : DirectedPayload)
    (h : rowPayloadCheck r p = true) :
    p.originalOrdinal = r.ordinal ∧ p.originalKey = rowKey r ∧
      0 ≤ p.massLo ∧ p.massLo ≤ p.massHi ∧ 0 ≤ p.omegaHi ∧
        (r.floorQ : ℤ) ≤ literalSavingLo p :=
  of_decide_eq_true h

/-- The first batch's hMass input is derived on the ACTUAL retained rows
from their checked decoder and the real ordered tied-simplex geometry. -/
theorem actual_retained_massLower_sound (r : SourceRow)
    (hr : r ∈ actualRetainedRows) :
    massLower r ≤ parentUnweightedMass (fullParent r) := by
  have hd := decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1
  exact term1_massLower_le_true_parent r hd.1 ⟨hd.2.1, hd.2.2.1⟩

def omegaArgument (v : LogFour) : ℝ :=
  (1 - (v 0 + v 1 + v 2 + v 3)) / v 2

private theorem unweightedDensity_nonneg (r : SourceRow) (v : LogFour)
    (hv : v ∈ fullParent r) : 0 ≤ harmonicDensity v / v 2 := by
  have h0 := row_coordinate_pos r v hv 0
  have h1 := row_coordinate_pos r v hv 1
  have h2 := row_coordinate_pos r v hv 2
  have h3 := row_coordinate_pos r v hv 3
  unfold harmonicDensity
  positivity

theorem true_parent_mass_nonneg (r : SourceRow) :
    0 ≤ parentUnweightedMass (fullParent r) := by
  apply setIntegral_nonneg (measurableSet_fullParent r)
  exact unweightedDensity_nonneg r

/-- A Buchstab bound on the actual row interval is integrated
against the actual ordered mass; no supplied switched-cost bound remains. -/
theorem true_switch_mass_le_scalar_mass (r : SourceRow) (c : ℝ)
    (hOmega : ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ c) :
    parentSwitchedMass (fullParent r) ≤
      c * parentUnweightedMass (fullParent r) := by
  have hp : ∀ v ∈ fullParent r,
      switchBase v * harmonicDensity v ≤ c * (harmonicDensity v / v 2) := by
    intro v hv
    have h := mul_le_mul_of_nonneg_right (hOmega v hv)
      (unweightedDensity_nonneg r v hv)
    convert h using 1 <;>
      simp only [switchBase, switchedKernel, omegaArgument, one_mul] <;> ring
  have h := setIntegral_mono_on (integrable_switch_fullParent r)
    ((integrable_unweightedDensity_fullParent r).const_mul c)
    (measurableSet_fullParent r) hp
  simpa only [parentSwitchedMass, parentUnweightedMass, integral_const_mul] using h

/-- Exact outward baseline product, with the same Z as in the source. -/
theorem directed_baseline_sound (r : SourceRow) (p : DirectedPayload)
    (hLoNonneg : 0 ≤ p.massLo)
    (hMassLo : value p.massLo ≤ parentUnweightedMass (fullParent r)) :
    value (baselineLo p) ≤
      anchorK * omegaCap * parentUnweightedMass (fullParent r) := by
  have hc : value (roundLo (sourceK * sourceC)) ≤ anchorK * omegaCap := by
    simpa [sourceK, sourceC, anchorK, omegaCap] using roundLo_sound (sourceK * sourceC)
  have hl : 0 ≤ value p.massLo := div_nonneg (by exact_mod_cast hLoNonneg) q80_pos.le
  have hkc : 0 ≤ anchorK * omegaCap := by norm_num [anchorK, omegaCap]
  exact (mulLo_sound _ _).trans (mul_le_mul hc hMassLo hl hkc)

/-- Two ceiling operations preserve the literal I(K)*raw(omegaHi)*Z chain. -/
theorem directed_omega_cost_sound (r : SourceRow) (p : DirectedPayload)
    (hOmegaNonneg : 0 ≤ p.omegaHi)
    (hMassHi : parentUnweightedMass (fullParent r) ≤ value p.massHi)
    (hOmega : ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ value p.omegaHi) :
    anchorK * parentSwitchedMass (fullParent r) ≤ value (omegaCostHi p) := by
  have hk : 0 ≤ anchorK := by norm_num [anchorK]
  have hw : 0 ≤ value p.omegaHi :=
    div_nonneg (by exact_mod_cast hOmegaNonneg) q80_pos.le
  have hKhi : anchorK ≤ value (roundHi sourceK) := by
    simpa [sourceK, anchorK] using roundHi_sound sourceK
  have hkw : anchorK * value p.omegaHi ≤
      value (mulHi (roundHi sourceK) p.omegaHi) :=
    (mul_le_mul_of_nonneg_right hKhi hw).trans (mulHi_sound _ _)
  have hmid : 0 ≤ value (mulHi (roundHi sourceK) p.omegaHi) :=
    (mul_nonneg hk hw).trans hkw
  calc
    anchorK * parentSwitchedMass (fullParent r) ≤
        anchorK * (value p.omegaHi * parentUnweightedMass (fullParent r)) :=
      mul_le_mul_of_nonneg_left (true_switch_mass_le_scalar_mass r _ hOmega) hk
    _ = (anchorK * value p.omegaHi) * parentUnweightedMass (fullParent r) := by ring
    _ ≤ value (mulHi (roundHi sourceK) p.omegaHi) * value p.massHi :=
      mul_le_mul hkw hMassHi (true_parent_mass_nonneg r) hmid
    _ ≤ value (omegaCostHi p) := mulHi_sound _ _

/-- Symbolic soundness of the original max-clamped Q80 saved payload.
The true Buchstab cap supplies nonnegative real saving even when the
directed baseline-minus-cost endpoint is negative and stored floor is 0. -/
theorem original_Q80_method_zero_saved_bound (r : SourceRow) (p : DirectedPayload)
    (hcheck : rowPayloadCheck r p = true)
    (hMass : value p.massLo ≤ parentUnweightedMass (fullParent r) ∧
      parentUnweightedMass (fullParent r) ≤ value p.massHi)
    (hOmega : ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ value p.omegaHi)
    (hCap : ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ omegaCap) :
    anchorK * parentSwitchedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  obtain ⟨hOrdinal, hKey, hLo, hLoHi, hOm, hFloor⟩ := rowPayloadCheck_sound r p hcheck
  have hB := directed_baseline_sound r p hLo hMass.1
  have hT := directed_omega_cost_sound r p hOm hMass.2 hOmega
  have hk : 0 ≤ anchorK := by norm_num [anchorK]
  have hTrueCap : anchorK * parentSwitchedMass (fullParent r) ≤
      anchorK * omegaCap * parentUnweightedMass (fullParent r) := by
    have hc := mul_le_mul_of_nonneg_left (true_switch_mass_le_scalar_mass r _ hCap) hk
    simpa only [mul_assoc] using hc
  by_cases hd : 0 ≤ baselineLo p - omegaCostHi p
  · have hFloor' : (r.floorQ : ℤ) ≤ baselineLo p - omegaCostHi p := by
      simpa only [literalSavingLo, max_eq_right hd] using hFloor
    have hFR : (r.floorQ : ℝ) ≤ (baselineLo p : ℝ) - (omegaCostHi p : ℝ) := by
      exact_mod_cast hFloor'
    have hFD := div_le_div_of_nonneg_right hFR q80_pos.le
    have hUnit : (r.floorQ : ℝ) / floorScale ≤
        value (baselineLo p) - value (omegaCostHi p) := by
      simpa only [value, q80_eq_floorScale, sub_div] using hFD
    dsimp [savedParent]
    linarith only [hB, hT, hUnit]
  · have hd' : baselineLo p - omegaCostHi p ≤ 0 := le_of_not_ge hd
    have hZero : r.floorQ = 0 := by
      have hF : (r.floorQ : ℤ) ≤ 0 := by
        simpa only [literalSavingLo, max_eq_left hd'] using hFloor
      omega
    simpa only [savedParent, hZero, Nat.cast_zero, zero_div, sub_zero] using hTrueCap

/-- The actual archive's massLower and geometric ownership are derived,
while concrete log-mass and Buchstab endpoint licences remain inputs.
The full negative-domain uncovered remainder remains explicit. -/
theorem actual_selected_functional_upper_of_original_Q80
    (p : SourceRow → DirectedPayload)
    (hcheck : ∀ r ∈ actualRetainedRows, rowPayloadCheck r (p r) = true)
    (hMass : ∀ r ∈ actualRetainedRows,
      value (p r).massLo ≤ parentUnweightedMass (fullParent r) ∧
        parentUnweightedMass (fullParent r) ≤ value (p r).massHi)
    (hOmega : ∀ r ∈ actualRetainedRows, ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ value (p r).omegaHi)
    (hCap : ∀ r ∈ actualRetainedRows, ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ omegaCap) :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient ≤
      (∑ r ∈ actualRetainedRows,
        savedParent r (parentUnweightedMass (fullParent r))) -
      (∑ r ∈ actualRetainedRows, rowGainLower r) + uncoveredCost actualRetainedRows := by
  apply actual_selected_functional_upper_with_decoded_keys actual_retained_massLower_sound
  intro r hr _ _
  exact original_Q80_method_zero_saved_bound r (p r) (hcheck r hr)
    (hMass r hr) (hOmega r hr) (hCap r hr)

end
end ImbalancedChen.P2N48OriginalQ80DirectedRowSoundness
