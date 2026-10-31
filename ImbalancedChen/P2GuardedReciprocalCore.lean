import ImbalancedChen.P2DirectedEnclosureCore

/-! Exact generic prefix of the legacy reciprocal-rounding facade.
All declaration names, bodies and proofs are moved verbatim. -/
namespace ImbalancedChen.Certificates.P2DirectedLogRounding

def Enclosure.ReciprocalValid (a : Enclosure) : Prop :=
  a.lower ≤ a.upper ∧ (0 < a.lower ∨ a.upper < 0)

instance (a : Enclosure) : Decidable a.ReciprocalValid := by
  unfold Enclosure.ReciprocalValid
  infer_instance

def Enclosure.reciprocalCheck (a : Enclosure) : Bool := decide a.ReciprocalValid

def Enclosure.reciprocalBounds (a : Enclosure) : Enclosure :=
  ⟨1 / a.upper, 1 / a.lower⟩

def Enclosure.checkedReciprocal (a : Enclosure) : Option Enclosure :=
  if a.reciprocalCheck = true then some a.reciprocalBounds else none

/-- Failure is explicit at both zero endpoints and throughout a crossing
interval; division by Lean's totalized zero cannot silently certify it. -/
theorem Enclosure.reciprocalCheck_false_of_crosses_zero (a : Enclosure)
    (hl : a.lower ≤ 0) (hu : 0 ≤ a.upper) : a.reciprocalCheck = false := by
  have hbad : ¬ a.ReciprocalValid := by
    rintro ⟨_, hp | hn⟩
    · exact (not_lt_of_ge hl) hp
    · exact (not_lt_of_ge hu) hn
  simp [Enclosure.reciprocalCheck, hbad]

theorem Enclosure.checkedReciprocal_none_of_crosses_zero (a : Enclosure)
    (hl : a.lower ≤ 0) (hu : 0 ≤ a.upper) : a.checkedReciprocal = none := by
  simp [Enclosure.checkedReciprocal, a.reciprocalCheck_false_of_crosses_zero hl hu]

theorem Enclosure.reciprocal_endpoint_ne_zero (a : Enclosure)
    (hc : a.reciprocalCheck = true) : a.lower ≠ 0 ∧ a.upper ≠ 0 := by
  have hv : a.ReciprocalValid := of_decide_eq_true hc
  rcases hv with ⟨horder, hp | hn⟩
  · exact ⟨ne_of_gt hp, ne_of_gt (hp.trans_le horder)⟩
  · exact ⟨ne_of_lt (horder.trans_lt hn), ne_of_lt hn⟩

theorem Enclosure.reciprocal_width_denominator_pos (a : Enclosure)
    (hc : a.reciprocalCheck = true) : 0 < a.lower * a.upper := by
  have hv : a.ReciprocalValid := of_decide_eq_true hc
  rcases hv with ⟨horder, hp | hn⟩
  · exact mul_pos hp (hp.trans_le horder)
  · exact mul_pos_of_neg_of_neg (horder.trans_lt hn) hn

/-- Reciprocal is decreasing on either sign component separately. -/
theorem Enclosure.reciprocalBounds_contains {a : Enclosure} {x : ℝ}
    (hx : a.Contains x) (hc : a.reciprocalCheck = true) :
    a.reciprocalBounds.Contains (1 / x) := by
  have hv : a.ReciprocalValid := of_decide_eq_true hc
  rcases hv with ⟨_, hp | hn⟩
  · have hpR : (0 : ℝ) < (a.lower : ℝ) := by exact_mod_cast hp
    have hxpos : 0 < x := hpR.trans_le hx.1
    constructor <;> simp only [Enclosure.reciprocalBounds, Rat.cast_div, Rat.cast_one]
    · exact one_div_le_one_div_of_le hxpos hx.2
    · exact one_div_le_one_div_of_le hpR hx.1
  · have hnR : (a.upper : ℝ) < 0 := by exact_mod_cast hn
    have hxneg : x < 0 := hx.2.trans_lt hnR
    constructor <;> simp only [Enclosure.reciprocalBounds, Rat.cast_div, Rat.cast_one]
    · exact one_div_le_one_div_of_neg_of_le hnR hx.2
    · exact one_div_le_one_div_of_neg_of_le hxneg hx.1

theorem Enclosure.checkedReciprocal_sound {a b : Enclosure} {x : ℝ}
    (hx : a.Contains x) (hresult : a.checkedReciprocal = some b) :
    b.Contains (1 / x) := by
  have hc : a.reciprocalCheck = true := by
    by_contra hbad
    simp [Enclosure.checkedReciprocal, hbad] at hresult
  have hb : a.reciprocalBounds = b := by
    simpa [Enclosure.checkedReciprocal, hc] using hresult
  rw [← hb]
  exact Enclosure.reciprocalBounds_contains hx hc

/-- Exact amplification of interval width by inversion.  The sign guard
makes the product in this denominator strictly positive. -/
theorem Enclosure.reciprocal_width (a : Enclosure) (hc : a.reciprocalCheck = true) :
    a.reciprocalBounds.upper - a.reciprocalBounds.lower =
      (a.upper - a.lower) / (a.lower * a.upper) := by
  obtain ⟨hl, hu⟩ := a.reciprocal_endpoint_ne_zero hc
  dsimp only [Enclosure.reciprocalBounds]
  field_simp [hl, hu]

def Enclosure.reciprocalQ80 (a : Enclosure) : Enclosure :=
  a.reciprocalBounds.round 80

theorem Enclosure.reciprocalQ80_contains {a : Enclosure} {x : ℝ}
    (hx : a.Contains x) (hc : a.reciprocalCheck = true) :
    a.reciprocalQ80.Contains (1 / x) := by
  exact Enclosure.round_contains (Enclosure.reciprocalBounds_contains hx hc) 80

/-- Endpoint rounding errors are exact rational statements, not a stored
approximation to a real reciprocal.  Each outward error is below one Q80 ulp. -/
theorem Enclosure.reciprocalQ80_errors (a : Enclosure) :
    (0 ≤ 1 / a.upper - a.reciprocalQ80.lower ∧
      1 / a.upper - a.reciprocalQ80.lower < 1 / dyadicScale 80) ∧
    (0 ≤ a.reciprocalQ80.upper - 1 / a.lower ∧
      a.reciprocalQ80.upper - 1 / a.lower < 1 / dyadicScale 80) := by
  exact ⟨roundDown_error 80 (1 / a.upper), roundUp_error 80 (1 / a.lower)⟩

theorem Enclosure.reciprocalQ80_width (a : Enclosure)
    (hc : a.reciprocalCheck = true) :
    a.reciprocalQ80.upper - a.reciprocalQ80.lower <
      (a.upper - a.lower) / (a.lower * a.upper) + 2 / dyadicScale 80 := by
  have hw := Enclosure.round_width a.reciprocalBounds 80
  rw [a.reciprocal_width hc] at hw
  exact hw

def Enclosure.divisionBounds (a b : Enclosure) : Enclosure :=
  a.mul b.reciprocalBounds

def Enclosure.checkedDivision (a b : Enclosure) : Option Enclosure :=
  if b.reciprocalCheck = true then some (a.divisionBounds b) else none

theorem Enclosure.checkedDivision_none_of_crosses_zero (a b : Enclosure)
    (hl : b.lower ≤ 0) (hu : 0 ≤ b.upper) : a.checkedDivision b = none := by
  simp [Enclosure.checkedDivision, b.reciprocalCheck_false_of_crosses_zero hl hu]

/-- The numerator can have either sign or cross zero; only the denominator
needs a sign-separated guard, because multiplication uses all four corners. -/
theorem Enclosure.divisionBounds_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) (hc : b.reciprocalCheck = true) :
    (a.divisionBounds b).Contains (x / y) := by
  simpa only [Enclosure.divisionBounds, div_eq_mul_inv, one_div, one_mul] using
    Enclosure.mul_contains hx (Enclosure.reciprocalBounds_contains hy hc)

theorem Enclosure.checkedDivision_sound {a b c : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y)
    (hresult : a.checkedDivision b = some c) : c.Contains (x / y) := by
  have hc : b.reciprocalCheck = true := by
    by_contra hbad
    simp [Enclosure.checkedDivision, hbad] at hresult
  have hresult' : a.divisionBounds b = c := by
    simpa [Enclosure.checkedDivision, hc] using hresult
  rw [← hresult']
  exact Enclosure.divisionBounds_contains hx hy hc

def Enclosure.divisionQ80 (a b : Enclosure) : Enclosure :=
  (a.divisionBounds b).round 80

theorem Enclosure.divisionQ80_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) (hc : b.reciprocalCheck = true) :
    (a.divisionQ80 b).Contains (x / y) := by
  exact Enclosure.round_contains (Enclosure.divisionBounds_contains hx hy hc) 80

theorem Enclosure.divisionQ80_errors (a b : Enclosure) :
    (0 ≤ (a.divisionBounds b).lower - (a.divisionQ80 b).lower ∧
      (a.divisionBounds b).lower - (a.divisionQ80 b).lower < 1 / dyadicScale 80) ∧
    (0 ≤ (a.divisionQ80 b).upper - (a.divisionBounds b).upper ∧
      (a.divisionQ80 b).upper - (a.divisionBounds b).upper < 1 / dyadicScale 80) := by
  exact ⟨roundDown_error 80 (a.divisionBounds b).lower,
    roundUp_error 80 (a.divisionBounds b).upper⟩

def Enclosure.clampLower (a : Enclosure) (q : ℚ) : Enclosure :=
  ⟨max q a.lower, max q a.upper⟩

theorem Enclosure.clampLower_contains {a : Enclosure} {x : ℝ}
    (hx : a.Contains x) (q : ℚ) : (a.clampLower q).Contains (max (q : ℝ) x) := by
  constructor <;> simp only [Enclosure.clampLower, Rat.cast_max]
  · exact max_le_max le_rfl hx.1
  · exact max_le_max le_rfl hx.2


end ImbalancedChen.Certificates.P2DirectedLogRounding
