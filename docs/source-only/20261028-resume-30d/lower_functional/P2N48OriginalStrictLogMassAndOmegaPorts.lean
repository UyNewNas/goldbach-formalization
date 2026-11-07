import ImbalancedChen.P2N48OriginalQ80DirectedRowSoundness
import ImbalancedChen.P2DirectedLogRounding
import ImbalancedChen.Part5OriginalOmegaGridCore

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The actual strict high-band n48 parent has the original ordered_weights
logarithmic Z formula. Three individual rational-log certificates and
finite payload containment supply its directed mass endpoints. There is
no caller-supplied Z-enclosure, hBaseline or hOmegaCost in the final row
consumer. The tied z-moment cases are not replaced by a symmetry factor.

For every high-band parent, the original un-clipped rational omega query
contains the actual switched argument. The existing original Bernstein
OmegaCoverCertificate supplies the query and cap bounds from finite
checks; no new Buchstab theorem or alternative node recurrence is made.

No row payload, log check, Bernstein check, numerical row or compiler is
executed. The actual tied weighted moments and full retained cover remain
separate OPEN internal obligations.
-/

namespace ImbalancedChen.P2N48OriginalStrictLogMassAndOmegaPorts

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Interval
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48OriginalQ80DirectedRowSoundness
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P5Z.U11Integral P5Z.U11Canonical
open Certificates.P2DirectedLogRounding
open Certificates.SavedParent394700ActualBuchstabSourceOnly (OmegaCoverCertificate)

/-- Exactly the original rational n48 coordinate endpoints. -/
def lowerQ (r : SourceRow) (j : Fin 4) : ℚ := (leftEnd r j : ℚ) / 240000

def upperQ (r : SourceRow) (j : Fin 4) : ℚ := (rightEnd r j : ℚ) / 240000

theorem lowerQ_cast (r : SourceRow) (j : Fin 4) :
    (lowerQ r j : ℝ) = rowLower r j := by simp [lowerQ, rowLower]

theorem upperQ_cast (r : SourceRow) (j : Fin 4) :
    (upperQ r j : ℝ) = rowUpper r j := by simp [upperQ, rowUpper]

private theorem leftEnd_pos (r : SourceRow) (j : Fin 4) : 0 < leftEnd r j := by
  unfold leftEnd
  split_ifs <;> simp only [lowLo, highLo] <;> omega

theorem rowLower_pos (r : SourceRow) (j : Fin 4) : 0 < rowLower r j :=
  div_pos (by exact_mod_cast leftEnd_pos r j) (by norm_num)

theorem rowLower_le_upper (r : SourceRow) (j : Fin 4) :
    rowLower r j ≤ rowUpper r j := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 240000)
  exact_mod_cast (show leftEnd r j ≤ rightEnd r j by unfold rightEnd; omega)

/-- In the strict-bin case, every point of the original half-open box
already satisfies the actual high-band physical ordering and endpoints. -/
theorem strict_fullParent_eq_nativeBox (r : SourceRow) (ht : r.term.val = 1)
    (h12 : r.iz < r.iy) (h23 : r.iw < r.iz) :
    fullParent r = nativeBox r := by
  apply Set.Subset.antisymm (fun _ h => h.1)
  intro v hv
  have hb := mem_logPrimeBox.mp hv
  have h32 := separated_coords_23 r h23 v hv
  have h21 := separated_coords_12 r h12 v hv
  have hlow3 : (417/5000 : ℝ) ≤ v 3 := by
    have h := (hb 3).1
    have hi : (0 : ℝ) ≤ r.iw.val := Nat.cast_nonneg _
    dsimp [leftEnd, lowLo] at h
    norm_num at h ⊢
    linarith
  have hu1 : v 1 < (19/125 : ℝ) := by
    have h := (hb 1).2
    have hi : (r.iy.val : ℝ) ≤ 47 := by exact_mod_cast (show r.iy.val ≤ 47 by omega)
    dsimp [rightEnd, leftEnd, lowLo, width] at h
    norm_num at h ⊢
    linarith
  have hl0 : (19/125 : ℝ) ≤ v 0 := by
    have h := (hb 0).1
    have hi : (0 : ℝ) ≤ r.ix.val := Nat.cast_nonneg _
    simp only [leftEnd, if_pos rfl, if_neg (by omega : r.term.val ≠ 0), highLo] at h
    norm_num at h ⊢
    linarith
  have hu0 : v 0 < (59/250 : ℝ) := by
    have h := (hb 0).2
    have hi : (r.ix.val : ℝ) ≤ 47 := by exact_mod_cast (show r.ix.val ≤ 47 by omega)
    simp only [rightEnd, leftEnd, if_pos rfl, if_neg (by omega : r.term.val ≠ 0),
      highLo, width, ht, and_self, if_true] at h
    norm_num at h ⊢
    linarith
  have hd : v ∈ originalDomain ∅ := ⟨hlow3, h32, h21, hu1, hl0, hu0, by simp⟩
  simpa [fullParent, ht] using And.intro hv hd

private theorem integrableOn_inv_sq_Ico {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / x^2) (Ico a b) := by
  have hc : ContinuousOn (fun x : ℝ => 1 / x^2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ha.trans_le hx.1).ne')
  exact hc.integrableOn_Icc.mono_set Ico_subset_Icc_self

private theorem integral_inv_sq_Ico {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Ico a b, 1 / x^2) = 1/a - 1/b := by
  let F : ℝ → ℝ := fun x => -(1/x)
  have hc : ContinuousOn (fun x : ℝ => 1 / x^2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ha.trans_le hx.1).ne')
  have hd : ∀ x ∈ uIcc a b, HasDerivAt F (1/x^2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    have h := (((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0).neg)
    apply h.congr_deriv
    dsimp
    ring
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hab)]
  dsimp [F]
  ring

def strictZ (r : SourceRow) : ℝ :=
  Real.log (rowUpper r 0 / rowLower r 0) *
    Real.log (rowUpper r 1 / rowLower r 1) *
      (1 / rowLower r 2 - 1 / rowUpper r 2) *
        Real.log (rowUpper r 3 / rowLower r 3)

private def coordinateKernel (j : Fin 4) (x : ℝ) : ℝ :=
  if j = 2 then 1/x^2 else 1/x

/-- The extra distinguished 1/z is evaluated at slot 2. There is no
factorial symmetry argument for this nonsymmetric weighted moment. -/
theorem strict_true_mass_eq_log_formula (r : SourceRow) (ht : r.term.val = 1)
    (h12 : r.iz < r.iy) (h23 : r.iw < r.iz) :
    parentUnweightedMass (fullParent r) = strictZ r := by
  have heq : (fun v : LogFour => harmonicDensity v / v 2) =
      (fun v => ∏ j : Fin 4, coordinateKernel j (v j)) := by
    funext v
    simp [coordinateKernel, Fin.prod_univ_four, harmonicDensity, pow_two,
      one_div, mul_inv_rev, div_eq_mul_inv] <;> ring
  have hi (j : Fin 4) : IntegrableOn (coordinateKernel j)
      (Ico (rowLower r j) (rowUpper r j)) := by
    by_cases hj : j = 2
    · simpa [coordinateKernel, hj] using integrableOn_inv_sq_Ico
        (b := rowUpper r j) (rowLower_pos r j)
    · simpa [coordinateKernel, hj] using
        integrableOn_one_div_Ico (rowUpper r j) (rowLower_pos r j)
  calc
    parentUnweightedMass (fullParent r) =
        ∫ v in nativeBox r, ∏ j : Fin 4, coordinateKernel j (v j) := by
      rw [parentUnweightedMass, strict_fullParent_eq_nativeBox r ht h12 h23, heq]
    _ = ∏ j : Fin 4, ∫ x in Ico (rowLower r j) (rowUpper r j), coordinateKernel j x := by
      unfold nativeBox logPrimeBox
      rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
      rfl
    _ = strictZ r := by
      simp only [Fin.prod_univ_four, coordinateKernel, if_pos rfl,
        show (0 : Fin 4) ≠ 2 by decide, show (1 : Fin 4) ≠ 2 by decide,
        show (3 : Fin 4) ≠ 2 by decide, if_false]
      rw [integral_one_div_Ico (rowLower_pos r 0) (rowLower_le_upper r 0),
        integral_one_div_Ico (rowLower_pos r 1) (rowLower_le_upper r 1),
        integral_inv_sq_Ico (rowLower_pos r 2) (rowLower_le_upper r 2),
        integral_one_div_Ico (rowLower_pos r 3) (rowLower_le_upper r 3)]
      simp only [strictZ] <;> ring

def logArgument (r : SourceRow) (j : Fin 4) : ℚ := upperQ r j / lowerQ r j

structure StrictLogPayload where
  tLog : Certificates.RationalLogCertificate
  uLog : Certificates.RationalLogCertificate
  wLog : Certificates.RationalLogCertificate

/-- This finite check contains only the three original positive rational
log queries and their pre-existing scalar logarithm certificates. -/
def strictLogCheck (r : SourceRow) (d : StrictLogPayload) : Bool :=
  decide (d.tLog.argument = logArgument r 0 ∧ d.tLog.check = true ∧
    d.uLog.argument = logArgument r 1 ∧ d.uLog.check = true ∧
    d.wLog.argument = logArgument r 3 ∧ d.wLog.check = true)

def strictMassExpr (r : SourceRow) (d : StrictLogPayload) : Expr :=
  .rounded 80 (.mul
    (.rounded 80 (.mul
      (.rounded 80 (.mul (.logarithm d.tLog) (.logarithm d.uLog)))
      (.rounded 80 (.rational (1/lowerQ r 2 - 1/upperQ r 2)))))
    (.logarithm d.wLog))

theorem strictMassExpr_sound (r : SourceRow) (d : StrictLogPayload)
    (hcheck : strictLogCheck r d = true) :
    (strictMassExpr r d).enclosure.Contains (strictZ r) := by
  obtain ⟨htArg, htLog, huArg, huLog, hwArg, hwLog⟩ :=
    of_decide_eq_true hcheck
  have hvalid : (strictMassExpr r d).Valid := by
    exact ⟨⟨⟨htLog, huLog⟩, trivial⟩, hwLog⟩
  have h := Expr.enclosure_sound (strictMassExpr r d) hvalid
  have heval : (strictMassExpr r d).eval = strictZ r := by
    simp only [strictMassExpr, Expr.eval, htArg, huArg, hwArg, logArgument,
      Rat.cast_div, Rat.cast_one, Rat.cast_sub, lowerQ_cast, upperQ_cast, strictZ]
  rw [heval] at h
  exact h

/-- Endpoint containment is a finite rational comparison against the
existing payload; it is not a caller-supplied real integral enclosure. -/
def strictMassPayloadCheck (r : SourceRow) (d : StrictLogPayload)
    (p : DirectedPayload) : Bool :=
  strictLogCheck r d && decide (
    (p.massLo : ℚ)/(q80 : ℚ) ≤ (strictMassExpr r d).enclosure.lower ∧
    (strictMassExpr r d).enclosure.upper ≤ (p.massHi : ℚ)/(q80 : ℚ))

theorem actual_strict_mass_endpoints (r : SourceRow) (ht : r.term.val = 1)
    (h12 : r.iz < r.iy) (h23 : r.iw < r.iz)
    (d : StrictLogPayload) (p : DirectedPayload)
    (hcheck : strictMassPayloadCheck r d p = true) :
    value p.massLo ≤ parentUnweightedMass (fullParent r) ∧
      parentUnweightedMass (fullParent r) ≤ value p.massHi := by
  have hh := Bool.and_eq_true.mp hcheck
  have he := strictMassExpr_sound r d hh.1
  have hrat : (p.massLo : ℚ)/(q80 : ℚ) ≤ (strictMassExpr r d).enclosure.lower ∧
      (strictMassExpr r d).enclosure.upper ≤ (p.massHi : ℚ)/(q80 : ℚ) :=
    of_decide_eq_true hh.2
  have hlo : value p.massLo ≤ ((strictMassExpr r d).enclosure.lower : ℝ) := by
    exact_mod_cast hrat.1
  have hhi : ((strictMassExpr r d).enclosure.upper : ℝ) ≤ value p.massHi := by
    exact_mod_cast hrat.2
  rw [strict_true_mass_eq_log_formula r ht h12 h23]
  exact ⟨hlo.trans he.1, he.2.trans hhi⟩

/-- Literal original omega argument bounds, before any mesh conversion. -/
def rawQueryLower (r : SourceRow) : ℚ :=
  (1 - (upperQ r 0 + upperQ r 1 + upperQ r 2 + upperQ r 3)) / upperQ r 2

def rawQueryUpper (r : SourceRow) : ℚ :=
  (1 - (lowerQ r 0 + lowerQ r 1 + lowerQ r 2 + lowerQ r 3)) / lowerQ r 2

/-- Applies to every high-band row, including ALL tied patterns. -/
theorem actual_raw_query_contains (r : SourceRow) (ht : r.term.val = 1)
    {v : LogFour} (hv : v ∈ fullParent r) :
    omegaArgument v ∈ Icc (rawQueryLower r : ℝ) (rawQueryUpper r : ℝ) := by
  have hb := mem_logPrimeBox.mp hv.1
  have hd : v ∈ originalDomain ∅ := by simpa [fullParent, ht] using hv.2
  have hsD := originalDomain_argument_mem ∅ v hd
  have hz := row_coordinate_pos r v hv 2
  have hl := rowLower_pos r 2
  have hu := rowUpper_pos r 2
  have hzl : rowLower r 2 ≤ v 2 := (hb 2).1
  have hzu : v 2 ≤ rowUpper r 2 := (hb 2).2.le
  let n : ℝ := 1 - (v 0 + v 1 + v 2 + v 3)
  let l : ℝ := 1 - (rowUpper r 0 + rowUpper r 1 + rowUpper r 2 + rowUpper r 3)
  let u : ℝ := 1 - (rowLower r 0 + rowLower r 1 + rowLower r 2 + rowLower r 3)
  have hln : l ≤ n := by
    dsimp [l, n]
    linarith only [(hb 0).2, (hb 1).2, (hb 2).2, (hb 3).2]
  have hnu : n ≤ u := by
    dsimp [n, u]
    linarith only [(hb 0).1, (hb 1).1, (hb 2).1, (hb 3).1]
  have hn : 0 ≤ n := by
    have hs : (0 : ℝ) ≤ n / v 2 := (by norm_num : (0 : ℝ) ≤ 2).trans hsD.1
    simpa only [zero_mul] using (le_div_iff₀ hz).mp hs
  have hu0 : 0 ≤ u := hn.trans hnu
  have hlo : l / rowUpper r 2 ≤ n / v 2 := by
    by_cases hl0 : 0 ≤ l
    · exact (div_le_div_of_nonneg_left hl0 hz hzu).trans
        (div_le_div_of_nonneg_right hln hz.le)
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hl0) hu.le).trans
        (div_nonneg hn hz.le)
  have hhi : n / v 2 ≤ u / rowLower r 2 :=
    (div_le_div_of_nonneg_right hnu hz.le).trans
      (div_le_div_of_nonneg_left hu0 hl hzl)
  simpa only [omegaArgument, rawQueryLower, rawQueryUpper, Rat.cast_div,
    Rat.cast_sub, Rat.cast_one, Rat.cast_add, lowerQ_cast, upperQ_cast, n, l, u] using
    And.intro hlo hhi

private theorem original_scale_eq_q80 :
    (Certificates.SavedParent394700ActualBuchstabSourceOnly.scale : ℝ) = (q80 : ℝ) := by
  norm_num [Certificates.SavedParent394700ActualBuchstabSourceOnly.scale, q80]

def omegaPayloadCheck (r : SourceRow) (p : DirectedPayload) (c : OmegaCoverCertificate) : Bool :=
  c.check (rawQueryLower r) (rawQueryUpper r) && decide (c.numerator ≤ p.omegaHi)

def omegaCapCheck (r : SourceRow) (c : OmegaCoverCertificate) : Bool :=
  c.check (rawQueryLower r) (rawQueryUpper r) && decide (
    (c.numerator : ℚ) /
      Certificates.SavedParent394700ActualBuchstabSourceOnly.scale ≤ sourceC)

/-- Both premises are finite original Bernstein cover/numerator checks.
No real omega-enclosure premise is exposed. -/
theorem actual_omega_payload_bound (r : SourceRow) (ht : r.term.val = 1)
    (p : DirectedPayload) (c : OmegaCoverCertificate)
    (hcheck : omegaPayloadCheck r p c = true) :
    ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ value p.omegaHi := by
  have hh := Bool.and_eq_true.mp hcheck
  have hnum : c.numerator ≤ p.omegaHi := of_decide_eq_true hh.2
  have hR : (c.numerator : ℝ)/(q80 : ℝ) ≤ value p.omegaHi :=
    div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
  intro v hv
  have hb := c.check_sound _ _ hh.1 (actual_raw_query_contains r ht hv)
  rw [original_scale_eq_q80] at hb
  exact hb.trans hR

theorem actual_omega_cap_bound (r : SourceRow) (ht : r.term.val = 1)
    (c : OmegaCoverCertificate) (hcheck : omegaCapCheck r c = true) :
    ∀ v ∈ fullParent r,
      LiLiuPrereqBuchstab.buchstab (omegaArgument v) ≤ omegaCap := by
  have hh := Bool.and_eq_true.mp hcheck
  have hnum : (c.numerator : ℚ) /
      Certificates.SavedParent394700ActualBuchstabSourceOnly.scale ≤ sourceC :=
    of_decide_eq_true hh.2
  have hR : (c.numerator : ℝ) /
      Certificates.SavedParent394700ActualBuchstabSourceOnly.scale ≤ omegaCap := by
    have hr : (c.numerator : ℝ) /
        Certificates.SavedParent394700ActualBuchstabSourceOnly.scale ≤ (sourceC : ℝ) := by
      exact_mod_cast hnum
    simpa [sourceC, omegaCap] using hr
  intro v hv
  exact (c.check_sound _ _ hh.1 (actual_raw_query_contains r ht hv)).trans hR

/-- The two former directed ports are supplied from the real strict-row
mass formula plus scalar log/Bernstein certificate checks. -/
theorem actual_strict_directed_ports (r : SourceRow) (hr : r ∈ actualRetainedRows)
    (h12 : r.iz < r.iy) (h23 : r.iw < r.iz)
    (d : StrictLogPayload) (p : DirectedPayload) (c : OmegaCoverCertificate)
    (hrow : rowPayloadCheck r p = true)
    (hMass : strictMassPayloadCheck r d p = true)
    (hOmega : omegaPayloadCheck r p c = true) :
    value (baselineLo p) ≤ anchorK * omegaCap * parentUnweightedMass (fullParent r) ∧
      anchorK * parentSwitchedMass (fullParent r) ≤ value (omegaCostHi p) := by
  have ht := (decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1).1
  have hZ := actual_strict_mass_endpoints r ht h12 h23 d p hMass
  obtain ⟨_, _, hLo, _, hOm, _⟩ := rowPayloadCheck_sound r p hrow
  exact ⟨directed_baseline_sound r p hLo hZ.1,
    directed_omega_cost_sound r p hOm hZ.2 (actual_omega_payload_bound r ht p c hOmega)⟩

/-- Actual original strict-row Q80 soundness now consumes scalar log and
Bernstein finite checks, not Z/hBaseline/hOmegaCost real conclusions.
Tied row weighted formulas and successful finite checks remain pending. -/
theorem actual_strict_row_saved_bound (r : SourceRow) (hr : r ∈ actualRetainedRows)
    (h12 : r.iz < r.iy) (h23 : r.iw < r.iz)
    (d : StrictLogPayload) (p : DirectedPayload)
    (cOmega cCap : OmegaCoverCertificate)
    (hrow : rowPayloadCheck r p = true)
    (hMass : strictMassPayloadCheck r d p = true)
    (hOmega : omegaPayloadCheck r p cOmega = true)
    (hCap : omegaCapCheck r cCap = true) :
    anchorK * parentSwitchedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  have ht := (decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1).1
  exact original_Q80_method_zero_saved_bound r p hrow
    (actual_strict_mass_endpoints r ht h12 h23 d p hMass)
    (actual_omega_payload_bound r ht p cOmega hOmega)
    (actual_omega_cap_bound r ht cCap hCap)

/-- The real same-mask original-sixteen row cost receives the derived
saved bound and the already proved actual massLower licence. -/
theorem actual_strict_row_current_cost (r : SourceRow) (hr : r ∈ actualRetainedRows)
    (h12 : r.iz < r.iy) (h23 : r.iw < r.iz)
    (d : StrictLogPayload) (p : DirectedPayload)
    (cOmega cCap : OmegaCoverCertificate)
    (hrow : rowPayloadCheck r p = true)
    (hMass : strictMassPayloadCheck r d p = true)
    (hOmega : omegaPayloadCheck r p cOmega = true)
    (hCap : omegaCapCheck r cCap = true) :
    parentCost ImbalancedChen.currentK (selectedParent r actualMask) ≤
      savedParent r (parentUnweightedMass (fullParent r)) - rowGainLower r :=
  archived_method_zero_current_cost r actualMask (actual_retained_massLower_sound r hr)
    (actual_strict_row_saved_bound r hr h12 h23 d p cOmega cCap hrow hMass hOmega hCap)

end
end ImbalancedChen.P2N48OriginalStrictLogMassAndOmegaPorts
