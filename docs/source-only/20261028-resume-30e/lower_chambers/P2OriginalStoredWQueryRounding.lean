import ImbalancedChen.P2OriginalCommonActualWMesh

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The stored wQueryLower uses the entire upper endpoint prefix AND the upper
third denominator. Both rounding contributions are paid. This is not the
previous same-point cap/query comparison. All scalar premises below are
proved for the actual canonical code and its original WBoxCheck.
-/

namespace ImbalancedChen.P2OriginalStoredWQueryRounding

noncomputable section
open scoped Classical
open Set
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalLowerWThirdPhysicalRow
open P2OriginalStrictWLocalRationalCover
open P2OriginalCommonActualWMesh

private theorem quotient_rounding_bound
    (epsilon z Z n m d h M : ℝ) (hepsilon : 0 < epsilon)
    (hez : epsilon ≤ z) (hzZ : z ≤ Z)
    (hgap : Z - z ≤ h) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hd0 : 0 ≤ n - m) (hd : n - m ≤ d) :
    0 ≤ n / z - m / Z ∧
      n / z - m / Z ≤ d / epsilon + M * h / epsilon ^ 2 := by
  have hz : 0 < z := hepsilon.trans_le hez
  have hZ : 0 < Z := hz.trans_le hzZ
  have hg0 : 0 ≤ Z - z := sub_nonneg.mpr hzZ
  have hh0 : 0 ≤ h := hg0.trans hgap
  have hM : 0 ≤ M := hm.trans hmM
  have hden : epsilon ^ 2 ≤ z * Z := by
    calc
      epsilon ^ 2 = epsilon * epsilon := pow_two _
      _ ≤ z * Z := mul_le_mul hez (hez.trans hzZ) hepsilon.le hz.le
  have hn0 : 0 ≤ m * (Z - z) := mul_nonneg hm hg0
  have hnum : m * (Z - z) ≤ M * h :=
    mul_le_mul hmM hgap hg0 hM
  have heq : n / z - m / Z =
      (n - m) / z + m * (Z - z) / (z * Z) := by
    field_simp [hz.ne', hZ.ne']
    ring
  have hfirst : (n - m) / z ≤ d / epsilon := by
    calc
      _ ≤ (n - m) / epsilon :=
        div_le_div_of_nonneg_left hd0 hepsilon hez
      _ ≤ _ := div_le_div_of_nonneg_right hd hepsilon.le
  have hsecond : m * (Z - z) / (z * Z) ≤ M * h / epsilon ^ 2 := by
    calc
      _ ≤ M * h / (z * Z) :=
        div_le_div_of_nonneg_right hnum (mul_pos hz hZ).le
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hM hh0)
        (pow_pos hepsilon 2) hden
  rw [heq]
  exact ⟨add_nonneg (div_nonneg hd0 hz.le) (div_nonneg hn0 (mul_pos hz hZ).le),
    add_le_add hfirst hsecond⟩

def idealWQuery (x : Point) : ℝ :=
  (B (x 2) - (x 0 + x 1 + x 2)) / x 2

def storedWQuery (S : CompactStart) (mesh : ℕ) (x : Point) (r : ℚ) : ℝ :=
  wQueryLower S (canonicalThirdCode S mesh x) r

theorem storedWQuery_eq_endpoint_quotient
    (S : CompactStart) (mesh : ℕ) (x : Point) (r : ℚ) :
    storedWQuery S mesh x r =
      ((wCap S (canonicalThirdCode S mesh x) r : ℝ) -
        (meshUpper S mesh x 0 + meshUpper S mesh x 1 + meshUpper S mesh x 2)) /
        meshUpper S mesh x 2 := by
  unfold storedWQuery wQueryLower meshUpper liftSlot
  push_cast
  ring

def storedErrorEnvelope (S : CompactStart) (mesh : ℕ) (r : ℚ) : ℝ :=
  ((r : ℝ) + (27 / 8 : ℝ) *
    logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh) / S.epsilon +
    Lambda * logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh /
      (S.epsilon : ℝ) ^ 2

-- Full stored numerator error: the cap contributes r+3h/8, and all three
-- physical exponent endpoints together contribute at most another 3h.
-- The remaining Lambda*h/epsilon^2 term pays the changed denominator.
theorem actual_stored_W_query_loss (S : CompactStart) (rho : ℝ)
    (mesh : ℕ) (x : Point)
    (hx : ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ))
    (r delta : ℚ)
    (hW : WBoxCheck S (canonicalThirdCode S mesh x) rho r delta) :
    0 ≤ idealWQuery x - storedWQuery S mesh x r ∧
      idealWQuery x - storedWQuery S mesh x r ≤ storedErrorEnvelope S mesh r := by
  let H := meshUpper S mesh x
  let C := (wCap S (canonicalThirdCode S mesh x) r : ℝ)
  let n := B (x 2) - (x 0 + x 1 + x 2)
  let m := C - (H 0 + H 1 + H 2)
  let h := logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh
  have heps : (0 : ℝ) < S.epsilon := by exact_mod_cast S.epsilon_pos
  have hz : 0 < x 2 := heps.trans_le (hx 2).1
  have b0 := canonical_endpoint_bounds S mesh x hx 0
  have b1 := canonical_endpoint_bounds S mesh x hx 1
  have b2 := canonical_endpoint_bounds S mesh x hx 2
  have H0 : 0 < H 0 := heps.trans_le ((hx 0).1.trans b0.2.1)
  have H1 : 0 < H 1 := heps.trans_le ((hx 1).1.trans b1.2.1)
  have H2 : 0 < H 2 := hz.trans_le b2.2.1
  have hr : 0 ≤ r := hW.buffer_pos.le
  have hcaploss := W_cap_loss_le S mesh x hx r hr
  have htop : C ≤ Lambda := by
    simpa only [C, topCap, Lambda] using hW.compact_gates.2.1
  have hquery := WBoxCheck_query_gt_one S rho r delta
    (canonicalThirdCode S mesh x) hW
  have hstored : storedWQuery S mesh x r = m / H 2 :=
    storedWQuery_eq_endpoint_quotient S mesh x r
  change 1 < storedWQuery S mesh x r at hquery
  rw [hstored] at hquery
  have hm : 0 ≤ m := by
    have hnum := (lt_div_iff₀ H2).mp hquery
    linarith
  have hmM : m ≤ Lambda := by dsimp [m]; linarith
  have gaps0 : 0 ≤ H 0 - x 0 := sub_nonneg.mpr b0.2.1
  have gaps1 : 0 ≤ H 1 - x 1 := sub_nonneg.mpr b1.2.1
  have gaps2 : 0 ≤ H 2 - x 2 := sub_nonneg.mpr b2.2.1
  have gaph0 : H 0 - x 0 ≤ h := by dsimp [H, h]; linarith [b0.1, b0.2.2]
  have gaph1 : H 1 - x 1 ≤ h := by dsimp [H, h]; linarith [b1.1, b1.2.2]
  have gaph2 : H 2 - x 2 ≤ h := by dsimp [H, h]; linarith [b2.1, b2.2.2]
  have hd0 : 0 ≤ n - m := by dsimp [n, m]; linarith [hcaploss.1]
  have hd : n - m ≤ (r : ℝ) + (27 / 8 : ℝ) * h := by
    dsimp [n, m, h]
    linarith [hcaploss.2]
  have hbound := quotient_rounding_bound S.epsilon (x 2) (H 2) n m
    ((r : ℝ) + (27 / 8 : ℝ) * h) h Lambda heps (hx 2).1 b2.2.1 gaph2 hm hmM hd0 hd
  simpa only [idealWQuery, hstored, storedErrorEnvelope, n, h] using hbound

end
end ImbalancedChen.P2OriginalStoredWQueryRounding
