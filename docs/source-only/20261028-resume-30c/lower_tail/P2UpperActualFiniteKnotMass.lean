import ImbalancedChen.P2UpperActualCompiledQueryBuffer
import ImbalancedChen.P2LowerUnrestrictedTupleStripFubini

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Finite arithmetic knot mass for the actual ordinary part of the joint
U10/U11 source. The low band is unmasked and the high band retains E.
The clamp state is retained with its full original weight. Only the
nonclamped part is overcounted by finite affine prime strips. -/

namespace ImbalancedChen.P2UpperActualFiniteKnotMass

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P5Z U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox)
open P5U1011JointOverlap P2LowerFinitePrimeBandMass P2LowerCapPlanIntegerRetention
open P2LowerH248QueryKnotDictionary P2LowerUnrestrictedTupleStripFubini
open P2UpperActualCompiledQueryBuffer

private abbrev a : ℝ := 417 / 5000
private abbrev d : ℝ := 59 / 250

theorem slots_injective : Function.Injective slots := by
  intro t u h
  apply Prod.ext
  · apply Prod.ext
    · simpa only [slots, Matrix.cons_val_three] using congrFun h 3
    · simpa only [slots, Matrix.cons_val_two] using congrFun h 2
  · apply Prod.ext
    · simpa only [slots, Matrix.cons_val_one] using congrFun h 1
    · simpa only [slots, Matrix.cons_val_zero] using congrFun h 0

/-- Original four-prime multiplier weight, not a newly assigned mass. -/
theorem actual_tupleWeight_eq_original_totient {N : ℕ}
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E) :
    tupleWeight (slots t) = 1 / (Nat.totient (fullPrefix t) : ℝ) := by
  have hprod : ∀ I : Finset (Fin 4),
      Nat.totient (∏ i ∈ I, slots t i) = ∏ i ∈ I, Nat.totient (slots t i) := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      have hcop : Nat.Coprime (slots t i) (∏ j ∈ I, slots t j) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro j hj
        apply (Nat.coprime_primes (slots_prime ht i) (slots_prime ht j)).mpr
        intro heq
        exact hi (((slots_strictAnti ht).injective heq).symm ▸ hj)
      rw [Finset.prod_insert hi, Nat.totient_mul hcop, Finset.prod_insert hi, ih]
  rw [fullPrefix, hprod, Nat.cast_prod]
  simp [tupleWeight, reciprocalPrime, Finset.prod_div_distrib]

theorem actual_slots_in_prime_universe {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E) :
    slots t ∈ Finset.piFinset
      (fun _ : Fin 4 => P2LowerActualL6FiniteKnotMass.primeUniverse N) := by
  have hv := U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN ht
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_filter.mpr
  refine ⟨slots_carrier ht i, ?_, ?_⟩
  · simpa [coordinates, actualPrimeTupleLog, coordinate, lower,
      Part5OriginalUpsilon5CausalDictionary.a] using (mem_logPrimeBox.mp hv i).1
  · simpa [coordinates, actualPrimeTupleLog, coordinate, upper] using
      (mem_logPrimeBox.mp hv i).2.le

def restCoordinates (N : ℕ) (f : Fin 3 → ℕ) : LogFour :=
  ![coordinate N (f 0), coordinate N (f 1), coordinate N (f 2), 0]

def knotRest (N : ℕ) (p : Policy) (left : Bool) (q : ℝ)
    (f : Fin 3 → ℕ) : ℝ := upperKnotRest p left q (restCoordinates N f)

theorem actual_upper_knot_affine (N : ℕ) (p : Policy) (left : Bool)
    (q : ℝ) (f : Fin 4 → ℕ) :
    upperKnotEquation p left q (actualPrimeTupleLog N f) =
      upperKnotSlope p left q * coordinate N (f 3) +
        knotRest N p left q ((3 : Fin 4).removeNth f) := by
  rw [upper_knot_exact_affine]
  have hz : upperWZero (actualPrimeTupleLog N f) =
      upperWZero (restCoordinates N ((3 : Fin 4).removeNth f)) := by
    funext i
    fin_cases i <;> simp [upperWZero, restCoordinates, actualPrimeTupleLog,
      coordinate, Fin.removeNth, Function.update]
  simp only [knotRest, upperKnotRest, hz]
  rfl

def knotSlab (N : ℕ) (p : Policy) (left : Bool) (q radius : ℝ) :
    Finset (Fin 4 → ℕ) :=
  slabTuples (N := N) (P2LowerActualL6FiniteKnotMass.primeUniverse N) (3 : Fin 4)
    (upperKnotSlope p left q) d radius (knotRest N p left q)

theorem knotSlab_mass_le_mertens (N : ℕ) (p : Policy) (left : Bool)
    (q radius : ℝ) (hq : 2 ≤ q) (hradius : 0 ≤ radius) {eps : ℝ}
    (hM : PrimeIntervalMertens N a eps
      (P2LowerActualL6FiniteKnotMass.primeUniverse N)) :
    (∑ f ∈ knotSlab N p left q radius, tupleWeight f) ≤
      (∑ r ∈ P2LowerActualL6FiniteKnotMass.primeUniverse N, reciprocalPrime r) ^ 3 *
        (2 * (radius * d / upperKnotSlope p left q) / a + eps) :=
  unrestricted_slab_mass_le_mertens _ hM (3 : Fin 4)
    (upperKnotSlope p left q) d radius (upperKnotSlope_pos p left q hq)
    (by norm_num [d]) hradius (knotRest N p left q)

def nonclampSource (n N : ℕ) (E : ℕ × ℕ → Prop)
    (Q : Finset ℝ) (radius : ℝ) : Finset Four :=
  (U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E).filter
    (fun t => 2 * coordinates N t 3 <
      typedResidual (selectedPolicy n N t) (coordinates N t) ∧
      ∃ q ∈ Q, |idealQuery n N t - q| ≤ radius)

def nonclampMass (n N : ℕ) (E : ℕ × ℕ → Prop)
    (Q : Finset ℝ) (radius : ℝ) : ℝ :=
  ∑ t ∈ nonclampSource n N E Q radius, 1 / (Nat.totient (fullPrefix t) : ℝ)

/-- Actual selected policy and both its possible affine cap sides. All
sixteen policies are overcounted only after the source witness is read. -/
theorem nonclamp_source_has_slab {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {Q : Finset ℝ} {radius : ℝ} (hradius : 0 ≤ radius)
    {t : Four} (ht : t ∈ nonclampSource n N E Q radius) :
    ∃ q ∈ Q, ∃ p : Policy, ∃ left : Bool,
      slots t ∈ knotSlab N p left q radius := by
  obtain ⟨hord, hraw, q, hq, hnear⟩ := Finset.mem_filter.mp ht
  have hs := (Finset.mem_filter.mp hord).1
  have hv := U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs
  have hw : (0 : ℝ) < coordinates N t 3 :=
    (by norm_num [lower] : (0 : ℝ) < (lower : ℝ)).trans_le
      (mem_logPrimeBox.mp hv 3).1
  have hqraw : 2 < typedResidual (selectedPolicy n N t) (coordinates N t) /
      coordinates N t 3 := (lt_div_iff₀ hw).mpr hraw
  have hnear' : |typedResidual (selectedPolicy n N t) (coordinates N t) -
      q * coordinates N t 3| ≤ radius * coordinates N t 3 := by
    apply (P2LowerActualL5FiniteKnotMass.quotient_band_iff hw).mp
    simpa only [idealQuery, max_eq_right hqraw.le] using hnear
  have hwidth : coordinates N t 3 ≤ d := by
    simpa [upper, d] using (mem_logPrimeBox.mp hv 3).2.le
  obtain ⟨left, heq⟩ := actual_upper_policy_knot_has_affine_pivot
    (selectedPolicy n N t) q (coordinates N t)
  refine ⟨q, hq, selectedPolicy n N t, left, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨actual_slots_in_prime_universe hN hs, ?_⟩
  have heq' := actual_upper_knot_affine N (selectedPolicy n N t) left q (slots t)
  change |upperKnotSlope (selectedPolicy n N t) left q * coordinate N (slots t 3) +
    knotRest N (selectedPolicy n N t) left q ((3 : Fin 4).removeNth (slots t))| ≤ radius * d
  rw [← heq']
  -- The already chosen side in heq carries exactly the absolute wall.
  rw [upper_knot_exact_affine]
  exact (heq ▸ hnear').trans (mul_le_mul_of_nonneg_left hwidth hradius)

/-- Explicit finite-slab sum. Q, policies and affine sides are all finite;
its constant is independent of the number of physical grid cells. -/
def slabBudget (N : ℕ) (Q : Finset ℝ) (radius eps : ℝ) : ℝ :=
  ∑ q ∈ Q, ∑ p : Policy, ∑ left : Bool,
    (∑ r ∈ P2LowerActualL6FiniteKnotMass.primeUniverse N, reciprocalPrime r) ^ 3 *
      (2 * (radius * d / upperKnotSlope p left q) / a + eps)

theorem nonclamp_mass_le_mertens {n N : ℕ} (hN : 1 < N)
    (E : ℕ × ℕ → Prop) (Q : Finset ℝ) (radius : ℝ)
    (hQ : ∀ q ∈ Q, 2 ≤ q) (hradius : 0 ≤ radius) {eps : ℝ}
    (hM : PrimeIntervalMertens N a eps
      (P2LowerActualL6FiniteKnotMass.primeUniverse N)) :
    nonclampMass n N E Q radius ≤ slabBudget N Q radius eps := by
  let D := nonclampSource n N E Q radius
  let F := Finset.piFinset
    (fun _ : Fin 4 => P2LowerActualL6FiniteKnotMass.primeUniverse N)
  let term := fun (q : ℝ) (p : Policy) (left : Bool) (f : Fin 4 → ℕ) =>
    if f ∈ knotSlab N p left q radius then tupleWeight f else 0
  have hterm : ∀ q p left f, 0 ≤ term q p left f := by
    intro q p left f
    dsimp [term]
    split_ifs
    · exact tupleWeight_nonneg _
    · exact le_rfl
  have himage : D.image slots ⊆ F := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    exact actual_slots_in_prime_universe hN
      (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hcover : ∀ f ∈ D.image slots,
      tupleWeight f ≤ ∑ q ∈ Q, ∑ p : Policy, ∑ left : Bool, term q p left f := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨q, hq, p, left, hslab⟩ := nonclamp_source_has_slab hN hradius ht
    have h1 : tupleWeight (slots t) ≤ ∑ b : Bool, term q p b (slots t) := by
      simpa only [term, if_pos hslab] using
        (Finset.single_le_sum (fun b _ => hterm q p b (slots t)) (Finset.mem_univ left))
    have h2 := Finset.single_le_sum
      (fun p' _ => Finset.sum_nonneg (fun b _ => hterm q p' b (slots t)))
      (Finset.mem_univ p)
    have h3 := Finset.single_le_sum
      (fun q' _ => Finset.sum_nonneg (fun p' _ =>
        Finset.sum_nonneg (fun b _ => hterm q' p' b (slots t)))) hq
    exact h1.trans (h2.trans h3)
  have hmass : nonclampMass n N E Q radius = ∑ f ∈ D.image slots, tupleWeight f := by
    rw [Finset.sum_image (fun t ht u hu h => slots_injective h)]
    apply Finset.sum_congr rfl
    intro t ht
    exact (actual_tupleWeight_eq_original_totient
      (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).symm
  rw [hmass]
  calc
    _ ≤ ∑ f ∈ D.image slots, ∑ q ∈ Q, ∑ p : Policy, ∑ left : Bool,
        term q p left f := Finset.sum_le_sum hcover
    _ ≤ ∑ f ∈ F, ∑ q ∈ Q, ∑ p : Policy, ∑ left : Bool, term q p left f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro f hf hnot
      exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg
        (fun p _ => Finset.sum_nonneg (fun left _ => hterm q p left f)))
    _ = ∑ q ∈ Q, ∑ p : Policy, ∑ left : Bool, ∑ f ∈ F, term q p left f := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ ≤ slabBudget N Q radius eps := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro left hleft
      have hsum : (∑ f ∈ F, term q p left f) =
          ∑ f ∈ knotSlab N p left q radius, tupleWeight f := by
        have hsub : knotSlab N p left q radius ⊆ F := Finset.filter_subset _ _
        change (∑ f ∈ F, if f ∈ knotSlab N p left q radius then tupleWeight f else 0) = _
        rw [← Finset.sum_filter]
        congr 1
        ext f
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hf => ⟨hsub hf, hf⟩⟩
      rw [hsum]
      exact knotSlab_mass_le_mertens N p left q radius (hQ q hq) hradius hM

def idealMass (n N : ℕ) (E : ℕ × ℕ → Prop) (Q : Finset ℝ) (radius : ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    if ∃ q ∈ Q, |idealQuery n N t - q| ≤ radius
    then 1 / (Nat.totient (fullPrefix t) : ℝ) else 0

/-- This term is deliberately retained: it is a whole clamp state, not
an O(radius) error or a null wall. -/
def clampMass (n N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    if typedResidual (selectedPolicy n N t) (coordinates N t) ≤
      2 * coordinates N t 3
    then 1 / (Nat.totient (fullPrefix t) : ℝ) else 0

theorem ideal_mass_le_clamp_add_nonclamp (n N : ℕ)
    (E : ℕ × ℕ → Prop) (Q : Finset ℝ) (radius : ℝ) :
    idealMass n N E Q radius ≤ clampMass n N E + nonclampMass n N E Q radius := by
  unfold idealMass clampMass nonclampMass nonclampSource
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hn : ∃ q ∈ Q, |idealQuery n N t - q| ≤ radius
  · by_cases hc : typedResidual (selectedPolicy n N t) (coordinates N t) ≤
        2 * coordinates N t 3
    · simp [hn, hc, not_lt_of_ge hc]
    · have hs := lt_of_not_ge hc
      simp [hn, hc, hs]
  · simp only [if_neg hn, and_false, if_false, add_zero]
    split_ifs <;> positivity

theorem ideal_mass_le_clamp_add_mertens {n N : ℕ} (hN : 1 < N)
    (E : ℕ × ℕ → Prop) (Q : Finset ℝ) (radius : ℝ)
    (hQ : ∀ q ∈ Q, 2 ≤ q) (hradius : 0 ≤ radius) {eps : ℝ}
    (hM : PrimeIntervalMertens N a eps
      (P2LowerActualL6FiniteKnotMass.primeUniverse N)) :
    idealMass n N E Q radius ≤ clampMass n N E + slabBudget N Q radius eps :=
  (ideal_mass_le_clamp_add_nonclamp n N E Q radius).trans
    (add_le_add_left (nonclamp_mass_le_mertens hN E Q radius hQ hradius hM) _)

def bufferValues (n : ℕ) (eta : ℚ) : Finset ℝ :=
  Finset.univ.image (fun j : Grid n => boxBuffer
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta)

theorem bufferValues_nonempty (n : ℕ) (eta : ℚ) : (bufferValues n eta).Nonempty :=
  Finset.image_nonempty.mpr Finset.univ_nonempty

/-- A computed finite maximum, chosen before N and before every tuple. -/
def meshBuffer (n : ℕ) (eta : ℚ) : ℝ :=
  (bufferValues n eta).max' (bufferValues_nonempty n eta)

theorem actual_boxBuffer_le_meshBuffer (n N : ℕ) (eta : ℚ) (t : Four) :
    boxBuffer (selectedPolicy n N t) (ownerBox n N t) eta ≤ meshBuffer n eta := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨owner n (coordinates N t), Finset.mem_univ _, rfl⟩

theorem meshBuffer_nonneg (n : ℕ) (eta : ℚ) (heta : 0 ≤ eta) :
    0 ≤ meshBuffer n eta := by
  have hm := Finset.max'_mem (bufferValues n eta) (bufferValues_nonempty n eta)
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
  rw [← heq]
  unfold boxBuffer
  have hd := U1011OriginalSixteenNearCapBoxProfiles.diameter_nonneg
    (gridBox n j) (gridBox_valid n j)
  have he : (0 : ℝ) ≤ eta := by exact_mod_cast heta
  positivity

/-- The finite maximum is an explicit uniform mesh quantity. It carries
no factor equal to the number of cells. -/
theorem grid_boxBuffer_eq (n : ℕ) (j : Grid n) (p : Policy) (eta : ℚ) :
    boxBuffer p (gridBox n j) eta =
      10 * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n + (21 / 16 : ℝ) * eta := by
  have hwidth (i : Fin 4) :
      ((gridBox n j).hi i : ℝ) - ((gridBox n j).lo i : ℝ) =
        logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
    rw [cast_grid_hi, cast_grid_lo, logPrimeMeshHi_eq_lo_add_step]
    ring
  have hdiam : U1011OriginalSixteenNearCapBoxProfiles.diameter (gridBox n j) =
      4 * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
    simp only [U1011OriginalSixteenNearCapBoxProfiles.diameter,
      U1011OriginalSixteenNearCapBoxProfiles.diameterQ, Rat.cast_sum, Rat.cast_sub]
    simp_rw [hwidth]
    simp
  rw [boxBuffer, hdiam]
  ring

theorem meshBuffer_eq (n : ℕ) (eta : ℚ) :
    meshBuffer n eta =
      10 * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n + (21 / 16 : ℝ) * eta := by
  have hm := Finset.max'_mem (bufferValues n eta) (bufferValues_nonempty n eta)
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
  exact heq.symm.trans (grid_boxBuffer_eq n j _ eta)

/-- Rational precision chosen before N and all actual prime tuples. -/
def precision (n : ℕ) : ℚ := (upper - lower) / (n + 1 : ℚ)

theorem precision_pos (n : ℕ) : 0 < precision n := by
  unfold precision
  exact div_pos (by norm_num [lower, upper]) (by positivity)

theorem meshBuffer_precision_eq (n : ℕ) :
    meshBuffer n (precision n) =
      (181 / 16 : ℝ) * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
  rw [meshBuffer_eq]
  have hp : (precision n : ℝ) = logPrimeMeshStep (lower : ℝ) (upper : ℝ) n := by
    simp [precision, logPrimeMeshStep]
  rw [hp]
  ring

theorem meshBuffer_precision_tendsto :
    Tendsto (fun n : ℕ => meshBuffer n (precision n)) atTop (𝓝 0) := by
  have ht := (tendsto_logPrimeMeshStep (lower : ℝ) (upper : ℝ)).const_mul (181 / 16 : ℝ)
  simpa only [meshBuffer_precision_eq, mul_zero] using ht

theorem eventually_small_meshBuffer :
    ∀ᶠ n : ℕ in atTop, meshBuffer n (precision n) ≤ a / 2 := by
  have hsmall := meshBuffer_precision_tendsto.eventually
    (gt_mem_nhds (by norm_num [a] : (0 : ℝ) < a / 2))
  exact hsmall.mono (fun n hn => hn.le)

def physicalMass (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop)
    (Q : Finset ℝ) (radius : ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    if ∃ q ∈ Q, |compiledQuery n N eta t - q| ≤ radius
    then 1 / (Nat.totient (fullPrefix t) : ℝ) else 0

/-- The same actual frozen coefficient row determines the enlarged
radius. This is not an equality between physical and ideal queries. -/
theorem physical_mass_le_enlarged_ideal {n N : ℕ} (hN : 1 < N)
    (eta : ℚ) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (Q : Finset ℝ)
    (radius : ℝ) (hsmall : meshBuffer n eta ≤ a / 2) :
    physicalMass n N eta E Q radius ≤
      idealMass n N E Q (radius + 500 * meshBuffer n eta) := by
  unfold physicalMass idealMass
  apply Finset.sum_le_sum
  intro t ht
  by_cases hn : ∃ q ∈ Q, |compiledQuery n N eta t - q| ≤ radius
  · obtain ⟨q, hq, hnear⟩ := hn
    have hb := actual_boxBuffer_le_meshBuffer n N eta t
    have he := actual_frozen_knot_implies_enlarged_ideal hN heta ht
      (hb.trans hsmall) q radius hnear
    have hi : ∃ q ∈ Q, |idealQuery n N t - q| ≤ radius + 500 * meshBuffer n eta :=
      ⟨q, hq, he.trans (by linarith)⟩
    simp only [if_pos ⟨q, hq, hnear⟩, if_pos hi, le_refl]
  · rw [if_neg hn]
    split_ifs <;> positivity

/-- Actual U10/U11 ordinary-source finite knot bound with the original
weights/masks. The whole clamp is retained explicitly; the remaining
mass uses the mandatory radius+500*meshBuffer enlargement. Fallback
counts remain the distinct original compiler fallback source. -/
theorem physical_mass_le_clamp_add_mertens {n N : ℕ} (hN : 1 < N)
    (eta : ℚ) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (Q : Finset ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius) (hQ : ∀ q ∈ Q, 2 ≤ q)
    (hsmall : meshBuffer n eta ≤ a / 2) {eps : ℝ}
    (hM : PrimeIntervalMertens N a eps
      (P2LowerActualL6FiniteKnotMass.primeUniverse N)) :
    physicalMass n N eta E Q radius ≤ clampMass n N E +
      slabBudget N Q (radius + 500 * meshBuffer n eta) eps := by
  apply (physical_mass_le_enlarged_ideal hN eta heta E Q radius hsmall).trans
  exact ideal_mass_le_clamp_add_mertens hN E Q _ hQ
    (add_nonneg hradius (mul_nonneg (by norm_num) (meshBuffer_nonneg n eta heta.le))) hM

theorem physical_actual_table_mass_le_clamp_add_mertens {n N : ℕ} (hN : 1 < N)
    (eta : ℚ) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hsmall : meshBuffer n eta ≤ a / 2) {eps : ℝ}
    (hM : PrimeIntervalMertens N a eps
      (P2LowerActualL6FiniteKnotMass.primeUniverse N)) :
    physicalMass n N eta E actualH248ActiveKnots radius ≤ clampMass n N E +
      slabBudget N actualH248ActiveKnots (radius + 500 * meshBuffer n eta) eps := by
  apply physical_mass_le_clamp_add_mertens hN eta heta E _ radius hradius _ hsmall hM
  intro q hq
  exact (Finset.mem_filter.mp hq).2

end
end ImbalancedChen.P2UpperActualFiniteKnotMass
