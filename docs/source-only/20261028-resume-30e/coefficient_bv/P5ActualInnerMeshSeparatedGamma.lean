import ImbalancedChen.P5All16FineMeshGateScalar
import ImbalancedChen.P5OriginalGatedSlotsRetainedSupport
import ImbalancedChen.SmallRoughMainTerm

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This consumes the independently constructed ORIGINAL ordinary upper
fine-mesh alphabet and its all-tuple inner-cell gate theorem. The gate
and the residual Mobius sign are evaluated on the source side, then
proved constant, before the three fixed Cartesian boxes are regrouped.
No rho or gate remains in the product test of the resulting convolution.
The marked prefix stays in EVERY complete q. The original actual beta
is attached only to group3 by unique small/rough factorization, proving
a full-integer one-bound without counting the small support.

The normalization here is explicitly the existing slot-count factorial
normalization, with all three restoring factorials retained in the
external scalar. It is NOT a claim of the manuscript's sharper per-label
scalar budget. This ordinary inner-cell source is not identified with
the older compact W4 policy or the E common-refined physical policy.
The actual all16 inner-pair-to-full-box source dictionary, walls, and
all-winning-branch numerical licences remain independent obligations.
-/

namespace ImbalancedChen.P5Z.ActualInnerMeshSeparatedGamma
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open OriginalPresievedRoughPrimeSlots PresievedRoughGateMeshReserve
open OriginalOrdinaryCommonBetaModel OriginalPresievedRoughSlotCoefficient
open OriginalGatedSlotsRetainedSupport
open PresievedFineLabelPrimeBoxes
open JointPresievedSlotAffineRealization
open ActualAll16UnrestrictedResidualConvolution
open All16FineMeshGateScalar

def groupBox (N cap m : ℕ) (w Z : ℝ) (word : List (Fin (m + 1))) :
    Finset (List ℕ) := actualPrimeSlotBox (meshPrimeAlphabet N cap w Z m) word

def groupSupport (N cap m : ℕ) (w Z : ℝ) (word : List (Fin (m + 1))) : Finset ℕ :=
  (groupBox N cap m w Z word).image List.prod

def gamma (N cap m : ℕ) (w Z : ℝ) (word : List (Fin (m + 1))) (d : ℕ) : ℝ :=
  actualNormalizedPrimeTupleCoefficient (groupBox N cap m w Z word) word.length d

theorem mesh_prime_rough {N cap m : ℕ} {w Z : ℝ} {i : Fin (m + 1)} {p : ℕ}
    (hp : p ∈ meshPrimeAlphabet N cap w Z m i) : p ∈ roughPrimeFinset N cap w Z :=
  (Finset.mem_filter.mp hp).1

theorem gamma_abs_le_one (N cap m : ℕ) (w Z : ℝ)
    (word : List (Fin (m + 1))) (d : ℕ) : |gamma N cap m w Z word d| ≤ 1 := by
  exact actualPrimeSlotBox_normalized_abs_le_one _ word
    (fun _ _ _ hp => (mem_roughPrimeFinset.mp (mesh_prime_rough hp)).2.1) d

theorem groupSupport_rough {N cap m : ℕ} (w Z : ℝ)
    (word : List (Fin (m + 1))) {d : ℕ} (hd : d ∈ groupSupport N cap m w Z word) :
    RoughPrimeSupportedAt w d := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  have hp : ∀ p ∈ ps, p ∈ roughPrimeFinset N cap w Z :=
    actualPrimeSlotBox_forall _ word (fun p => p ∈ roughPrimeFinset N cap w Z)
      (fun _ _ _ h => mesh_prime_rough h) ps hps
  have hprime : ∀ p ∈ ps, Nat.Prime p := fun p h => (mem_roughPrimeFinset.mp (hp p h)).2.1
  have hpos : 0 < ps.prod := List.prod_pos (fun p h => (hprime p h).pos)
  refine ⟨hpos.ne', ?_⟩
  intro p hfactor
  have hlist : p ∈ ps.prod.primeFactorsList := by
    apply List.mem_toFinset.mp
    simpa only [Nat.toFinset_factors] using hfactor
  have hperm := Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod) hprime
  exact (mem_roughPrimeFinset.mp (hp p (hperm.mem_iff.mpr hlist))).2.2.2.1

/-- List form of the independent all-tuple original gate certificate. -/
theorem inner_list_original_gates {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (ps : List ℕ) (hps : ps ∈ meshPrimeBox N cap w Z m j) :
    ps.Pairwise (· > ·) ∧ ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell) ps.reverse := by
  have hlen : ps.length = r := by
    simpa only [List.length_ofFn] using actualPrimeSlotBox_length
      (meshPrimeAlphabet N cap w Z m) (List.ofFn j) ps hps
  subst r
  let p := slotVector ps
  have hlist : List.ofFn p = ps := ofFn_slotVector ps
  have hmem : List.ofFn p ∈ meshPrimeBox N cap w Z m j := by rwa [hlist]
  obtain ⟨hanti, hadm⟩ := inner_mesh_box_original_gates hN w Z ell hj p hmem
  have hsorted : ps.Pairwise (· > ·) := by
    rw [← hlist]
    exact List.pairwise_ofFn.mpr hanti
  exact ⟨hsorted, by simpa only [hlist] using hadm⟩

/-- The ORIGINAL raw upper gate and ORIGINAL Mobius sign are derived
from every tuple in the physical inner box, not given as premises. -/
theorem inner_list_gate_and_sign {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (ps : List ℕ) (hps : ps ∈ meshPrimeBox N cap w Z m j) :
    rawUpperGate ((N : ℝ) ^ ell) ps.prod ∧
      (ArithmeticFunction.moebius ps.prod : ℝ) = (-1 : ℝ) ^ r := by
  obtain ⟨hsorted, hadm⟩ := inner_list_original_gates hN w Z ell hj ps hps
  have hlen : ps.length = r := by
    simpa only [List.length_ofFn] using actualPrimeSlotBox_length
      (meshPrimeAlphabet N cap w Z m) (List.ofFn j) ps hps
  have hprime : ∀ q ∈ ps, Nat.Prime q :=
    actualPrimeSlotBox_prime _ (List.ofFn j)
      (fun _ _ _ hp => (mem_roughPrimeFinset.mp (mesh_prime_rough hp)).2.1) ps hps
  have hprod : (∏ q ∈ ps.toFinset, q) = ps.prod := by
    simpa using List.prod_toFinset (fun q : ℕ => q) hsorted.nodup
  have hfactor : ps.prod.primeFactors = ps.toFinset := by
    rw [← hprod]
    exact Nat.primeFactors_prod (fun q hq => hprime q (List.mem_toFinset.mp hq))
  constructor
  · change ((ps.reverse.prod : ℕ) : ℝ) < (N : ℝ) ^ ell ∧
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        ((N : ℝ) ^ ell) ps.reverse.toFinset at hadm
    simpa only [rawUpperGate, List.prod_reverse, List.toFinset_reverse, hfactor] using hadm
  · have hs := actualPrimeVector_moebius_eq_sign ps hprime hsorted.nodup
    rw [hlen] at hs
    exact_mod_cast hs

/-- Every tuple in the certified inner box is an ACTUAL retained modulus
of the independent original ordinary tree, by its reverse dictionary. -/
theorem inner_list_actual_retained {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (ps : List ℕ) (hps : ps ∈ meshPrimeBox N cap w Z m j) :
    ps.prod ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z := by
  obtain ⟨hsorted, hadm⟩ := inner_list_original_gates hN w Z ell hj ps hps
  apply ranked_word_product_retained (R := ps.length) hL
  apply Finset.mem_biUnion.mpr
  refine ⟨ps.length, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨(mem_actualPrimeSlotBox_replicate _ _ _).mpr ⟨rfl, ?_⟩, hsorted, hadm⟩
  exact actualPrimeSlotBox_forall _ (List.ofFn j)
    (fun p => p ∈ roughPrimeFinset N cap w Z)
    (fun _ _ _ hp => mesh_prime_rough hp) ps hps

/-- Pointwise binding to the independently defined actual ordinary
common-beta coefficient. The beta level B and the residual level remain
distinct. This is stronger than a gate-free candidate definition. -/
theorem inner_list_actual_presieved_value {r N cap m e : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (he : e ∈ actualSmallRosserSupport N cap w)
    (ps : List ℕ) (hps : ps ∈ meshPrimeBox N cap w Z m j) :
    presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) =
      (-1 : ℝ) ^ r * rawBetaWeight N cap r w B e := by
  have hd := inner_list_actual_retained hN w Z ell hL hj ps hps
  have hs := (inner_list_gate_and_sign hN w Z ell hj ps hps).2
  simpa only [commonSmallWeight, roughWeight_eq_moebius hL hd, hs, rawBetaWeight]
    using (presieved_coefficient_value (B := B) hL he hd)

/-- The gate-free value is proved pointwise on the actual inner box.
The arbitrary test still uses complete marked-prefix * small * rough q. -/
theorem inner_signed_source_gate_elimination {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (prefix e : ℕ) (F : ℕ → ℝ) :
    (∑ ps ∈ meshPrimeBox N cap w Z m j,
      (if rawUpperGate ((N : ℝ) ^ ell) ps.prod then
        (ArithmeticFunction.moebius ps.prod : ℝ) else 0) * F (prefix * (e * ps.prod))) =
    ∑ ps ∈ meshPrimeBox N cap w Z m j, (-1 : ℝ) ^ r * F (prefix * (e * ps.prod)) := by
  apply Finset.sum_congr rfl
  intro ps hps
  obtain ⟨hg, hs⟩ := inner_list_gate_and_sign hN w Z ell hj ps hps
  rw [if_pos hg, hs]

def attachedSupport (N cap m : ℕ) (w Z : ℝ) (word : List (Fin (m + 1))) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (groupSupport N cap m w Z word)

/-- Full-rank rawBetaWeight is frozen before the group assignment. -/
def attachedGamma (N cap m r : ℕ) (w Z B : ℝ) (word : List (Fin (m + 1))) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) (groupSupport N cap m w Z word)
    (gamma N cap m w Z word) (rawBetaWeight N cap r w B) (rawBetaWeight N cap r w B)

theorem attachedGamma_at_product {N cap m r e d : ℕ} (w Z B : ℝ)
    (word : List (Fin (m + 1))) (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ groupSupport N cap m w Z word) :
    attachedGamma N cap m r w Z B word (e * d) =
      gamma N cap m w Z word d * rawBetaWeight N cap r w B e := by
  rw [attachedGamma, smallRoughRho_mul
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fun d hd => groupSupport_rough w Z word hd) _ _ _ he hd]
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self]

theorem attachedGamma_abs_le_one (N cap m r : ℕ) (w Z B : ℝ)
    (word : List (Fin (m + 1))) (q : ℕ) : |attachedGamma N cap m r w Z B word q| ≤ 1 := by
  by_cases hq : q ∈ attachedSupport N cap m w Z word
  · obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
    exact abs_smallRoughRho_mul_le_one
      (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
      (fun d hd => groupSupport_rough w Z word hd)
      (gamma N cap m w Z word) _ _ (fun d _ => gamma_abs_le_one N cap m w Z word d)
      (fun e _ => raw_beta_abs_le_one N cap r w B e)
      (fun e _ => raw_beta_abs_le_one N cap r w B e) he hd
  · rw [attachedGamma, smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq]
    norm_num

theorem attachedGamma_fullq_sum (N cap m r : ℕ) (w Z B : ℝ)
    (word : List (Fin (m + 1))) (H : ℕ → ℝ) :
    (∑ q ∈ attachedSupport N cap m w Z word,
      attachedGamma N cap m r w Z B word q * H q) =
    ∑ e ∈ actualSmallRosserSupport N cap w, ∑ d ∈ groupSupport N cap m w Z word,
      gamma N cap m w Z word d * rawBetaWeight N cap r w B e * H (e * d) := by
  rw [attachedSupport, attachedGamma, sum_smallRoughRho_mul
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fun d hd => groupSupport_rough w Z word hd)]
  rw [smallRoughPairs, Finset.sum_product]
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self]

/-- All restoring slot-count factorials and the ORIGINAL per-label
denominator occur exactly once. Beta is excluded, to live in gamma3. -/
def atomScalar {r m : ℕ} (j : Grid r m) (out : List (Fin (m + 1)) ×
    List (Fin (m + 1)) × List (Fin (m + 1))) : ℝ :=
  ((-1 : ℝ) ^ r / (meshMultiplicity j : ℝ)) * (out.1.length.factorial : ℝ) *
    (out.2.1.length.factorial : ℝ) * (out.2.2.length.factorial : ℝ)

/-- Exact signed ORIGINAL inner-box source at fixed e; the fixed
endpoint assignment, not a tuplewise decision fibre, supplies the groups. -/
theorem inner_signed_fixed_beta_three_groups {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (D A : ℝ) (yz : Bool) (prefix e : ℕ) (F : ℕ → ℝ) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    meshScalar N cap w B e j *
      (∑ ps ∈ meshPrimeBox N cap w Z m j,
        (if rawUpperGate ((N : ℝ) ^ ell) ps.prod then
          (ArithmeticFunction.moebius ps.prod : ℝ) else 0) * F (prefix * (e * ps.prod))) =
    ∑ a ∈ groupSupport N cap m w Z out.1,
      ∑ b ∈ groupSupport N cap m w Z out.2.1,
        ∑ d ∈ groupSupport N cap m w Z out.2.2,
          atomScalar j out * rawBetaWeight N cap r w B e *
            gamma N cap m w Z out.1 a * gamma N cap m w Z out.2.1 b *
              gamma N cap m w Z out.2.2 d * F (prefix * (e * (a * b * d))) := by
  dsimp only
  let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
  rw [inner_signed_source_gate_elimination hN w Z ell hj prefix e F,
    computed_mesh_atom_three_group_sum w Z B e j D A yz
      (fun n => (-1 : ℝ) ^ r * F (prefix * (e * n)))]
  simp_rw [Finset.mul_sum]
  have hnorm := actualPrimeTuple_threeGroup_sum_normalized
    (groupBox N cap m w Z out.1) (groupBox N cap m w Z out.2.1)
    (groupBox N cap m w Z out.2.2) out.1.length out.2.1.length out.2.2.length
    (meshScalar N cap w B e j * (-1 : ℝ) ^ r)
    (fun n => F (prefix * (e * n)))
  calc
    _ = ∑ ps ∈ groupBox N cap m w Z out.1,
        ∑ qs ∈ groupBox N cap m w Z out.2.1,
          ∑ rs ∈ groupBox N cap m w Z out.2.2,
            (meshScalar N cap w B e j * (-1 : ℝ) ^ r) *
              F (prefix * (e * (ps.prod * qs.prod * rs.prod))) := by
      apply Finset.sum_congr rfl
      intro ps hps
      apply Finset.sum_congr rfl
      intro qs hqs
      apply Finset.sum_congr rfl
      intro rs hrs
      ring
    _ = _ := by
      rw [hnorm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [atomScalar, meshScalar, gamma]
      ring

/-- Genuine separated three-convolution for the independently defined
ordinary inner mesh source. Exact complete q, exact original sign/beta/
M_res, no rho or gate in the product test, and no card(small) loss. -/
theorem mesh_inner_signed_beta_three_convolution {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (D A : ℝ) (yz : Bool) (prefix : ℕ) (F : ℕ → ℝ) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (∑ e ∈ actualSmallRosserSupport N cap w, meshScalar N cap w B e j *
      (∑ ps ∈ meshPrimeBox N cap w Z m j,
        (if rawUpperGate ((N : ℝ) ^ ell) ps.prod then
          (ArithmeticFunction.moebius ps.prod : ℝ) else 0) * F (prefix * (e * ps.prod)))) =
    ∑ a ∈ groupSupport N cap m w Z out.1,
      ∑ b ∈ groupSupport N cap m w Z out.2.1,
        ∑ q3 ∈ attachedSupport N cap m w Z out.2.2,
          atomScalar j out * gamma N cap m w Z out.1 a *
            gamma N cap m w Z out.2.1 b * attachedGamma N cap m r w Z B out.2.2 q3 *
              F (prefix * (a * b * q3)) := by
  dsimp only
  let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
  simp_rw [inner_signed_fixed_beta_three_groups hN w Z ell B hj D A yz prefix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have hpush := attachedGamma_fullq_sum N cap m r w Z B out.2.2
    (fun q3 => atomScalar j out * gamma N cap m w Z out.1 a *
      gamma N cap m w Z out.2.1 b * F (prefix * (a * b * q3)))
  calc
    _ = ∑ e ∈ actualSmallRosserSupport N cap w,
        ∑ d ∈ groupSupport N cap m w Z out.2.2,
          gamma N cap m w Z out.2.2 d * rawBetaWeight N cap r w B e *
            (atomScalar j out * gamma N cap m w Z out.1 a *
              gamma N cap m w Z out.2.1 b * F (prefix * (a * b * (e * d)))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d hd
      rw [show a * b * (e * d) = e * (a * b * d) by ring]
      ring
    _ = _ := by
      rw [← hpush]
      apply Finset.sum_congr rfl
      intro q3 hq3
      ring

/-- The same separated identity now starts from the INDEPENDENT ACTUAL
ordinary common-beta coefficient, evaluated at every full residual e*d.
No definition identifies that coefficient with the proposed tensor.
Its displayed inner-box source normalization is retained literally.
This does not itself prove the external all16 inner-pairs/box dictionary. -/
theorem actual_ordinary_inner_source_three_convolution {r N cap m : ℕ} (hN : 1 < N)
    (w Z ell B : ℝ) (hL : 1 < (N : ℝ) ^ ell)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m)
    (D A : ℝ) (yz : Bool) (prefix : ℕ) (F : ℕ → ℝ) :
    let out := computedGroups D A yz (meshUpper N m) (List.ofFn j)
    (∑ e ∈ actualSmallRosserSupport N cap w,
      (1 / (meshMultiplicity j : ℝ)) *
        (∑ ps ∈ meshPrimeBox N cap w Z m j,
          presievedCoefficient N cap w Z ((N : ℝ) ^ ell) B (e * ps.prod) *
            F (prefix * (e * ps.prod)))) =
    ∑ a ∈ groupSupport N cap m w Z out.1,
      ∑ b ∈ groupSupport N cap m w Z out.2.1,
        ∑ q3 ∈ attachedSupport N cap m w Z out.2.2,
          atomScalar j out * gamma N cap m w Z out.1 a *
            gamma N cap m w Z out.2.1 b * attachedGamma N cap m r w Z B out.2.2 q3 *
              F (prefix * (a * b * q3)) := by
  calc
    _ = ∑ e ∈ actualSmallRosserSupport N cap w, meshScalar N cap w B e j *
        (∑ ps ∈ meshPrimeBox N cap w Z m j,
          (if rawUpperGate ((N : ℝ) ^ ell) ps.prod then
            (ArithmeticFunction.moebius ps.prod : ℝ) else 0) *
              F (prefix * (e * ps.prod))) := by
      apply Finset.sum_congr rfl
      intro e he
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ps hps
      obtain ⟨hg, hs⟩ := inner_list_gate_and_sign hN w Z ell hj ps hps
      rw [inner_list_actual_presieved_value hN w Z ell B hL hj he ps hps,
        if_pos hg, hs]
      dsimp only [meshScalar]
      ring
    _ = _ := mesh_inner_signed_beta_three_convolution hN w Z ell B hj D A yz prefix F

end
end ImbalancedChen.P5Z.ActualInnerMeshSeparatedGamma
