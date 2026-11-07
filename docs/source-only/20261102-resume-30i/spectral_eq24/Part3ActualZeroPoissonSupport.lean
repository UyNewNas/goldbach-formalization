import ImbalancedChen.Part3ActualZeroPoissonKernel
import ImbalancedChen.Part3ActualCountedSpectralPolynomial

/-!
Source only; uncompiled; zero formal credit.
The actual signed output support supplies U*Z in the physical zero-mode
bound. The literal H cutoff costs one explicit poissonLoss; no fictitious
dyadic y length or unsupported U*Z cardinality is assumed. H's counted
Eq. (25) polynomial then consumes the physical estimate.
-/

namespace ImbalancedChen.Part3.ActualZeroPoissonSupport20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open LichtmanSignedDifferenceMultiplicity OriginalSignedCountingNorm20261028
open ActualZeroPoissonKernel20261102 ActualOriginalSpectralScales20261028
open ActualOccupiedCountingScale20261102 ActualCountedSpectralPolynomial20261102
open ActualReturnedPolynomialCompression20261102 ActualSpectralDoubleCauchyNormalization20261028
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open OriginalLambdaTrimPoissonFamily20261028 ActualMediumVarianceAtomBindingSourceOnly

private theorem frequency_mem_iff {H : ℝ} (hH : 0 ≤ H) {h : ℤ} :
    h ∈ frequencyCarrier H ↔ h ≠ 0 ∧ (h.natAbs : ℝ) ≤ H := by
  constructor
  · intro hh
    rcases mem_union.mp hh with hh | hh
    · obtain ⟨n,hn,rfl⟩ := mem_image.mp hh
      obtain ⟨hnlo,hnhi⟩ := mem_Icc.mp hn
      refine ⟨by omega,?_⟩
      simpa only [Int.natAbs_natCast] using
        (show (n : ℝ) ≤ Nat.floor H by exact_mod_cast hnhi).trans (Nat.floor_le hH)
    · obtain ⟨n,hn,rfl⟩ := mem_image.mp hh
      obtain ⟨hnlo,hnhi⟩ := mem_Icc.mp hn
      refine ⟨by omega,?_⟩
      simpa only [Int.natAbs_neg,Int.natAbs_natCast] using
        (show (n : ℝ) ≤ Nat.floor H by exact_mod_cast hnhi).trans (Nat.floor_le hH)
  · rintro ⟨hne,hbound⟩
    have hn : h.natAbs ∈ Icc 1 (Nat.floor H) :=
      mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr hne),Nat.le_floor hbound⟩
    rcases Int.natAbs_eq h with heq | heq
    · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨h.natAbs,hn,heq.symm⟩))
    · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨h.natAbs,hn,heq.symm⟩))

private theorem frequency_card_le {H : ℝ} (hH : 0 ≤ H) :
    ((frequencyCarrier H).card : ℝ) ≤ 2*H := by
  have hc : (frequencyCarrier H).card ≤ 2*Nat.floor H := by
    calc
      _ ≤ ((Icc 1 (Nat.floor H)).image (fun n : ℕ => (n : ℤ))).card +
          ((Icc 1 (Nat.floor H)).image (fun n : ℕ => -(n : ℤ))).card := card_union_le _ _
      _ ≤ (Icc 1 (Nat.floor H)).card + (Icc 1 (Nat.floor H)).card :=
        Nat.add_le_add card_image_le card_image_le
      _ = _ := by simp only [Nat.card_Icc]; omega
  calc
    _ ≤ 2*(Nat.floor H : ℝ) := by exact_mod_cast hc
    _ ≤ 2*H := mul_le_mul_of_nonneg_left (Nat.floor_le hH) (by norm_num)

private theorem cast_natAbs (h : ℤ) : (h.natAbs : ℝ) = |(h : ℝ)| := by
  simpa only [Int.cast_natCast,Int.cast_abs] using
    congrArg (fun n : ℤ => (n : ℝ)) (Int.natCast_natAbs h)

/-- Both h signs and nonzero y are retained. No lower bound H>=1 is
needed; a short literal source remains empty. -/
theorem outputCarrier_subset_box {S H F : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    outputCarrier S H F ⊆
      Ioc 0 (Nat.floor (4*S^2)) ×ˢ frequencyCarrier (8*F*H*S) := by
  intro zy hzy
  have hyne := output_y_ne_zero hzy
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hzy
  obtain ⟨hprod,hne⟩ := mem_filter.mp ht
  obtain ⟨hss,hhh⟩ := mem_product.mp hprod
  obtain ⟨hs1,hs2f⟩ := mem_product.mp hss
  obtain ⟨hs2,hf⟩ := mem_product.mp hs2f
  obtain ⟨hh1,hh2⟩ := mem_product.mp hhh
  have hs1pos := (mem_Ioc.mp (mem_filter.mp hs1).1).1
  have hs2pos := (mem_Ioc.mp (mem_filter.mp hs2).1).1
  have hs1hi := (mem_filter.mp hs1).2.2.le
  have hs2hi := (mem_filter.mp hs2).2.2.le
  have hfhi := (mem_filter.mp hf).2.2.le
  have hh1hi := ((frequency_mem_iff hH).mp hh1).2
  have hh2hi := ((frequency_mem_iff hH).mp hh2).2
  have hdiff : ((difference t).natAbs : ℝ) ≤ 4*H*S := by
    calc
      _ = |(t.2.1 : ℝ)*(t.1.1 : ℝ)-(t.2.2 : ℝ)*(t.1.2.1 : ℝ)| := by
        simp only [cast_natAbs,difference,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
      _ ≤ |(t.2.1 : ℝ)*(t.1.1 : ℝ)|+|(t.2.2 : ℝ)*(t.1.2.1 : ℝ)| := abs_sub _ _
      _ = (t.2.1.natAbs : ℝ)*(t.1.1 : ℝ) +
          (t.2.2.natAbs : ℝ)*(t.1.2.1 : ℝ) := by
        rw [abs_mul,abs_mul,← cast_natAbs t.2.1,← cast_natAbs t.2.2,
          abs_of_nonneg (Nat.cast_nonneg t.1.1),abs_of_nonneg (Nat.cast_nonneg t.1.2.1)]
      _ ≤ H*(2*S)+H*(2*S) := add_le_add
        (mul_le_mul hh1hi hs1hi (Nat.cast_nonneg _) hH)
        (mul_le_mul hh2hi hs2hi (Nat.cast_nonneg _) hH)
      _ = _ := by ring
  apply mem_product.mpr
  constructor
  · apply mem_Ioc.mpr
    refine ⟨Nat.mul_pos hs1pos hs2pos,?_⟩
    apply Nat.le_floor
    change ((t.1.1*t.1.2.1 : ℕ) : ℝ) ≤ 4*S^2
    rw [Nat.cast_mul]
    calc
      _ ≤ (2*S)*(2*S) := mul_le_mul hs1hi hs2hi (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  · apply (frequency_mem_iff (by positivity)).mpr
    refine ⟨hyne,?_⟩
    change ((((t.1.2.2 : ℤ)*difference t).natAbs) : ℝ) ≤ _
    rw [Int.natAbs_mul,Int.natAbs_natCast,Nat.cast_mul]
    calc
      _ ≤ (2*F)*(4*H*S) := mul_le_mul hfhi hdiff (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring

theorem outputCarrier_card_le {S H F : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    ((outputCarrier S H F).card : ℝ) ≤ 64*F*H*S^3 := by
  have hc := card_le_card (outputCarrier_subset_box hS hH hF)
  calc
    _ ≤ ((Ioc 0 (Nat.floor (4*S^2)) ×ˢ frequencyCarrier (8*F*H*S)).card : ℝ) := by
      exact_mod_cast hc
    _ = (Nat.floor (4*S^2) : ℝ)*((frequencyCarrier (8*F*H*S)).card : ℝ) := by
      simp only [card_product,Nat.card_Ioc,Nat.sub_zero,Nat.cast_mul]
    _ ≤ (4*S^2)*(2*(8*F*H*S)) := mul_le_mul
      (Nat.floor_le (by positivity)) (frequency_card_le (by positivity))
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- The occupied original H, rather than an independently chosen y
length, supplies the physical U*Z factor. The cutoff loss is explicit. -/
theorem occupied_outputCarrier_card_le {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z) :
    ((outputCarrier (roughS k) (keyRealH atom k) (countingF atom)).card : ℝ) ≤
      64*poissonLoss atom k*spectralU atom k*spectralZ k := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hS : 0 ≤ roughS k := zero_le_one.trans (rough_scales_one_le k).2
  have hF : 0 ≤ countingF atom := by unfold countingF; positivity
  have hH := (poisson_nonneg hA k).1
  calc
    _ ≤ 64*countingF atom*keyRealH atom k*(roughS k)^3 := outputCarrier_card_le hS hH hF
    _ ≤ 64*countingF atom*countingH atom k (poissonLoss atom k)*(roughS k)^3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (actual_H_le_countingH hA z k hk) (by positivity))
        (pow_nonneg hS _)
    _ = _ := by
      unfold countingF countingH spectralU spectralZ
      field_simp [hQ.ne',hM.ne']
      ring

def occupiedZeroSource (atom : MediumAtom) (k : Key) (A : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) : ℂ :=
  actualZeroSource (roughS k) (keyRealH atom k) (countingF atom)
    (spectralC atom k) (spectralB atom k) A atom.residue lambda omega eps

def zeroBranchCost (atom : MediumAtom) (k : Key) : ℝ :=
  2304*zeroFourierMass^2*
    (residueDivisorMaximum (roughS k) (keyRealH atom k) (countingF atom) atom.residue : ℝ)^2*
    poissonLoss atom k

theorem zeroBranchCost_nonneg {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) : 0 ≤ zeroBranchCost atom k := by
  have hL := (poisson_nonneg hA k).2
  unfold zeroBranchCost
  positivity

/-- The actual physical m=0 branch reaches the literal zero-Poisson
monomial of (25). All coefficient, residue-divisor and H costs are visible.
No kernel estimate or source equality is assumed. -/
theorem occupiedZeroSource_sq_le_zeroPolynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (ha : atom.residue ≠ 0) (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) :
    ‖occupiedZeroSource atom k A lambda omega eps‖^2 ≤
      zeroBranchCost atom k*zeroPoissonPolynomial atom k*sourceNorm atom k A lambda omega eps 1 := by
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hnorm := countingNorm_nonneg (roughS k) (keyRealH atom k) (countingF atom)
    A atom.residue lambda omega eps 1
  have hkernel := actualZeroSource_sq_le hC hD.le (roughS k) (keyRealH atom k)
    (countingF atom) A atom.residue ha lambda omega eps
  calc
    _ ≤ _ := hkernel
    _ ≤ (6*spectralB atom k*zeroFourierMass*
        (residueDivisorMaximum (roughS k) (keyRealH atom k) (countingF atom) atom.residue : ℝ))^2*
        (64*poissonLoss atom k*spectralU atom k*spectralZ k)*
        countingNorm (roughS k) (keyRealH atom k) (countingF atom)
          A atom.residue lambda omega eps 1 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (occupied_outputCarrier_card_le hA z k hk) (sq_nonneg _)) hnorm
    _ = _ := by unfold zeroBranchCost zeroPoissonPolynomial sourceNorm; ring

/-- The literal H polynomial is an actual consumer of the physical branch,
not a premise. This inequality does not estimate any nonzero m term. -/
theorem occupiedZeroSource_sq_le_countedPolynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (ha : atom.residue ≠ 0) (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nus : Finset ℕ) :
    ‖occupiedZeroSource atom k A lambda omega eps‖^2 ≤
      zeroBranchCost atom k*countedPolynomial atom k A lambda omega eps nus := by
  have hn : 0 ≤ sourceNorm atom k A lambda omega eps 1 := countingNorm_nonneg _ _ _ _ _ _ _ _ _
  have hreg : 0 ≤ ∑ nu ∈ nus,
      ((atom.residue.natAbs : ℝ)*(nu : ℝ))^theta*regularPolynomial atom k nu*
        sourceNorm atom k A lambda omega eps nu := by
    apply sum_nonneg
    intro nu hnu
    have hr := regularPolynomial_nonneg hA k nu
    have hs : 0 ≤ sourceNorm atom k A lambda omega eps nu := countingNorm_nonneg _ _ _ _ _ _ _ _ _
    positivity
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hexc : 0 ≤ exceptionalPolynomial atom k := by
    unfold exceptionalPolynomial ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalPolynomial
    positivity
  have hpoly : zeroPoissonPolynomial atom k*sourceNorm atom k A lambda omega eps 1 ≤
      countedPolynomial atom k A lambda omega eps nus := by
    unfold countedPolynomial
    nlinarith only [hreg,mul_nonneg hexc hn]
  exact (occupiedZeroSource_sq_le_zeroPolynomial hA ha z k hk A lambda omega eps).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hpoly (zeroBranchCost_nonneg hA k))

/-- Physical m=0, with the actual coefficient count and H's D1
normalization both discharged. The geometric gates are exactly H's. -/
theorem normalized_occupiedZeroSource {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (hsigma : 0 < sigma) (ha : atom.residue ≠ 0) (z : ℝ) (k : Key)
    (hk : k ∈ originalNumericKeys atom z)
    (hB : (spectralB atom k)^2 ≤ atom.scale) (ha1 : 1 ≤ (atom.residue.natAbs : ℝ))
    (hshort : 1+keyRealH atom k/roughS k ≤ 2)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) :
    normalizingFactor atom k*‖occupiedZeroSource atom k A lambda omega eps‖^2 ≤
      zeroBranchCost atom k*sourceDivisorCost atom k*(poissonLoss atom k)^2*D1 atom k := by
  have hzero := occupiedZeroSource_sq_le_zeroPolynomial hA ha z k hk A lambda omega eps
  have hcount := sourceNorm_le_countingMass hA hsigma z k hk hshort
    A lambda omega eps hlambda homega heps 1 (by norm_num)
  simp only [Nat.cast_one,div_one] at hcount
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hp0 : 0 ≤ zeroPoissonPolynomial atom k := by unfold zeroPoissonPolynomial; positivity
  have hq0 := normalizingFactor_nonneg atom k
  have hcost := zeroBranchCost_nonneg hA k
  have hK := sourceDivisorCost_nonneg atom k
  calc
    _ ≤ normalizingFactor atom k*(zeroBranchCost atom k*zeroPoissonPolynomial atom k*
        sourceNorm atom k A lambda omega eps 1) := mul_le_mul_of_nonneg_left hzero hq0
    _ ≤ normalizingFactor atom k*(zeroBranchCost atom k*zeroPoissonPolynomial atom k*
        (sourceDivisorCost atom k*countingMass atom k (poissonLoss atom k))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcount (mul_nonneg hcost hp0)) hq0
    _ = (zeroBranchCost atom k*sourceDivisorCost atom k)*
        (fourthNormalization atom k (poissonLoss atom k)*zeroPoissonPolynomial atom k) := by
      rw [← normalizingFactor_mul_mass]
      ring
    _ ≤ (zeroBranchCost atom k*sourceDivisorCost atom k)*
        ((poissonLoss atom k)^2*D1 atom k) := mul_le_mul_of_nonneg_left
      (normalized_zeroPoissonPolynomial hA k hB ha1 (poissonLoss atom k)) (mul_nonneg hcost hK)
    _ = _ := by ring

/-- One original threshold precedes all atoms and every genuine coefficient.
This completes only the m=0 physical branch, with explicit finite costs. -/
theorem exists_normalized_occupiedZeroSource_threshold (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 atom → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
      ∀ (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ),
      (∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1) →
      (∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1) →
      (∀ zy, ‖eps zy‖ ≤ 1) →
      normalizingFactor atom k*‖occupiedZeroSource atom k A lambda omega eps‖^2 ≤
        zeroBranchCost atom k*sourceDivisorCost atom k*(poissonLoss atom k)^2*D1 atom k := by
  obtain ⟨x0,hx0,hgeometry⟩ :=
    ActualSpectralUniformGeometry20261028.exists_actual_spectral_geometry_threshold sigma hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hc0 hA hx z k hk A lambda omega eps hlambda homega heps
  obtain ⟨hD0,hB,hH,hshort⟩ := hgeometry B kappa c0 atom hA hx z k hk
  obtain ⟨hN,hM,hQ,hxone⟩ := scale_facts hA
  have haPos : (0 : ℝ) < atom.residue.natAbs :=
    (mul_pos hc0 (zero_lt_one.trans hxone)).trans_le hA.2.2.2.2.2.2.1
  have haNat : 0 < atom.residue.natAbs := by exact_mod_cast haPos
  have ha : atom.residue ≠ 0 := Int.natAbs_pos.mp haNat
  have ha1 : (1 : ℝ) ≤ atom.residue.natAbs := by exact_mod_cast Nat.succ_le_iff.mpr haNat
  exact normalized_occupiedZeroSource hA hsigma ha z k hk hB.le ha1 hshort
    A lambda omega eps hlambda homega heps

end
end ImbalancedChen.Part3.ActualZeroPoissonSupport20261102
