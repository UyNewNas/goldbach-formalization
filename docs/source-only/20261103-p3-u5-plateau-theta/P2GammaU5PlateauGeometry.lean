import ImbalancedChen.P2GammaRootFiberRelative
import ImbalancedChen.ActualPrimeBoxMass

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
A real positive-area constant-level piece of the ORIGINAL U5 selector.
The root is not rounded or replaced: on the displayed separated box its
max formula equals its own constant B(a) branch. All target exclusions,
strict pair order and half-open endpoints remain in the actual carrier.
This is one genuine root fibre, not coverage of every causal history.
-/
namespace ImbalancedChen.P2GammaU5PlateauGeometry
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaSelectedPhysicalTheta P2GammaRootFiberRelative
open P2OriginalU5SmallPartnerRootPayment
open P5OriginalU5CausalFinite (pairSupport coordinates)

/-- Original constant branch, NOT the global cap 153/256. -/
def plateauLevel : ℝ := VariableEnvelope.B Part5OriginalUpsilon5CausalDictionary.a

theorem plateauLevel_exact : plateauLevel = (90621/160000 : ℝ) := by
  norm_num [plateauLevel,VariableEnvelope.B,VariableEnvelope.cap,
    Part5OriginalUpsilon5CausalDictionary.a]

def plateauQ (N : ℕ) : ℝ := (N : ℝ)^plateauLevel

def boxLo : Fin 2 → ℝ := ![1/10,3/25]
def boxHi : Fin 2 → ℝ := ![11/100,13/100]

def rectangle (N : ℕ) : Finset Pair :=
  (actualPrimeBoxTuples N boxLo boxHi).image (fun p => (p 0,p 1))

def plateauFiber (N : ℕ) : Finset Pair :=
  rootFiber N (plateauQ N) (fun _ => True)

theorem tuple_pair_eta (p : Fin 2 → ℕ) : ![p 0,p 1] = p := by
  funext i
  fin_cases i <;> rfl

theorem mem_rectangle (N : ℕ) (t : Pair) :
    t ∈ rectangle N ↔ ![t.1,t.2] ∈ actualPrimeBoxTuples N boxLo boxHi := by
  constructor
  · intro ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    simpa only [tuple_pair_eta] using hp
  · intro ht
    exact Finset.mem_image.mpr ⟨![t.1,t.2],ht,rfl⟩

/-- Closed box geometry is stronger than the half-open arithmetic box.
Both nonconstant branches are strictly below the original constant. -/
theorem original_level_on_box {u t : ℝ}
    (hu0 : 1/10 ≤ u) (hu1 : u ≤ 11/100)
    (ht0 : 3/25 ≤ t) (ht1 : t ≤ 13/100) :
    Part5OriginalUpsilon5CausalDictionary.level u t = plateauLevel := by
  have htmu : t ≤ VariableEnvelope.mu := by
    dsimp [VariableEnvelope.mu]
    linarith
  have hsum : VariableEnvelope.mu ≤ t+u := by
    dsimp [VariableEnvelope.mu]
    linarith
  have hA : VariableEnvelope.A t ≤ plateauLevel := by
    rw [plateauLevel_exact]
    dsimp [VariableEnvelope.A]
    linarith
  have hC : VariableEnvelope.C (t+u) ≤ plateauLevel := by
    rw [plateauLevel_exact]
    dsimp [VariableEnvelope.C]
    linarith
  unfold Part5OriginalUpsilon5CausalDictionary.level
  rw [VariableEnvelope.v_eq_A htmu,VariableEnvelope.v_eq_C hsum]
  change max (VariableEnvelope.A t) (max (VariableEnvelope.C (t+u)) plateauLevel) = _
  rw [max_eq_right hC,max_eq_right hA]

theorem rectangle_subset_pairSupport {N : ℕ} (hN : 2 ≤ N) :
    rectangle N ⊆ pairSupport N := by
  intro t ht
  have h := mem_actualPrimeBoxTuples_iff.mp ((mem_rectangle N t).mp ht)
  have h0 : t.1.Prime ∧ ¬t.1 ∣ N ∧
      (N : ℝ)^(1/10 : ℝ) ≤ t.1 ∧ (t.1 : ℝ) < (N : ℝ)^(11/100 : ℝ) := by
    simpa only [boxLo,boxHi,Matrix.cons_val_zero] using h 0
  have h1 : t.2.Prime ∧ ¬t.2 ∣ N ∧
      (N : ℝ)^(3/25 : ℝ) ≤ t.2 ∧ (t.2 : ℝ) < (N : ℝ)^(13/100 : ℝ) := by
    simpa only [boxLo,boxHi,Matrix.cons_val_one] using h 1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpN : (t.1 : ℝ) < N := h0.2.2.2.trans_le (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (11/100 : ℝ) ≤ 1))
  have hqN : (t.2 : ℝ) < N := h1.2.2.2.trans_le (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (13/100 : ℝ) ≤ 1))
  have hord : t.1 < t.2 := by
    exact_mod_cast h0.2.2.2.trans_le
      ((Real.rpow_le_rpow_of_exponent_le hNr
        (by norm_num : (11/100 : ℝ) ≤ 3/25)).trans h1.2.2.1)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,hord,?_⟩
  · exact mem_chenAdditivePrimeCarrier.mpr
      ⟨by exact_mod_cast hpN,h0.1,h0.1.coprime_iff_not_dvd.mpr h0.2.1⟩
  · exact mem_chenAdditivePrimeCarrier.mpr
      ⟨by exact_mod_cast hqN,h1.1,h1.1.coprime_iff_not_dvd.mpr h1.2.1⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hNr
      (by norm_num : (417/5000 : ℝ) ≤ 1/10)).trans h0.2.2.1
  · exact h1.2.2.2.trans_le (Real.rpow_le_rpow_of_exponent_le hNr
      (by norm_num : (13/100 : ℝ) ≤ 19/125))

theorem rectangle_coordinates {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ rectangle N) :
    ∀ i : Fin 2,boxLo i ≤ coordinates N t i ∧ coordinates N t i < boxHi i := by
  have h := mem_actualPrimeBoxTuples_iff.mp ((mem_rectangle N t).mp ht)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hp := actualPrimeTupleLog_rpow (show 1 < N by omega) ![t.1,t.2]
    (fun i => (h i).1.pos)
  intro i
  constructor
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    change (N : ℝ)^boxLo i ≤ (N : ℝ)^actualPrimeTupleLog N ![t.1,t.2] i
    rw [hp i]
    exact (h i).2.2.1
  · apply (Real.rpow_lt_rpow_left_iff hNr).mp
    change (N : ℝ)^actualPrimeTupleLog N ![t.1,t.2] i < (N : ℝ)^boxHi i
    rw [hp i]
    exact (h i).2.2.2

theorem rectangle_rootQ {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ rectangle N) : rootQ N t = plateauQ N := by
  have hx := rectangle_coordinates hN ht
  have h0 := hx 0
  have h1 := hx 1
  simp only [boxLo,boxHi,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  unfold rootQ plateauQ
  rw [original_level_on_box h0.1 h0.2.le h1.1 h1.2.le]

/-- All original U5 pairs already satisfy the upper residual-domain test;
this is not restricted to the new plateau rectangle. -/
theorem root_residual_le_target {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ pairSupport N) : rootQ N t/((t.1*t.2 : ℕ) : ℝ) ≤ N := by
  have hd : (1 : ℝ) ≤ ((t.1*t.2 : ℕ) : ℝ) := by
    exact_mod_cast pair_product_pos ht
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hroot : rootQ N t ≤ (N : ℝ) :=
    (root_level_cap (show 1 ≤ N by omega) t).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
        (by norm_num : (153/256 : ℝ) ≤ 1))
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ))).mpr
  exact hroot.trans (by nlinarith [Nat.cast_nonneg N])

/-- The two residual tests do not discard any original pair whose root
level equals Q. This does not make distinct root levels identical. -/
theorem rootFiber_eq_original_level_filter {N : ℕ} (hN : 2 ≤ N)
    (Qphys : ℝ) (keep : Pair → Prop) :
    rootFiber N Qphys keep =
      (pairSupport N).filter (fun t => keep t ∧ rootQ N t = Qphys) := by
  ext t
  simp only [rootFiber,Finset.mem_filter]
  constructor
  · rintro ⟨ht,hkeep,heq,_⟩
    exact ⟨ht,hkeep,heq⟩
  · rintro ⟨ht,hkeep,heq⟩
    refine ⟨ht,hkeep,heq,?_,?_⟩
    · simpa only [← heq] using root_residual_gt_one hN ht
    · simpa only [← heq] using root_residual_le_target hN ht

theorem rectangle_subset_plateauFiber {N : ℕ} (hN : 2 ≤ N) :
    rectangle N ⊆ plateauFiber N := by
  intro t ht
  have hp := rectangle_subset_pairSupport hN ht
  rw [plateauFiber,rootFiber_eq_original_level_filter hN]
  exact Finset.mem_filter.mpr ⟨hp,True.intro,rectangle_rootQ hN ht⟩

end
end ImbalancedChen.P2GammaU5PlateauGeometry
