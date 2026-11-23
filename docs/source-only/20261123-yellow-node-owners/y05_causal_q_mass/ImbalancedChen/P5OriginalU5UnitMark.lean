import ImbalancedChen.P5OriginalU5NativeRootCover

/-! Every original ordered pair has its own active complete physical
atom at quotient one, uniformly in the native causal history. -/
namespace ImbalancedChen.P5OriginalU5UnitMark

noncomputable section
open Classical
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV

theorem unit_row {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (he : 0 < e) (he8 : e < 1/8)
    (P : List ℕ → Bool) :
    1 ∈ support N e P ∧ rho N e P 1 = 1 := by
  let cap := Nat.ceil (cutoff N)
  let w := smallCutoff N e
  let z := cutoff N
  let L := smallLevel N e
  have hs : 1 ∈ actualSmallRosserSupport N cap w :=
    Nat.mem_divisors.mpr ⟨one_dvd _, actualSmallPrimeProduct_ne_zero N cap w⟩
  have hr : 1 ∈ fixedEvenRoughSupport P N cap w z := by
    rw [fixedEvenRoughSupport, mem_firstExitRetainedModuli_iff_validSelection]
    exact ⟨[], List.nil_sublist _, True.intro, rfl⟩
  have hcoeff : fixedEvenRoughCoefficient P N cap w z 1 = 1 := by
    change 1 ∈ firstExitRetainedModuli (evenFirstExitPolicy P)
      (roughPrimeUniverse N cap w z) at hr
    simp [fixedEvenRoughCoefficient, firstExitRetainedCoefficient, hr]
  have hb : actualSmallRosserMinus N cap w L 1 = 1 :=
    MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_one
      (actualSmallPrimeProduct_ne_zero N cap w) (attachment_gates hN he he8).1
  refine ⟨Finset.mem_image.mpr ⟨(1,1), Finset.mem_product.mpr ⟨hs,hr⟩, rfl⟩, ?_⟩
  have h := smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt P N cap w z hd)
    (fixedEvenRoughCoefficient P N cap w z)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L) hs hr
  simpa only [smallRoughPairCoefficient, signAttachedCoefficient, hcoeff, hb,
    zero_le_one, if_true, one_mul] using h

theorem original_integer_unit {N : ℕ} (hN : 2 ≤ N) {e : ℝ}
    (he : 0 < e) (he8 : e < 1/8) (P : Policy) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    fullModulus t 1 ∈ moduli N e P ∧ integerRho N e P (fullModulus t 1) = 1 := by
  obtain ⟨hk, hunit⟩ := unit_row hN he he8 (P t)
  refine ⟨P3ActualU6PhysicalRhoPushforward.tagged_physical_mem _ _ _ ht hk, ?_⟩
  rw [integerRho_at_original P (attachment_gates hN he he8).2.2 ht hk]
  have hc : ((rowInteger N e P t 1 : ℤ) : ℝ) = 1 :=
    (P3ActualEvenLowerIntegerRho.actualEvenLowerIntegerRho_cast _ _ _ _ _ _ _).trans hunit
  exact_mod_cast hc

end
end ImbalancedChen.P5OriginalU5UnitMark
