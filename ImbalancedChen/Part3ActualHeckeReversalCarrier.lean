import ImbalancedChen.Part3ActualHeckeReversalInvolution
import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The literal partial Atkin-Lehner W-image of the actual prime-level reduced
carrier is measurable, has only actual +/-I deck returns, and its actual
prime-level translates cover conullly. The normalizer is paid in both
directions using the proved W-square deck transformation. No generic
canonical-carrier comparison is copied and no quotient measure conclusion
is asserted: the public comparison API remains a separate dependency.
-/

namespace ImbalancedChen.Part3.ActualHeckeReversalCarrier20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ActualHeckeReversalInvolution20261026b ActualPrimeHeckeRealBranch20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierInteriorUniqueness20261025a

variable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)

/-- Reverse deck transport is derived, rather than an assumed normalizer
surjectivity: conjugation squared is the actual W-square inner action. -/
theorem reversal_deck_left (g : CongruenceSubgroup.Gamma0 (N*p)) :
    ∃ h : CongruenceSubgroup.Gamma0 (N*p),
      castIntegral g * reversalSL N p hp hpN = reversalSL N p hp hpN * castIntegral h := by
  obtain ⟨a,ha⟩ := reversal_deck N p hp hpN g
  let k := reversalSquareDeck N p hp hpN
  let h : CongruenceSubgroup.Gamma0 (N*p) := k⁻¹*a*k
  have ha' : castIntegral a = reversalSL N p hp hpN * castIntegral g * (reversalSL N p hp hpN)⁻¹ := by
    rw [ha]
    group
  have hh : castIntegral h = (castIntegral k)⁻¹ * castIntegral a * castIntegral k := by
    simp only [h,Subgroup.coe_mul,Subgroup.coe_inv,castIntegral,map_mul,map_inv]
  refine ⟨h,?_⟩
  rw [hh,ha']
  change castIntegral g * reversalSL N p hp hpN =
    reversalSL N p hp hpN * ((castIntegral (reversalSquareDeck N p hp hpN))⁻¹ *
      (reversalSL N p hp hpN * castIntegral g * (reversalSL N p hp hpN)⁻¹) *
        castIntegral (reversalSquareDeck N p hp hpN))
  rw [← reversal_square N p hp hpN]
  group

theorem reversalAction_measurePreserving :
    MeasurePreserving (fun z : ℍ => reversalSL N p hp hpN • z)
      (volume : Measure ℍ) (volume : Measure ℍ) := by
  change MeasurePreserving (fun z : ℍ => SpecialLinearGroup.mapGL ℝ (reversalSL N p hp hpN) • z) _ _
  exact measurePreserving_smul _ _

theorem reversalAction_embedding : MeasurableEmbedding (fun z : ℍ => reversalSL N p hp hpN • z) := by
  change MeasurableEmbedding (fun z : ℍ => SpecialLinearGroup.mapGL ℝ (reversalSL N p hp hpN) • z)
  exact measurableEmbedding_const_smul _

def reversalCarrier [NeZero (N*p)] : Set ℍ :=
  (fun z : ℍ => reversalSL N p hp hpN • z) '' reducedCarrier (N*p)

theorem reversalCarrier_measurable [NeZero (N*p)] : MeasurableSet (reversalCarrier N p hp hpN) :=
  (reversalAction_embedding N p hp hpN).measurableSet_image.mpr (reducedCarrier_measurable (N*p))

theorem reversalCarrier_return_kernel [NeZero (N*p)]
    (g : CongruenceSubgroup.Gamma0 (N*p)) {z : ℍ}
    (hz : z ∈ reversalCarrier N p hp hpN) (hgz : g • z ∈ reversalCarrier N p hp hpN) :
    g ∈ gamma0ActionKernel (N*p) := by
  obtain ⟨x,hx,hxz⟩ := hz
  obtain ⟨y,hy,hyz⟩ := hgz
  obtain ⟨h,hh⟩ := reversal_deck_left N p hp hpN g
  have hact (u : ℍ) : g • (reversalSL N p hp hpN • u) = reversalSL N p hp hpN • (h • u) := by
    rw [← castIntegral_smul g,← mul_smul,hh,mul_smul,castIntegral_smul]
  have hmove : h • x = y := by
    apply (MulAction.toPerm (reversalSL N p hp hpN)).injective
    change reversalSL N p hp hpN • (h • x) = reversalSL N p hp hpN • y
    rw [← hact,hxz,hyz]
  have hker : h ∈ gamma0ActionKernel (N*p) :=
    gamma0_open_to_closed_mem_kernel (N*p) h (reducedCarrier_subset_open (N*p) hx)
      (by rw [hmove]; exact hy.1)
  apply (gamma0_actionKernel_iff (N*p) g).mpr
  apply (sl2_fixed_all_iff (g : SL(2, ℤ))).mp
  intro w
  have hfix := (sl2_fixed_all_iff (h : SL(2, ℤ))).mpr
    ((gamma0_actionKernel_iff (N*p) h).mp hker) ((reversalSL N p hp hpN)⁻¹ • w)
  have heq := hact ((reversalSL N p hp hpN)⁻¹ • w)
  rw [smul_inv_smul,hfix,smul_inv_smul] at heq
  exact heq

/-- True conull orbit coverage of the W-image carrier. Whole-H volume is
used only to transport the explicit null omitted set; no quotient measure
is inferred from whole-H preservation. -/
theorem reversalCarrier_orbit_cover [NeZero (N*p)] :
    ∀ᵐ z ∂(volume : Measure ℍ), ∃ g : CongruenceSubgroup.Gamma0 (N*p),
      g • z ∈ reversalCarrier N p hp hpN := by
  have hmp : MeasurePreserving (fun z : ℍ => (reversalSL N p hp hpN)⁻¹ • z)
      (volume : Measure ℍ) (volume : Measure ℍ) := by
    change MeasurePreserving (fun z : ℍ => SpecialLinearGroup.mapGL ℝ ((reversalSL N p hp hpN)⁻¹) • z) _ _
    exact measurePreserving_smul _ _
  have hnull : (volume : Measure ℍ)
      ((fun z : ℍ => (reversalSL N p hp hpN)⁻¹ • z) ⁻¹' (allEffectiveCells (N*p))ᶜ) = 0 := by
    rw [hmp.measure_preimage (allEffectiveCells_measurable (N*p)).compl]
    exact allEffectiveCells_compl_null (N*p)
  have hae : ∀ᵐ z ∂(volume : Measure ℍ), (reversalSL N p hp hpN)⁻¹ • z ∈ allEffectiveCells (N*p) :=
    ae_iff.mpr hnull
  filter_upwards [hae] with z hz
  obtain ⟨q,x,hx,hxz⟩ := mem_iUnion.mp hz
  let a := effectiveRepresentative (N*p) q
  obtain ⟨h,hh⟩ := reversal_deck N p hp hpN a
  have hact : reversalSL N p hp hpN • (a • x) = h • (reversalSL N p hp hpN • x) := by
    rw [← castIntegral_smul a,← mul_smul,hh,mul_smul,castIntegral_smul]
  have hz' : z = h • (reversalSL N p hp hpN • x) := by
    calc
      z = reversalSL N p hp hpN • ((reversalSL N p hp hpN)⁻¹ • z) := (smul_inv_smul _ _).symm
      _ = reversalSL N p hp hpN • (a • x) := congrArg _ hxz.symm
      _ = _ := hact
  refine ⟨h⁻¹,?_⟩
  rw [hz',inv_smul_smul]
  exact ⟨x,hx,rfl⟩

end
end ImbalancedChen.Part3.ActualHeckeReversalCarrier20261026b
