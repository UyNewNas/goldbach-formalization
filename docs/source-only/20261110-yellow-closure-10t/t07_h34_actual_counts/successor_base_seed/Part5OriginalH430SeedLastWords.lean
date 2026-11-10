import ImbalancedChen.P2EnhancedNonunitLastDictionary
import ImbalancedChen.P2SeedOmegaLastFullMassBounds

/-! The native positive-remainder integrals and the original closed seed caps
for Γ20 and Γ21. The two quotient-one masses have their own dimensions. -/
namespace ImbalancedChen.Part5OriginalH430SeedLastWords
noncomputable section
open Set MeasureTheory Filter Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2SeedOmegaLiteralFibre (a2 a3 b)
open P2SeedOmegaLastSwitchGeometry P2SeedOmegaLastUnitIntegrals P2SeedOmegaLastFullMassBounds
open P2EnhancedNonunitMarkedMass P2EnhancedNonunitLastDictionary
open P2SeedOmegaLiteralFunctional (switchedMass)
open scoped Classical BigOperators

private theorem domain20 (alpha : ℝ) : HighNonunitLegal.D20 a2 a3 b alpha ⊆ D20 := by
  intro x hx
  obtain ⟨⟨hx0,h0x,h1,hm,hlast⟩,_⟩ := hx
  refine ⟨⟨hx0,h0x⟩,fun i => ⟨h1.trans (hm ?_), (hm (Fin.le_last i.succ)).trans hlast⟩,
    fun i j hij => hm (show i.succ≤j.succ from Nat.succ_le_succ hij)⟩
  change 1 ≤ i.val+1
  omega

private theorem domain21 (alpha : ℝ) : HighNonunitLegal.D21 a3 b alpha ⊆ D21 := by
  intro x hx
  obtain ⟨⟨hx0,hm,hlast⟩,_⟩ := hx
  exact ⟨fun i => ⟨hx0.trans (hm (Fin.zero_le i)),(hm (Fin.le_last i)).trans hlast⟩,hm⟩

private theorem upperOnLegal {m : ℕ} (j : Fin m) (alpha : ℝ) (x : Fin m → ℝ)
    (hx : x ∈ HighNonunitLegal.legal j alpha) (hpos : ∀ i, 0<x i) :
    HighNonunitLegal.G j alpha x * continuousDensity x ≤
      nonunitKernel (fun _ => 1) alpha (x j) x := by
  have he : (∑ i,x i)+x j≤alpha := hx
  have hl : total x ≤ alpha-x j := by unfold total; linarith only [he]
  have hw := buchstab_le_one (rough_argument_ge_one (hpos j) hl)
  rw [HighNonunitLegal.weighted_formula hx,nonunitKernel,if_pos hl]
  exact div_le_div_of_nonneg_right hw (mul_nonneg (hpos j).le (Finset.prod_pos (fun i _ => hpos i)).le)

private theorem oneBounds : ∀ t : ℝ, 1≤t → 0≤(fun _ : ℝ => (1:ℝ)) t ∧
    (fun _ : ℝ => (1:ℝ)) t ≤ 1 := fun _ _ => ⟨zero_le_one,le_rfl⟩

theorem original_last_full_costs (alpha : ℝ) :
    nonunitIntegral [2,3,3,3,3] alpha + unit20Mass alpha ≤ switchedMass (11 : Fin 13) ∧
    nonunitIntegral [3,3,3,3,3,3] alpha + unit21Mass alpha ≤ switchedMass (12 : Fin 13) := by
  let one := fun _ : ℝ => (1:ℝ)
  obtain ⟨hc20,hc21⟩ := full_masses_le_original one measurable_const oneBounds alpha
  have h20 : IntegrableOn (fun x => nonunitKernel one alpha (w20 x) x) D20 :=
    (integrable_indicator_iff measurableSet_D20).mp
      (integrable_nonunit20Density one measurable_const oneBounds alpha)
  have h21 : IntegrableOn (fun x => nonunitKernel one alpha (w21 x) x) D21 :=
    (integrable_indicator_iff measurableSet_D21).mp
      (integrable_nonunit21Density one measurable_const oneBounds alpha)
  have h20' : nonunitIntegral [2,3,3,3,3] alpha ≤ nonunit20Mass one alpha := by
    rw [nonunitIntegral20_eq_K20]
    calc
      _ ≤ ∫ x in HighNonunitLegal.D20 a2 a3 b alpha, nonunitKernel one alpha (w20 x) x := by
        apply setIntegral_mono_on
          (HighNonunitLegal.K20_integrable (by norm_num [a2]) (by norm_num [b]) alpha)
          (h20.mono_set (domain20 alpha)) (HighNonunitLegal.D20_measurable ..)
        exact fun x hx => upperOnLegal 3 alpha x hx.2 (fun i =>
          (by norm_num [a2] : 0 < a2).trans_le (D20_coordinate_bounds (domain20 alpha hx) i).1)
      _ ≤ _ := by
        apply setIntegral_mono_set h20 _ (Eventually.of_forall (domain20 alpha))
        filter_upwards [ae_restrict_mem measurableSet_D20] with x hx
        exact (nonunit20_bounds one oneBounds alpha hx).1
  have h21' : nonunitIntegral [3,3,3,3,3,3] alpha ≤ nonunit21Mass one alpha := by
    rw [nonunitIntegral21_eq_K21]
    calc
      _ ≤ ∫ x in HighNonunitLegal.D21 a3 b alpha, nonunitKernel one alpha (w21 x) x := by
        apply setIntegral_mono_on
          (HighNonunitLegal.K21_integrable (by norm_num [a3]) (by norm_num [b]) alpha)
          (h21.mono_set (domain21 alpha)) (HighNonunitLegal.D21_measurable ..)
        exact fun x hx => upperOnLegal 4 alpha x hx.2 (fun i =>
          (by norm_num [a3] : 0 < a3).trans_le (D21_coordinate_bounds (domain21 alpha hx) i).1)
      _ ≤ _ := by
        apply setIntegral_mono_set h21 _ (Eventually.of_forall (domain21 alpha))
        filter_upwards [ae_restrict_mem measurableSet_D21] with x hx
        exact (nonunit21_bounds one oneBounds alpha hx).1
  exact ⟨(add_le_add_right h20' _).trans hc20, (add_le_add_right h21' _).trans hc21⟩

end
end ImbalancedChen.Part5OriginalH430SeedLastWords
