import ImbalancedChen.Part3GlobalFrickeParityProjections
import ImbalancedChen.Part3Gamma0PhysicalClosedDirichletForm

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The actual global Fricke +/- projections intertwine with the genuine
physical energy projection, preserve the actual closed-form and full
Friedrichs domains, and commute with the actual unbounded operator on
its native domain. Both physical mass and the EXISTING closed Dirichlet
pair split into orthogonal channels. No spectral completeness, form
isometry or prescribed domain/pairing conclusion is assumed.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeParityFormDomain20261026b

open Set MeasureTheory
open ImbalancedChen.Part3.InvolutiveHilbertProjection20261026b
open ImbalancedChen.Part3.GlobalFrickeParityProjections20261026b
open ImbalancedChen.Part3.GlobalFrickeClosedEnergyAction20261026b
open ImbalancedChen.Part3.GlobalFrickeFriedrichsIntertwining20261026b
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0PhysicalClosedDirichletForm20261025a

theorem energyPlus_physical (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    physicalProjection N (energyPlus N hN e) = frickePlus N hN (physicalProjection N e) := by
  simp only [energyPlus, frickePlus, plus_apply, map_smul, map_add, energyFricke_physical]

theorem energyMinus_physical (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    physicalProjection N (energyMinus N hN e) = frickeMinus N hN (physicalProjection N e) := by
  simp only [energyMinus, frickeMinus, minus_apply, map_smul, map_sub, energyFricke_physical]

theorem energy_parity_orthogonal (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    inner ℂ (energyPlus N hN d) (energyMinus N hN e) = 0 :=
  projections_orthogonal _ (energyFricke_involutive N hN)
    (fun u v => (energyFricke_inner_flip N hN u v).symm) d e

/-- Physical and energy-space cross terms both vanish, hence the true
unshifted closed Dirichlet cross term vanishes as well. -/
theorem Dirichlet_plus_minus_zero (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    actualDirichletPair N (energyPlus N hN d) (energyMinus N hN e) = 0 := by
  unfold actualDirichletPair
  rw [energy_parity_orthogonal, energyPlus_physical, energyMinus_physical,
    fricke_parity_orthogonal, sub_self]

theorem Dirichlet_minus_plus_zero (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    actualDirichletPair N (energyMinus N hN d) (energyPlus N hN e) = 0 := by
  have h := congrArg star (Dirichlet_plus_minus_zero N hN e d)
  simpa only [actualDirichletPair_star, star_zero] using h

/-- Full sesquilinear splitting, so the diagonal Dirichlet-energy split
includes all actual cross terms rather than discarding them by assertion. -/
theorem Dirichlet_parity_split (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    actualDirichletPair N d e =
      actualDirichletPair N (energyPlus N hN d) (energyPlus N hN e) +
        actualDirichletPair N (energyMinus N hN d) (energyMinus N hN e) := by
  have hd : d = energyPlus N hN d + energyMinus N hN d := (plus_add_minus _ d).symm
  have he : e = energyPlus N hN e + energyMinus N hN e := (plus_add_minus _ e).symm
  calc
    _ = actualDirichletPair N (energyPlus N hN d + energyMinus N hN d)
        (energyPlus N hN e + energyMinus N hN e) := congrArg₂ (actualDirichletPair N) hd he
    _ = _ := by
      rw [actualDirichletPair_add_left, actualDirichletPair_add_right,
        actualDirichletPair_add_right, Dirichlet_plus_minus_zero, Dirichlet_minus_plus_zero]
      simp only [add_zero, zero_add]

theorem completed_energy_norm_split (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    ‖e‖ ^ 2 = ‖energyPlus N hN e‖ ^ 2 + ‖energyMinus N hN e‖ ^ 2 :=
  norm_sq_split _ (energyFricke_involutive N hN)
    (fun u v => (energyFricke_inner_flip N hN u v).symm) e

theorem completed_physical_mass_split (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    ‖physicalProjection N e‖ ^ 2 = ‖physicalProjection N (energyPlus N hN e)‖ ^ 2 +
      ‖physicalProjection N (energyMinus N hN e)‖ ^ 2 := by
  rw [energyPlus_physical, energyMinus_physical]
  exact fricke_mass_split N hN _

theorem parityPlus_mem_formDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ actualEnergyFormDomain N) :
    frickePlus N hN f ∈ actualEnergyFormDomain N := by
  obtain ⟨e, he⟩ := hf
  refine ⟨energyPlus N hN e, ?_⟩
  rw [energyPlus_physical, he]

theorem parityMinus_mem_formDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ actualEnergyFormDomain N) :
    frickeMinus N hN f ∈ actualEnergyFormDomain N := by
  obtain ⟨e, he⟩ := hf
  refine ⟨energyMinus N hN e, ?_⟩
  rw [energyMinus_physical, he]

def formPlus (N : ℕ) [NeZero N] (hN : 0 < N) (u : actualEnergyFormDomain N) : actualEnergyFormDomain N :=
  ⟨frickePlus N hN u, parityPlus_mem_formDomain N hN u.property⟩

def formMinus (N : ℕ) [NeZero N] (hN : 0 < N) (u : actualEnergyFormDomain N) : actualEnergyFormDomain N :=
  ⟨frickeMinus N hN u, parityMinus_mem_formDomain N hN u.property⟩

theorem actualEnergyLift_formPlus (N : ℕ) [NeZero N] (hN : 0 < N) (u : actualEnergyFormDomain N) :
    actualEnergyLift N (formPlus N hN u) = energyPlus N hN (actualEnergyLift N u) := by
  apply physicalProjection_injective N
  simpa only [actualEnergyLift_projection, energyPlus_physical] using
    (rfl : (formPlus N hN u : QuotientL2 N) = frickePlus N hN u)

theorem actualEnergyLift_formMinus (N : ℕ) [NeZero N] (hN : 0 < N) (u : actualEnergyFormDomain N) :
    actualEnergyLift N (formMinus N hN u) = energyMinus N hN (actualEnergyLift N u) := by
  apply physicalProjection_injective N
  simpa only [actualEnergyLift_projection, energyMinus_physical] using
    (rfl : (formMinus N hN u : QuotientL2 N) = frickeMinus N hN u)

/-- Exact physical closed-form mass and Dirichlet-energy channel split. -/
theorem actual_form_mass_energy_split (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : actualEnergyFormDomain N) :
    ‖(u : QuotientL2 N)‖ ^ 2 = ‖(formPlus N hN u : QuotientL2 N)‖ ^ 2 +
      ‖(formMinus N hN u : QuotientL2 N)‖ ^ 2 ∧
    actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u) =
      actualDirichletPair N (actualEnergyLift N (formPlus N hN u)) (actualEnergyLift N (formPlus N hN u)) +
        actualDirichletPair N (actualEnergyLift N (formMinus N hN u)) (actualEnergyLift N (formMinus N hN u)) := by
  refine ⟨fricke_mass_split N hN u, ?_⟩
  rw [actualEnergyLift_formPlus, actualEnergyLift_formMinus]
  exact Dirichlet_parity_split N hN _ _

theorem parityPlus_mem_friedrichsDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ (actualGammaFriedrichs N).domain) :
    frickePlus N hN f ∈ (actualGammaFriedrichs N).domain := by
  change (1 / 2 : ℂ) • (f + frickeL2 N hN f) ∈ (actualGammaFriedrichs N).domain
  exact (actualGammaFriedrichs N).domain.smul_mem _
    ((actualGammaFriedrichs N).domain.add_mem hf (fricke_friedrichsDomain_action N hN hf))

theorem parityMinus_mem_friedrichsDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ (actualGammaFriedrichs N).domain) :
    frickeMinus N hN f ∈ (actualGammaFriedrichs N).domain := by
  change (1 / 2 : ℂ) • (f - frickeL2 N hN f) ∈ (actualGammaFriedrichs N).domain
  exact (actualGammaFriedrichs N).domain.smul_mem _
    ((actualGammaFriedrichs N).domain.sub_mem hf (fricke_friedrichsDomain_action N hN hf))

def friedrichsPlus (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualGammaFriedrichs N).domain) : (actualGammaFriedrichs N).domain :=
  ⟨frickePlus N hN u, parityPlus_mem_friedrichsDomain N hN u.property⟩

def friedrichsMinus (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualGammaFriedrichs N).domain) : (actualGammaFriedrichs N).domain :=
  ⟨frickeMinus N hN u, parityMinus_mem_friedrichsDomain N hN u.property⟩

theorem actualFriedrichs_plus (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N (friedrichsPlus N hN u) = frickePlus N hN (actualGammaFriedrichs N u) := by
  change actualGammaFriedrichs N ((1 / 2 : ℂ) • (u + friedrichsFrickeDomain N hN u)) =
    (1 / 2 : ℂ) • (actualGammaFriedrichs N u + frickeL2 N hN (actualGammaFriedrichs N u))
  rw [(actualGammaFriedrichs N).map_smul, (actualGammaFriedrichs N).map_add, actualGammaFriedrichs_fricke]

theorem actualFriedrichs_minus (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N (friedrichsMinus N hN u) = frickeMinus N hN (actualGammaFriedrichs N u) := by
  change actualGammaFriedrichs N ((1 / 2 : ℂ) • (u - friedrichsFrickeDomain N hN u)) =
    (1 / 2 : ℂ) • (actualGammaFriedrichs N u - frickeL2 N hN (actualGammaFriedrichs N u))
  rw [(actualGammaFriedrichs N).map_smul, (actualGammaFriedrichs N).map_sub, actualGammaFriedrichs_fricke]

end ImbalancedChen.Part3.GlobalFrickeParityFormDomain20261026b
