import ImbalancedChen.Part5OriginalH430ClassicalThinRadialTail

/-! Joint original ordinary boundary budget, including the critical radial
wall, every proper wall and the thin radial portion of the larger-product
query. The K0 factor uses the manuscript density and the clamp's own Theta. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalAllBoundaryCredit
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430RootIntervalTheta (clampLevel clampMass intervalMass)
open Part5OriginalH430ClassicalRootThetaPayment (uniform_clamp_witness)
open Part5OriginalH430ClassicalFixedClampMarks (frozen_bounds)
open Part5OriginalH430ClassicalRadialTupleCount (boundaryCount absolute_radial_payment)
open Part5OriginalH430ClassicalRadialSeedCredit (markedBoundary original_boundary_le)
open Part5OriginalH430ClassicalProperWallSeedCredit
open Part5OriginalH430ClassicalThinRadialTail
open scoped Classical Topology BigOperators

def totalAmbient (N : ℕ) (ν h δ c : ℝ) : ℝ :=
  boundaryCount N (1-2*h) (1+2*h)+properCount N ν δ+boundaryCount N 0 c

def totalMarked (N : ℕ) (ν κ h δ c : ℝ) : ℝ :=
  markedBoundary N ν κ h+markedProper N ν κ δ+markedThin N ν κ c

theorem marked_le_ambient {N : ℕ} {ν κ h δ c : ℝ} (hN : 1<N)
    (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) (hh : 0<h) :
    totalMarked N ν κ h δ c≤totalAmbient N ν h δ c :=
  add_le_add (add_le_add (original_boundary_le hN hν hν' hk hh)
    (original_proper_le hN hν hν' hk)) (original_thin_le hN hν hν' hk)

/-- n,tau,kappa are fixed before the target. The widths and eventual target
are common to all twenty words, ranks, slot pairs and sides of every wall. -/
theorem same_clamp_boundary_payment {n : ℕ} {τ κ ε : ℝ} (ht : 0≤τ) (ht' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hk : 0<κ) (hk' : κ≤1/112) (he : 0<ε) :
    ∃ h δ c : ℝ,0<h ∧ h≤1/8 ∧ 0<δ ∧ 0<c ∧ c≤1/8 ∧
      ∀ᶠ N : ℕ in atTop,(N:ℝ)^(1-κ)≤(c/2)*(N:ℝ) ∧
       (8452171/1250000)*(singularSeries N/log (N:ℝ))*totalAmbient N (clampLevel n τ) h δ c≤
         ε*clampMass N n τ ∧
       (8452171/1250000)*(singularSeries N/log (N:ℝ))*totalMarked N (clampLevel n τ) κ h δ c≤
         ε*clampMass N n τ := by
  let I := intervalMass clampStart (1/3) (1/2)
  let K0 : ℝ := 8452171/1250000
  let ν := clampLevel n τ
  obtain ⟨hI,hw⟩ := uniform_clamp_witness
  have hi : 0<I := hI
  have hK : 0<K0 := by norm_num [K0]
  let e := ε*(I/2)/K0
  have hE : 0<e := div_pos (mul_pos he (half_pos hi)) hK
  have hthird : 0<e/3 := by positivity
  obtain ⟨h,hh,hh',hr⟩ := absolute_radial_payment hthird
  obtain ⟨δ,hδ,hproper⟩ := absolute_proper_payment ν hthird
  obtain ⟨c,hc,hc',htail⟩ := absolute_thin_payment hthird
  have hgeom := frozen_bounds ht ht' hn
  refine ⟨h,δ,c,hh,hh',hδ,hc,hc',?_⟩
  filter_upwards [hr,hproper,htail,hw,lower_wall_in_tail hk (half_pos hc),eventually_ge_atTop (2:ℕ)]
    with N hrad hwall hthin hmass hlower hN
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have h0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  let B := totalAmbient N ν h δ c
  have hraw : (log (N:ℝ)/(N:ℝ))*B≤e := by
    change (log (N:ℝ)/(N:ℝ))*boundaryCount N (1-2*h) (1+2*h)≤e/3 at hrad
    dsimp only [B,totalAmbient]
    rw [mul_add,mul_add]
    linarith only [hrad,hwall,hthin]
  have hB : B≤e*((N:ℝ)/log (N:ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hraw (div_nonneg h0.le hlog.le)
    convert h using 1 <;> field_simp [hlog.ne',h0.ne'] <;> ring
  have hsign := mul_nonneg hK.le (densityScale_pos hN).le
  have hprice : K0*(singularSeries N/log (N:ℝ))*(e*((N:ℝ)/log (N:ℝ)))=
      ε*((I/2)*singularNormalization N) := by
    rw [←sourceMassScale_mul_densityScale]
    dsimp only [e]
    field_simp [hK.ne',hlog.ne'] <;> ring
  have hactual := mul_le_mul_of_nonneg_left hB hsign
  rw [hprice] at hactual
  have hfinal := hactual.trans (mul_le_mul_of_nonneg_left (hmass n τ ht ht' hn) he.le)
  refine ⟨hlower,hfinal,?_⟩
  exact (mul_le_mul_of_nonneg_left (marked_le_ambient (by omega) hgeom.1 hgeom.2 hk' hh) hsign).trans hfinal

end
end ImbalancedChen.Part5OriginalH430ClassicalAllBoundaryCredit

