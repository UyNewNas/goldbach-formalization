import ImbalancedChen.Part3CommonSmoothCutoff
import ImbalancedChen.Part3ActualSeparatedRowFiniteMatcher
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / PROPOSED MODULE:
  ImbalancedChen.Part3ActualPositiveLatticeSmoothCover
This ONE parent reuses the actual cutoff and actual finite matcher.
Tight1063 L18-L160 and six566 L9-L356 retain their complete namespaces,
sections, declaration types and proof bodies. The sole local edit renames
one unused assumption binder hM to _hM; its positive-scale premise remains.
All five private helpers stay in this same module. No M2 or proposed import
is introduced; no actual matcher, whole log supplier or cutoff is recopied.
No new row-to-J, spectral or target-shaped hypothesis is supplied.
Only ROOT controls subsequent actual installation and compilation.
-/

namespace ImbalancedChen.Part3.CommonSmoothCutoff

noncomputable section

open Set
open scoped SchwartzMap

/-- Exact closed support of the actual radius-one bump. -/
theorem dyadicCutoff_tsupport_eq_tight :
    tsupport dyadicCutoff = Icc (1 / 2 : ℝ) (5 / 2) := by
  change tsupport (dyadicBump : ℝ → ℝ) = _
  rw [dyadicBump.tsupport_eq]
  ext x
  change |x - 3 / 2| ≤ 1 ↔ 1 / 2 ≤ x ∧ x ≤ 5 / 2
  rw [abs_le]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith

/-- Complex.ofReal is injective, so Schwartz realization changes no
support point. This is an identity for the existing actual function. -/
theorem dyadicCutoffSchwartz_tsupport_eq_tight :
    tsupport (dyadicCutoffSchwartz : ℝ → ℂ) = Icc (1 / 2 : ℝ) (5 / 2) := by
  have hs : Function.support (dyadicCutoffSchwartz : ℝ → ℂ) =
      Function.support dyadicCutoff := by
    ext x
    simp only [Function.mem_support, dyadicCutoffSchwartz_apply,
      ne_eq, Complex.ofReal_eq_zero]
  change closure (Function.support (dyadicCutoffSchwartz : ℝ → ℂ)) = _
  rw [hs]
  exact dyadicCutoff_tsupport_eq_tight

theorem dyadicCutoffSchwartz_mem_tight_of_ne_zero {x : ℝ}
    (hx : dyadicCutoffSchwartz x ≠ 0) : x ∈ Icc (1 / 2 : ℝ) (5 / 2) := by
  rw [← dyadicCutoffSchwartz_tsupport_eq_tight]
  exact subset_closure hx

theorem dyadicCutoffSchwartz_hasCompactSupport_tight :
    HasCompactSupport (dyadicCutoffSchwartz : ℝ → ℂ) := by
  change IsCompact (tsupport (dyadicCutoffSchwartz : ℝ → ℂ))
  rw [dyadicCutoffSchwartz_tsupport_eq_tight]
  exact isCompact_Icc

theorem dyadicCutoffSchwartz_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    dyadicCutoffSchwartz x = 0 := by
  by_contra hn
  have hlo := (dyadicCutoffSchwartz_mem_tight_of_ne_zero hn).1
  linarith

@[simp] theorem dyadicCutoffSchwartz_zero : dyadicCutoffSchwartz 0 = 0 := by
  exact dyadicCutoffSchwartz_eq_zero_of_nonpos le_rfl

/-- Same actual owned scaled Schwartz function, written in the literal
physical-kernel psi(c/C) notation. -/
theorem scaledDyadicCutoffSchwartz_eq_literal
    (C : ℝ) (hC : 0 < C) (c : ℝ) :
    scaledDyadicCutoffSchwartz C hC c = dyadicCutoffSchwartz (c / C) := by
  simp only [scaledDyadicCutoffSchwartz_apply, scaledDyadicCutoff,
    dyadicCutoffSchwartz_apply]

/-- The tight support bounds used by a physical outer c-sum. -/
theorem physical_cutoff_nonzero_bounds {C c : ℝ} (hC : 0 < C)
    (hc : dyadicCutoffSchwartz (c / C) ≠ 0) :
    C / 2 ≤ c ∧ c ≤ 5 * C / 2 := by
  obtain ⟨hlo, hhi⟩ := dyadicCutoffSchwartz_mem_tight_of_ne_zero hc
  have hl := (le_div_iff₀ hC).mp hlo
  have hu := (div_le_iff₀ hC).mp hhi
  constructor <;> linarith

theorem physical_cutoff_tsupport_subset {C : ℝ} (hC : 0 < C) :
    tsupport (fun c : ℝ => dyadicCutoffSchwartz (c / C)) ⊆
      Icc (C / 2) (5 * C / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro c hc
  exact physical_cutoff_nonzero_bounds hC hc

theorem physical_cutoff_hasCompactSupport {C : ℝ} (hC : 0 < C) :
    HasCompactSupport (fun c : ℝ => dyadicCutoffSchwartz (c / C)) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (physical_cutoff_tsupport_subset hC)

/-- Zero numerator is a genuine zero of the physical cutoff, for EVERY
real scale, including zero and negative scales. -/
@[simp] theorem physical_cutoff_zero_modulus (C : ℝ) :
    dyadicCutoffSchwartz ((0 : ℝ) / C) = 0 := by
  simp only [zero_div, dyadicCutoffSchwartz_zero]

/-- Lean's real division at zero makes the literal factor zero for any c.
This is a cutoff fact, not permission to apply a positive-modulus Poisson theorem. -/
@[simp] theorem physical_cutoff_zero_scale (c : ℝ) :
    dyadicCutoffSchwartz (c / (0 : ℝ)) = 0 := by
  simp only [div_zero, dyadicCutoffSchwartz_zero]

/-- The nonpositive-scale vanishing branch needs c>=0. -/
theorem physical_cutoff_nonpos_scale {C c : ℝ} (hC : C ≤ 0) (hc : 0 ≤ c) :
    dyadicCutoffSchwartz (c / C) = 0 := by
  apply dyadicCutoffSchwartz_eq_zero_of_nonpos
  exact div_nonpos_of_nonneg_of_nonpos hc hC

theorem physical_cutoff_nonpos_scale_nat {C : ℝ} (hC : C ≤ 0) (c : ℕ) :
    dyadicCutoffSchwartz ((c : ℝ) / C) = 0 := by
  exact physical_cutoff_nonpos_scale hC (Nat.cast_nonneg c)

/-- For a nonnegative physical modulus, nonvanishing supplies BOTH scale
and modulus positivity, as well as the tight bounds. -/
theorem physical_cutoff_nonzero_nonneg_modulus {C c : ℝ} (hc : 0 ≤ c)
    (hn : dyadicCutoffSchwartz (c / C) ≠ 0) :
    0 < C ∧ 0 < c ∧ C / 2 ≤ c ∧ c ≤ 5 * C / 2 := by
  have hC : 0 < C := by
    by_contra h
    exact hn (physical_cutoff_nonpos_scale (le_of_not_gt h) hc)
  obtain ⟨hlo, hhi⟩ := physical_cutoff_nonzero_bounds hC hn
  exact ⟨hC, by linarith, hlo, hhi⟩

/-- Literal natural outer modulus: no c>0 premise is silently assumed. -/
theorem physical_cutoff_nonzero_nat_modulus {C : ℝ} {c : ℕ}
    (hn : dyadicCutoffSchwartz ((c : ℝ) / C) ≠ 0) :
    0 < C ∧ 0 < c ∧ C / 2 ≤ (c : ℝ) ∧ (c : ℝ) ≤ 5 * C / 2 := by
  obtain ⟨hC, hc, hlo, hhi⟩ :=
    physical_cutoff_nonzero_nonneg_modulus (Nat.cast_nonneg c) hn
  exact ⟨hC, by exact_mod_cast hc, hlo, hhi⟩

/-- For unrestricted real c and a negative scale the support reverses,
so this branch must not be replaced by an unconditional zero claim. -/
theorem physical_cutoff_negative_scale_bounds {C c : ℝ} (hC : C < 0)
    (hn : dyadicCutoffSchwartz (c / C) ≠ 0) :
    5 * C / 2 ≤ c ∧ c ≤ C / 2 := by
  obtain ⟨hlo, hhi⟩ := dyadicCutoffSchwartz_mem_tight_of_ne_zero hn
  have hl := mul_le_mul_of_nonpos_right hlo hC.le
  have hu := mul_le_mul_of_nonpos_right hhi hC.le
  rw [div_mul_cancel₀ _ hC.ne] at hl hu
  constructor <;> linarith

/-- A concrete actual plateau value shows why C<0 alone is insufficient
for vanishing when c may also be negative. -/
theorem physical_cutoff_negative_scale_plateau {C : ℝ} (hC : C < 0) :
    dyadicCutoffSchwartz (((3 / 2 : ℝ) * C) / C) = 1 := by
  have hr : ((3 / 2 : ℝ) * C) / C = 3 / 2 := by
    field_simp [hC.ne]
  rw [hr, dyadicCutoffSchwartz_apply,
    dyadicCutoff_eq_one (by norm_num : (3 / 2 : ℝ) ∈ Icc (1 : ℝ) 2)]
  exact Complex.ofReal_one

end

end ImbalancedChen.Part3.CommonSmoothCutoff

namespace ImbalancedChen.Part3.ActualPositiveLatticeSmoothCoverSourceOnly

noncomputable section
open Classical Finset CommonSmoothCutoff GeneralDGateNormalization
open GeneralDActiveOuterEnergySourceOnly GeneralDActivePairCountSourceOnly
open ActualFixedFeaturePacketPushforwardSourceOnly
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

/-- Fixed two-window cover of [B,4B]. -/
def bCover (B x : ℝ) : ℝ := scaledDyadicCutoff B x + scaledDyadicCutoff (2*B) x

/-- Fixed three-window cover of [C,8C]. -/
def cCover (C x : ℝ) : ℝ :=
  scaledDyadicCutoff C x + scaledDyadicCutoff (2*C) x + scaledDyadicCutoff (4*C) x

theorem bCover_nonneg (B x : ℝ) : 0 ≤ bCover B x :=
  add_nonneg (scaledDyadicCutoff_nonneg _ _) (scaledDyadicCutoff_nonneg _ _)

theorem cCover_nonneg (C x : ℝ) : 0 ≤ cCover C x :=
  add_nonneg (add_nonneg (scaledDyadicCutoff_nonneg _ _) (scaledDyadicCutoff_nonneg _ _))
    (scaledDyadicCutoff_nonneg _ _)

theorem bCover_le_two (B x : ℝ) : bCover B x ≤ 2 := by
  have h0 := scaledDyadicCutoff_le_one B x
  have h1 := scaledDyadicCutoff_le_one (2*B) x
  dsimp [bCover]
  linarith

theorem cCover_le_three (C x : ℝ) : cCover C x ≤ 3 := by
  have h0 := scaledDyadicCutoff_le_one C x
  have h1 := scaledDyadicCutoff_le_one (2*C) x
  have h2 := scaledDyadicCutoff_le_one (4*C) x
  dsimp [cCover]
  linarith

theorem bCover_contDiff (B : ℝ) : ContDiff ℝ ∞ (bCover B) :=
  (scaledDyadicCutoff_contDiff B).add (scaledDyadicCutoff_contDiff (2*B))

theorem cCover_contDiff (C : ℝ) : ContDiff ℝ ∞ (cCover C) :=
  ((scaledDyadicCutoff_contDiff C).add (scaledDyadicCutoff_contDiff (2*C))).add
    (scaledDyadicCutoff_contDiff (4*C))

theorem bCover_hasCompactSupport {B : ℝ} (hB : 0 < B) : HasCompactSupport (bCover B) :=
  (scaledDyadicCutoff_hasCompactSupport hB).add
    (scaledDyadicCutoff_hasCompactSupport (by positivity : 0 < 2*B))

theorem cCover_hasCompactSupport {C : ℝ} (hC : 0 < C) : HasCompactSupport (cCover C) :=
  ((scaledDyadicCutoff_hasCompactSupport hC).add
    (scaledDyadicCutoff_hasCompactSupport (by positivity : 0 < 2*C))).add
      (scaledDyadicCutoff_hasCompactSupport (by positivity : 0 < 4*C))

theorem bCover_ge_one {B x : ℝ} (hB : 0 < B) (hx : B ≤ x ∧ x ≤ 4*B) :
    1 ≤ bCover B x := by
  by_cases hmid : x ≤ 2*B
  · have h0 := scaledDyadicCutoff_eq_one hB ⟨hx.1, hmid⟩
    have h1 := scaledDyadicCutoff_nonneg (2*B) x
    dsimp [bCover]
    rw [h0]
    linarith
  · have h1 := scaledDyadicCutoff_eq_one (by positivity : 0 < 2*B)
      ⟨(lt_of_not_ge hmid).le, by linarith [hx.2]⟩
    have h0 := scaledDyadicCutoff_nonneg B x
    dsimp [bCover]
    rw [h1]
    linarith

theorem cCover_ge_one {C x : ℝ} (hC : 0 < C) (hx : C ≤ x ∧ x ≤ 8*C) :
    1 ≤ cCover C x := by
  by_cases hmid : x ≤ 2*C
  · have h0 := scaledDyadicCutoff_eq_one hC ⟨hx.1, hmid⟩
    have h1 := scaledDyadicCutoff_nonneg (2*C) x
    have h2 := scaledDyadicCutoff_nonneg (4*C) x
    dsimp [cCover]
    rw [h0]
    linarith
  · by_cases hmid' : x ≤ 4*C
    · have h1 := scaledDyadicCutoff_eq_one (by positivity : 0 < 2*C)
        ⟨(lt_of_not_ge hmid).le, by linarith [hmid']⟩
      have h0 := scaledDyadicCutoff_nonneg C x
      have h2 := scaledDyadicCutoff_nonneg (4*C) x
      dsimp [cCover]
      rw [h1]
      linarith
    · have h2 := scaledDyadicCutoff_eq_one (by positivity : 0 < 4*C)
        ⟨(lt_of_not_ge hmid').le, by linarith [hx.2]⟩
      have h0 := scaledDyadicCutoff_nonneg C x
      have h1 := scaledDyadicCutoff_nonneg (2*C) x
      dsimp [cCover]
      rw [h2]
      linarith

/-- This complete carrier contains the full support of ALL six pieces.
The original bc-unit gate and signed nonzero f window are retained. -/
def packetBox (B C F : ℝ) : Finset Packet :=
  ((Ioc 0 (Nat.floor (5*B)) ×ˢ Ioc 0 (Nat.floor (10*C))) ×ˢ
    Icc (Int.ceil (-F)) (Int.floor F)).filter (fun k => k.1.1.Coprime k.1.2 ∧ k.2 ≠ 0)

def packetWeight (B C : ℝ) (k : Packet) : ℝ := bCover B k.1.1 * cCover C k.1.2

theorem packetWeight_nonneg (B C : ℝ) (k : Packet) : 0 ≤ packetWeight B C k :=
  mul_nonneg (bCover_nonneg _ _) (cCover_nonneg _ _)

private theorem scaled_nat_support {M : ℝ} (_hM : 0 < M) {n : ℕ}
    (hn : scaledDyadicCutoff M n ≠ 0) : 0 < n ∧ (n : ℝ) ≤ 5*M/2 := by
  have hpsi : dyadicCutoffSchwartz ((n : ℝ)/M) ≠ 0 := by
    simpa only [dyadicCutoffSchwartz_apply, scaledDyadicCutoff, ne_eq,
      Complex.ofReal_eq_zero] using hn
  obtain ⟨_, hnpos, _, hhi⟩ := physical_cutoff_nonzero_nat_modulus hpsi
  exact ⟨hnpos, hhi⟩

/-- A piece's b,c support is fully inside the common box. Thus its
outer carrier truncation adds no rough endpoint on a nonzero smooth term. -/
theorem piece_nonzero_mem_box {B C F M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hMB : M ≤ 2*B) (hNC : N ≤ 4*C) {k : Packet}
    (hbc : k.1.1.Coprime k.1.2) (hf : k.2 ≠ 0) (hfF : |(k.2 : ℝ)| ≤ F)
    (hw : scaledDyadicCutoff M k.1.1 * scaledDyadicCutoff N k.1.2 ≠ 0) :
    k ∈ packetBox B C F := by
  have hwb : scaledDyadicCutoff M k.1.1 ≠ 0 := by
    intro hz
    exact hw (by rw [hz, zero_mul])
  have hwc : scaledDyadicCutoff N k.1.2 ≠ 0 := by
    intro hz
    exact hw (by rw [hz, mul_zero])
  have hb := scaled_nat_support hM hwb
  have hc := scaled_nat_support hN hwc
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩, hbc, hf⟩
  · exact mem_Ioc.mpr ⟨hb.1, Nat.le_floor (by linarith [hb.2])⟩
  · exact mem_Ioc.mpr ⟨hc.1, Nat.le_floor (by linarith [hc.2])⟩
  · exact mem_Icc.mpr ⟨Int.ceil_le.mpr (abs_le.mp hfF).1,
      Int.le_floor.mpr (abs_le.mp hfF).2⟩

def scaleB (e : MediumAtom) (delta l : ℕ) : ℝ := (l : ℝ)*e.U*e.Q3/delta

def scaleC (e : MediumAtom) (D g l : ℕ) : ℝ := e.U*e.Q3*e.Q2/((g : ℝ)*l*D)

def scaleF (e : MediumAtom) (D g : ℕ) : ℝ := e.U/((g : ℝ)*e.Q1*D)

/-- No delta>0 premise is added: actual membership itself supplies it. -/
private theorem scaleB_pos_of_mem (e : MediumAtom)
    (hN : 1 ≤ e.U) (hR : 1 ≤ e.Q3) (Yb Ys : ℝ) {D delta g l : ℕ}
    (hl : 0 < l) {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) :
    0 < scaleB e delta l := by
  have hd := (mem_filter.mp ho).2.2.1
  have hrmem := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.1
  have hr : 0 < o.2.1.1 := (factorCarrier_bounds hR hrmem).1
  have hdelta : 0 < delta := by rw [← hd]; exact Nat.gcd_pos_of_pos_left D hr
  have hNR : 0 < e.U := zero_lt_one.trans_le hN
  have hRR : 0 < e.Q3 := zero_lt_one.trans_le hR
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  dsimp [scaleB]
  positivity

private theorem scaleC_pos (e : MediumAtom)
    (hN : 1 ≤ e.U) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    {D g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l) : 0 < scaleC e D g l := by
  have hNR : 0 < e.U := zero_lt_one.trans_le hN
  have hRR : 0 < e.Q3 := zero_lt_one.trans_le hR
  have hSR : 0 < e.Q2 := zero_lt_one.trans_le hS
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  dsimp [scaleC]
  positivity

theorem actual_packetImage_subset_box (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l) :
    packetImage e Yb Ys D delta g l ⊆
      packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g) := by
  intro k hk
  obtain ⟨o, ho, rfl⟩ := mem_image.mp hk
  have d := fixedSlice_packetData e hN hQ hR hS Yb Ys hD hg hl ho
  have hw := packetB_C_scales e hN hQ hR hS Yb Ys hD hg hl ho
  have hf := packetF_scale e hN hQ hR hS Yb Ys hD hg hl ho
  have hB := scaleB_pos_of_mem e hN hR Yb Ys hl ho
  have hC := scaleC_pos e hN hR hS hD hg hl
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩, d.bc_coprime, d.f_ne⟩
  · exact mem_Ioc.mpr ⟨d.b_pos, Nat.le_floor (by change (packetB delta g l o : ℝ) ≤ 5*scaleB e delta l; dsimp [scaleB] at *; linarith [hw.2.1])⟩
  · exact mem_Ioc.mpr ⟨d.c_pos, Nat.le_floor (by change (packetC D g o : ℝ) ≤ 10*scaleC e D g l; dsimp [scaleC] at *; linarith [hw.2.2.2])⟩
  · exact mem_Icc.mpr ⟨Int.ceil_le.mpr (abs_le.mp hf.2.1).1,
      Int.le_floor.mpr (abs_le.mp hf.2.1).2⟩

theorem actual_packetWeight_ge_one (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {k : Packet} (hk : k ∈ packetImage e Yb Ys D delta g l) :
    1 ≤ packetWeight (scaleB e delta l) (scaleC e D g l) k := by
  obtain ⟨o, ho, rfl⟩ := mem_image.mp hk
  have hw := packetB_C_scales e hN hQ hR hS Yb Ys hD hg hl ho
  have hb := bCover_ge_one (scaleB_pos_of_mem e hN hR Yb Ys hl ho) ⟨hw.1, hw.2.1⟩
  have hc := cCover_ge_one (scaleC_pos e hN hR hS hD hg hl) ⟨hw.2.2.1, hw.2.2.2⟩
  change 1 ≤ bCover (scaleB e delta l) (packetB delta g l o : ℝ) *
    cCover (scaleC e D g l) (packetC D g o : ℝ)
  simpa only [one_mul] using mul_le_mul hb hc zero_le_one (zero_le_one.trans hb)

/-- General positive finite extension; no restriction inside J is discarded. -/
private theorem positive_lattice_domination (T L : Finset Packet) (w m : Packet → ℝ)
    (J : Packet → ℂ) (hTL : T ⊆ L) (hw : ∀ k, 0 ≤ w k) (hm : ∀ k, 0 ≤ m k)
    (hone : ∀ k ∈ T, 1 ≤ w k) :
    (∑ k ∈ T, m k * ‖J k‖^2) ≤ ∑ k ∈ L, w k * (m k * ‖J k‖^2) := by
  calc
    _ ≤ ∑ k ∈ T, w k * (m k * ‖J k‖^2) := by
      apply sum_le_sum
      intro k hk
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hone k hk)
        (mul_nonneg (hm k) (sq_nonneg _))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hTL (fun k hk hn =>
      mul_nonneg (hw k) (mul_nonneg (hm k) (sq_nonneg _)))

/-- The actual fibre multiplicity is retained, not silently replaced by1. -/
theorem actual_positive_mass_smooth_mu (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (J : Packet → ℂ) :
    (∑ o ∈ fixedSlice e Yb Ys D delta g l, ‖J (packetKey D delta g l o)‖^2) ≤
      ∑ k ∈ packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g),
        packetWeight (scaleB e delta l) (scaleC e D g l) k *
          (((packetFiber e Yb Ys D delta g l k).card : ℝ) * ‖J k‖^2) := by
  rw [positive_mass_eq_packet_mass]
  exact positive_lattice_domination _ _ _ _ J
    (actual_packetImage_subset_box e hN hQ hR hS Yb Ys hD hg hl)
    (packetWeight_nonneg _ _) (fun k => Nat.cast_nonneg _)
    (fun k hk => actual_packetWeight_ge_one e hN hQ hR hS Yb Ys hD hg hl hk)

/-- Literal proven representation payment, defined also off the packet image. -/
def packetTau (A D : ℕ) (k : Packet) : ℕ :=
  (k.1.1/A).divisors.card * D.divisors.card * k.1.2.divisors.card^2

def tauEnvelope (A D : ℕ) (L : Finset Packet) : ℕ := L.sup (packetTau A D)

def smoothMass (M N : ℝ) (L : Finset Packet) (J : Packet → ℂ) : ℝ :=
  ∑ k ∈ L, scaledDyadicCutoff M k.1.1 * scaledDyadicCutoff N k.1.2 * ‖J k‖^2

def sixSmoothMass (B C : ℝ) (L : Finset Packet) (J : Packet → ℂ) : ℝ :=
  smoothMass B C L J + smoothMass B (2*C) L J + smoothMass B (4*C) L J +
    smoothMass (2*B) C L J + smoothMass (2*B) (2*C) L J + smoothMass (2*B) (4*C) L J

/-- Six exact terms, with NO additional Cauchy factor six. -/
theorem cover_mass_eq_six (B C : ℝ) (L : Finset Packet) (J : Packet → ℂ) :
    (∑ k ∈ L, packetWeight B C k * ‖J k‖^2) = sixSmoothMass B C L J := by
  simp only [packetWeight, bCover, cCover, add_mul, mul_add, sum_add_distrib,
    sixSmoothMass, smoothMass]
  ring

/-- Written as ordinary integer b,c,f sums with the SAME unit/nonzero masks. -/
theorem smoothMass_lattice (M N B C F : ℝ) (J : Packet → ℂ) :
    smoothMass M N (packetBox B C F) J =
      ∑ b ∈ Ioc 0 (Nat.floor (5*B)), ∑ c ∈ Ioc 0 (Nat.floor (10*C)),
        ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
          if b.Coprime c ∧ f ≠ 0 then
            scaledDyadicCutoff M b * scaledDyadicCutoff N c * ‖J ((b,c),f)‖^2 else 0 := by
  simp only [smoothMass, packetBox, sum_filter, sum_product]

/-- Fixed divisor cost before smoothing: an ACTUAL finite maximum, not x^epsilon. -/
private theorem tau_mass_domination (T L : Finset Packet) (A D : ℕ) (B C : ℝ)
    (J : Packet → ℂ) (hTL : T ⊆ L)
    (hone : ∀ k ∈ T, 1 ≤ packetWeight B C k) :
    (∑ k ∈ T, (packetTau A D k : ℝ)*‖J k‖^2) ≤
      (tauEnvelope A D L : ℝ) * sixSmoothMass B C L J := by
  have hsm := positive_lattice_domination T L (packetWeight B C)
    (fun k => (packetTau A D k : ℝ)) J hTL (packetWeight_nonneg B C)
      (fun k => Nat.cast_nonneg _) hone
  calc
    _ ≤ ∑ k ∈ L, packetWeight B C k * ((packetTau A D k : ℝ)*‖J k‖^2) := hsm
    _ ≤ ∑ k ∈ L, (tauEnvelope A D L : ℝ)*(packetWeight B C k*‖J k‖^2) := by
      apply sum_le_sum
      intro k hk
      have ht : (packetTau A D k : ℝ) ≤ (tauEnvelope A D L : ℝ) := by
        exact_mod_cast (show packetTau A D k ≤ tauEnvelope A D L from le_sup hk)
      have hh := mul_le_mul_of_nonneg_right ht
        (mul_nonneg (packetWeight_nonneg B C k) (sq_nonneg ‖J k‖))
      nlinarith only [hh]
    _ = (tauEnvelope A D L : ℝ) * (∑ k ∈ L, packetWeight B C k*‖J k‖^2) := by rw [mul_sum]
    _ = _ := by rw [cover_mass_eq_six]

/-- Actual finite packet Cauchy -> six smooth positive lattice squares.
All scales, the finite divisor maximum and original Co energy are constructed.
Arbitrary J is a fixed function on packet labels; no actual row=J is assumed.
Its interior masks and original signed H window are untouched by this theorem. -/
theorem actual_packet_Cauchy_six_smooth (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (J : Packet → ℂ) :
    let B := scaleB e delta l
    let C := scaleC e D g l
    let F := scaleF e D g
    let L := packetBox B C F
    ‖∑ o ∈ fixedSlice e Yb Ys D delta g l,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * J (packetKey D delta g l o)‖^2 ≤
      fixedFirstEnergy e Yb Ys D delta g l * (tauEnvelope (g*l) D L : ℝ) *
        sixSmoothMass B C L J := by
  dsimp only
  have hE : 0 ≤ fixedFirstEnergy e Yb Ys D delta g l :=
    sum_nonneg (fun o ho => sq_nonneg _)
  have ht := tau_mass_domination (packetImage e Yb Ys D delta g l)
    (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g))
    (g*l) D (scaleB e delta l) (scaleC e D g l) J
    (actual_packetImage_subset_box e hN hQ hR hS Yb Ys hD hg hl)
    (fun k hk => actual_packetWeight_ge_one e hN hQ hR hS Yb Ys hD hg hl hk)
  have hc := scalar_packet_Cauchy_tau e hN hQ hR hS Yb Ys (delta := delta) hD hg hl J
  change _ ≤ fixedFirstEnergy e Yb Ys D delta g l *
    (∑ k ∈ packetImage e Yb Ys D delta g l, (packetTau (g*l) D k : ℝ)*‖J k‖^2) at hc
  exact hc.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht hE)

/-- A literal reciprocal packet row for the next consumer. All coefficients
are fixed before b,c,f; both t-unit gates and the COMPLETE signed H window
remain inside the square. No assertion identifies an actual row with this J. -/
def reciprocalPacketRow (A : ℕ) (a : ℤ) (S : ℝ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (k : Packet) : ℂ :=
  ∑ t ∈ factorCarrier S,
    if t.Coprime (A*k.1.2) ∧ t.Coprime (a.natAbs*k.1.2) then
      lambda t * ∑ h ∈ poissonNonzeroFrequencyWindow H,
        omega h * fourier (a*h*k.2)
          (((CanonicalReciprocalPhase.wPhaseInverse (k.1.1*t) k.1.2 : ℝ) /
            (k.1.2 : ℝ) : ℝ) : UnitAddCircle)
    else 0

theorem reciprocal_inverse_licensed (A : ℕ) (a : ℤ) (k : Packet) (t : ℕ)
    (hbc : k.1.1.Coprime k.1.2)
    (ht : t.Coprime (A*k.1.2) ∧ t.Coprime (a.natAbs*k.1.2)) :
    Int.ModEq k.1.2 (((k.1.1*t : ℕ) : ℤ) *
      CanonicalReciprocalPhase.wPhaseInverse (k.1.1*t) k.1.2) 1 := by
  have htc : t.Coprime k.1.2 := ht.1.of_dvd_right (dvd_mul_left _ _)
  exact CanonicalReciprocalPhase.wPhaseInverse_spec (hbc.mul_left htc)

/-- Minimal P8-facing specialization with the actual fixed-slice H and
Sinner scales. lambda/omega are arbitrary FIXED functions, not b,c weights.
There is no hypothesized hclean, row-to-J equality, PSD or spectral bound. -/
theorem actual_reciprocal_packet_Cauchy_six_smooth (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys Z : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    let J := reciprocalPacketRow (g*l) e.residue (e.Q2*(delta : ℝ)/D)
      (e.sharedSmoothFrequencyBound Z D) lambda omega
    let B := scaleB e delta l
    let C := scaleC e D g l
    let L := packetBox B C (scaleF e D g)
    ‖∑ o ∈ fixedSlice e Yb Ys D delta g l,
      e.smallCoreSquaredOuterCoefficient Yb Ys o * J (packetKey D delta g l o)‖^2 ≤
      fixedFirstEnergy e Yb Ys D delta g l * (tauEnvelope (g*l) D L : ℝ) *
        sixSmoothMass B C L J := by
  dsimp only
  exact actual_packet_Cauchy_six_smooth e hN hQ hR hS Yb Ys hD hg hl _

end
end ImbalancedChen.Part3.ActualPositiveLatticeSmoothCoverSourceOnly
