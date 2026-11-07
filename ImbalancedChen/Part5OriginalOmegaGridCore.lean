import ImbalancedChen.Part5SavedParent394700Buchstab

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/- SOURCEONLY module-split candidate. No Lean run or kernel receipt.
   Exact original data/proof segments; see modular recipe for provenance. -/

open Set
open scoped unitInterval

namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly

def genericBarrier (num : ℤ) (i : ℕ) : List ℤ :=
  addList [num*(i:ℤ)-2*err i,num] (scaleList (-2) (row i))

structure OmegaSubcell where
  cell : ℕ
  A : ℤ
  B : ℤ
  D : ℤ
  M : ℤ
  coefficients : List ℤ
  deriving DecidableEq, Repr

def OmegaSubcell.lower (c : OmegaSubcell) : ℚ :=
  ((c.cell:ℚ)*c.D+c.A)/(2*c.D)
def OmegaSubcell.upper (c : OmegaSubcell) : ℚ :=
  ((c.cell:ℚ)*c.D+c.A+c.B)/(2*c.D)

def OmegaSubcell.Valid (c : OmegaSubcell) (num : ℤ) : Prop :=
  2≤c.cell ∧ c.cell≤11 ∧ 0<c.M ∧ 0<c.D ∧ 0<c.B ∧
    0≤c.A ∧ c.A+c.B≤c.D ∧ positiveList c.coefficients=true ∧
    absSum (addList
      (scaleList c.M (homogeneousAffine c.A c.B c.D (genericBarrier num c.cell)))
      (scaleList (-1) (bernsteinSumFrom 52 0 c.coefficients)))=0

instance (c : OmegaSubcell) (num : ℤ) : Decidable (c.Valid num) := by
  unfold OmegaSubcell.Valid
  infer_instance
def OmegaSubcell.check (c : OmegaSubcell) (num : ℤ) : Bool := decide (c.Valid num)

def omegaChainCheck (num : ℤ) : List OmegaSubcell → Bool
  | [] => false
  | c::cs => c.check num && match cs with
    | [] => true
    | d::ds => decide (c.upper=d.lower) && omegaChainCheck num (d::ds)

def omegaChainLower : List OmegaSubcell → ℚ
  | [] => 0
  | c::_ => c.lower
def omegaChainUpper : List OmegaSubcell → ℚ
  | [] => 0
  | [c] => c.upper
  | _::d::ds => omegaChainUpper (d::ds)

structure OmegaCoverCertificate where
  numerator : ℤ
  cells : List OmegaSubcell
  deriving DecidableEq, Repr

def OmegaCoverCertificate.check (c : OmegaCoverCertificate) (lo hi : ℚ) : Bool :=
  ((omegaChainCheck c.numerator c.cells &&
    decide (omegaChainLower c.cells≤lo)) && decide (hi≤omegaChainUpper c.cells)) &&
      decide (0≤c.numerator)

noncomputable section

private theorem eval_genericBarrier (num : ℤ) (i : ℕ) (t : ℝ) :
    evalList (genericBarrier num i) t =
      (num:ℝ)*((i:ℝ)+t)-2*(err i:ℝ)-2*evalList (row i) t := by
  simp only [genericBarrier,eval_addList,eval_scaleList,evalList,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_zero,Int.cast_neg,
    Int.cast_ofNat,mul_zero,add_zero]
  ring

theorem OmegaSubcell.check_sound (c : OmegaSubcell) (num : ℤ)
    (hc : c.check num=true) {s : ℝ}
    (hs : s ∈ Set.Icc (c.lower:ℝ) (c.upper:ℝ)) :
    LiLiuPrereqBuchstab.buchstab s≤(num:ℝ)/scale := by
  have hv : c.Valid num := of_decide_eq_true hc
  rcases hv with ⟨hi2,hi11,hM,hD,hB,hA,hAB,hpos,hzero⟩
  have hDR : (0:ℝ)<(c.D:ℝ) := by exact_mod_cast hD
  have hAR : (0:ℝ)≤(c.A:ℝ) := by exact_mod_cast hA
  have hABR : (c.A:ℝ)+(c.B:ℝ)≤(c.D:ℝ) := by exact_mod_cast hAB
  have hden : (0:ℝ)<2*(c.D:ℝ) := mul_pos (by norm_num) hDR
  have hsl : ((c.cell:ℝ)*(c.D:ℝ)+(c.A:ℝ))/(2*(c.D:ℝ))≤s := by
    simpa [OmegaSubcell.lower] using hs.1
  have hsr : s≤((c.cell:ℝ)*(c.D:ℝ)+(c.A:ℝ)+(c.B:ℝ))/(2*(c.D:ℝ)) := by
    simpa [OmegaSubcell.upper] using hs.2
  have hsl' := (div_le_iff₀ hden).mp hsl
  have hsr' := (le_div_iff₀ hden).mp hsr
  let t : ℝ := 2*(s-left c.cell)
  have htl : (c.A:ℝ)≤(c.D:ℝ)*t := by dsimp [t,left]; nlinarith only [hsl']
  have htr : (c.D:ℝ)*t≤(c.A:ℝ)+(c.B:ℝ) := by
    dsimp [t,left]; nlinarith only [hsr']
  have ht0 : 0≤t := nonneg_of_mul_nonneg_right (hAR.trans htl) hDR
  have ht1 : t≤1 := by
    apply (mul_le_mul_iff_left₀ hDR).mp
    simpa only [mul_one] using htr.trans hABR
  have hsCell : s∈Set.Icc (left c.cell) (right c.cell) := by
    dsimp [t,left] at ht0 ht1
    dsimp [left,right]
    constructor <;> linarith only [ht0,ht1]
  have htAff : (c.A:ℝ)/c.D≤t ∧ t≤((c.A:ℝ)+c.B)/c.D :=
    ⟨(div_le_iff₀ hDR).2 (by nlinarith only [htl]),
      (le_div_iff₀ hDR).2 (by nlinarith only [htr])⟩
  have hb := integer_Bernstein_certificate_on_interval 52 c.M c.A c.B c.D
    (genericBarrier num c.cell) c.coefficients hM hD hB hpos hzero htAff
  rw [eval_genericBarrier] at hb
  have htSum : (c.cell:ℝ)+t=2*s := by dsimp [t,left]; ring
  rw [htSum] at hb
  have he := (abs_le.mp (all_cells c.cell hi11 hi2 s hsCell)).2
  dsimp only [value] at he
  change scaledSource s-evalList (row c.cell) t≤(err c.cell:ℝ) at he
  have hscaled : scaledSource s≤(num:ℝ)*s := by nlinarith only [hb,he]
  have hiR : (2:ℝ)≤(c.cell:ℝ) := by exact_mod_cast hi2
  have hspos : 0<s := by dsimp [left] at hsCell; linarith [hsCell.1]
  have hQ : (0:ℝ)<(scale:ℝ) := by exact_mod_cast scale_positive
  apply (mul_le_mul_iff_left₀ (mul_pos hQ hspos)).mp
  calc
    (scale:ℝ)*s*LiLiuPrereqBuchstab.buchstab s=scaledSource s := by
      dsimp [scaledSource]; ring
    _≤(num:ℝ)*s := hscaled
    _=((scale:ℝ)*s)*((num:ℝ)/scale) := by field_simp [hQ.ne']; ring

/-- Nonempty adjacent rational intervals cover their complete real range.
Every returned subcell carries its own finite checker receipt. -/
private theorem omegaChain_sound (num : ℤ) (cs : List OmegaSubcell)
    (hc : omegaChainCheck num cs=true) {s : ℝ}
    (hs : s∈Set.Icc (omegaChainLower cs:ℝ) (omegaChainUpper cs:ℝ)) :
    ∃ c∈cs, c.check num=true ∧ s∈Set.Icc (c.lower:ℝ) (c.upper:ℝ) := by
  revert hc hs
  induction cs generalizing s with
  | nil => intro hc hs; simp [omegaChainCheck] at hc
  | cons c cs ih =>
      intro hc hs
      change (c.check num && match cs with
        | [] => true
        | d::ds => decide (c.upper=d.lower) && omegaChainCheck num (d::ds))=true at hc
      have hboth := Bool.and_eq_true.mp hc
      cases cs with
      | nil => exact ⟨c,by simp,hboth.1,by simpa [omegaChainLower,omegaChainUpper] using hs⟩
      | cons d ds =>
          have htail := Bool.and_eq_true.mp hboth.2
          have hadj : c.upper=d.lower := of_decide_eq_true htail.1
          by_cases hcut : s≤(c.upper:ℝ)
          · exact ⟨c,by simp,hboth.1,
              ⟨by simpa [omegaChainLower] using hs.1,hcut⟩⟩
          · have hdl : (d.lower:ℝ)≤s := by
              rw [←hadj]
              exact (lt_of_not_ge hcut).le
            have htailRange : s∈Set.Icc (omegaChainLower (d::ds):ℝ)
                (omegaChainUpper (d::ds):ℝ) := by
              exact ⟨by simpa [omegaChainLower] using hdl,
                by simpa [omegaChainUpper] using hs.2⟩
            obtain ⟨e,hem,hcheck,herange⟩ := ih htail.2 htailRange
            exact ⟨e,by simp only [List.mem_cons]; exact Or.inr hem,hcheck,herange⟩

/-- Generic actual-omega supplier. The premises are finite certificate checks
and interval membership, not an actual function enclosure. -/
theorem OmegaCoverCertificate.check_sound (c : OmegaCoverCertificate) (lo hi : ℚ)
    (hc : c.check lo hi=true) {s : ℝ} (hs : s∈Set.Icc (lo:ℝ) (hi:ℝ)) :
    LiLiuPrereqBuchstab.buchstab s≤(c.numerator:ℝ)/scale := by
  have h := Bool.and_eq_true.mp hc
  have h' := Bool.and_eq_true.mp h.1
  have h'' := Bool.and_eq_true.mp h'.1
  have hlo : omegaChainLower c.cells≤lo := of_decide_eq_true h''.2
  have hhi : hi≤omegaChainUpper c.cells := of_decide_eq_true h'.2
  have hchain := h''.1
  have hlowR : (omegaChainLower c.cells:ℝ)≤(lo:ℝ) := by exact_mod_cast hlo
  have hhiR : (hi:ℝ)≤(omegaChainUpper c.cells:ℝ) := by exact_mod_cast hhi
  obtain ⟨cell,hmem,hcheck,hrange⟩ := omegaChain_sound c.numerator c.cells hchain
    ⟨hlowR.trans hs.1,hs.2.trans hhiR⟩
  exact cell.check_sound c.numerator hcheck hrange

end
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly

namespace ImbalancedChen.Certificates.OriginalOmegaGrid32SourceOnly
open Set
open SavedParent394700ActualBuchstabSourceOnly

structure OriginalGridRecord where
  hiLeft : ℤ
  hiRight : ℤ
  pointLeft : ℤ
  pointRight : ℤ
  upper : ℤ
  deriving DecidableEq, Repr

def mesh : ℕ := 4096
def gridCeilDiv (a b : ℤ) : ℤ := -((-a)/b)
def originalCap : ℤ := gridCeilDiv (70893*scale) 125000
def interpolationError : ℤ := gridCeilDiv scale (4*(mesh:ℤ)^2)

/-- This is the ORIGINAL interval-envelope schema. The point values alone
are not interpreted as an enclosure between grid nodes. -/
def OriginalGridRecord.Valid (r : OriginalGridRecord) (j : ℕ) : Prop :=
  r.pointLeft=gridCeilDiv (r.hiLeft*(mesh:ℤ)) (j:ℤ) ∧
  r.pointRight=gridCeilDiv (r.hiRight*(mesh:ℤ)) ((j+1:ℕ):ℤ) ∧
  r.upper=min originalCap (max r.pointLeft r.pointRight+interpolationError)

instance (r : OriginalGridRecord) (j : ℕ) : Decidable (r.Valid j) := by
  unfold OriginalGridRecord.Valid
  infer_instance

end ImbalancedChen.Certificates.OriginalOmegaGrid32SourceOnly
