import ImbalancedChen.P2SeedOmegaRationalRangeEnclosure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The TRUE sampled original kappa on inherited rational alpha boxes is
enclosed by internally generated rational floor queries and causal
Buchstab node data. Original argument s0*(alpha-u-v), K*s0/4 and both
prime denominators are exact. No omega/cost/gain/pass premise is used.
-/

namespace ImbalancedChen.P2SeedOmegaSampledKappaEnclosure
noncomputable section
open Set
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadCellSemantics (actualBadKernel)
open P2SeedOmegaFiniteMesh
open P2SeedOmegaFiniteMeshLimit
open P2SeedOmegaRationalRangeEnclosure
open Certificates.P2BuchstabRationalSemantics

theorem rational_node_bounds (n : ℕ) (i : Fin (n+1)) :
    (19/58:ℚ)≤rationalNode n i ∧ rationalNode n i≤(10/29:ℚ) := by
  have h := node_bounds n i
  rw [←rationalNode_cast] at h
  have hR : (19/58:ℝ)≤(rationalNode n i:ℝ) ∧ (rationalNode n i:ℝ)≤(10/29:ℝ) := by
    simpa only [corner,a2] using h
  exact_mod_cast hR

def queryLo (A : ℚ) (n : ℕ) (i j : Fin (n+1)) : ℚ :=
  (227/50)*(A-rationalNode n i-rationalNode n j)
def queryHi (B : ℚ) (n : ℕ) (i j : Fin (n+1)) : ℚ := queryLo B n i j
def boxTop (B : ℚ) : ℚ := (227/50)*(B-2*(19/58))
def kappaCoefficient (n : ℕ) (i j : Fin (n+1)) : ℚ :=
  ((681/100)*(227/50)/4)/(rationalNode n i*rationalNode n j)
def lowerKappa (m : ℕ) (cs : List NodeEnclosure) (A B : ℚ)
    (n : ℕ) (i j : Fin (n+1)) : ℚ :=
  kappaCoefficient n i j*lowerOmega m cs (queryLo A n i j) (queryHi B n i j)
def upperKappa (m : ℕ) (cs : List NodeEnclosure) (A B : ℚ)
    (n : ℕ) (i j : Fin (n+1)) : ℚ :=
  kappaCoefficient n i j*upperOmega m cs (queryLo A n i j) (queryHi B n i j)

/-- Original prime endpoint geometry PRODUCES the safe query lower
bound, including at the closed rational node endpoints. -/
theorem original_queries (n : ℕ) (i j : Fin (n+1)) {A B : ℚ}
    (hA : 2≤A) (hAB : A≤B) :
    (4313/725:ℚ)≤queryLo A n i j ∧
      queryLo A n i j≤queryHi B n i j ∧ queryHi B n i j≤boxTop B := by
  have hi := rational_node_bounds n i
  have hj := rational_node_bounds n j
  dsimp [queryLo,queryHi,boxTop]
  constructor
  · linarith only [hA,hi.2,hj.2]
  constructor
  · linarith only [hAB]
  · linarith only [hi.1,hj.1]

theorem original_query_membership (n : ℕ) (i j : Fin (n+1)) {A B : ℚ} {alpha : ℝ}
    (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    badArgument alpha (node n i) (node n j) ∈
      Icc (queryLo A n i j:ℝ) (queryHi B n i j:ℝ) := by
  have hLo : (queryLo A n i j:ℝ)=s0*((A:ℝ)-node n i-node n j) := by
    simp only [queryLo,s0,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,rationalNode_cast]
  have hHi : (queryHi B n i j:ℝ)=s0*((B:ℝ)-node n i-node n j) := by
    simp only [queryHi,queryLo,s0,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,rationalNode_cast]
  rw [hLo,hHi]
  dsimp [badArgument,s0]
  constructor <;> linarith only [ha.1,ha.2]

theorem coefficient_positive (n : ℕ) (i j : Fin (n+1)) : 0<kappaCoefficient n i j := by
  have hi : (0:ℚ)<rationalNode n i := lt_of_lt_of_le (by norm_num) (rational_node_bounds n i).1
  have hj : (0:ℚ)<rationalNode n j := lt_of_lt_of_le (by norm_num) (rational_node_bounds n j).1
  exact div_pos (by norm_num) (mul_pos hi hj)

/-- One common rational array-length condition licenses EVERY pair of
sample nodes in the finite mesh; no node-membership assumption survives. -/
theorem actual_sampled_kappa_enclosure {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs=true) {A B : ℚ} (hA : 2≤A) (hAB : A≤B)
    (hcover : queryIndex m (boxTop B)+1<cs.length)
    (n : ℕ) (i j : Fin (n+1)) {alpha : ℝ}
    (ha : alpha ∈ Icc (A:ℝ) (B:ℝ)) :
    (lowerKappa m cs A B n i j:ℝ)≤actualBadKernel alpha (node n i) (node n j) ∧
      actualBadKernel alpha (node n i) (node n j)≤(upperKappa m cs A B n i j:ℝ) := by
  have hq := original_queries n i j hA hAB
  have hq1 : (1:ℚ)≤queryLo A n i j := by linarith only [hq.1]
  have hlength : queryIndex m (queryHi B n i j)+1<cs.length :=
    (Nat.add_le_add_right (queryIndex_mono hq.2.2) 1).trans_lt hcover
  have hω := actual_buchstab_range_enclosure hc hq1 hq.2.1 hlength
    (original_query_membership n i j ha)
  have hcoef : (0:ℝ)≤(kappaCoefficient n i j:ℝ) := by
    exact_mod_cast (coefficient_positive n i j).le
  have he : actualBadKernel alpha (node n i) (node n j)=
      (kappaCoefficient n i j:ℝ)*
        LiLiuPrereqBuchstab.buchstab (badArgument alpha (node n i) (node n j)) := by
    simp only [actualBadKernel,kappaCoefficient,K,s0,Rat.cast_div,Rat.cast_mul,
      Rat.cast_ofNat,rationalNode_cast]
    ring
  rw [he]
  constructor
  · simpa only [lowerKappa,Rat.cast_mul] using mul_le_mul_of_nonneg_left hω.1 hcoef
  · simpa only [upperKappa,Rat.cast_mul] using mul_le_mul_of_nonneg_left hω.2 hcoef

end
end ImbalancedChen.P2SeedOmegaSampledKappaEnclosure
