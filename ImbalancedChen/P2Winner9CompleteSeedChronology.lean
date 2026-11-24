import ImbalancedChen.P2Winner9CompleteSeedData
import ImbalancedChen.P2Winner9LedgerCore
import ImbalancedChen.P2OriginalSeedChronologicalMaxArithmetic
import Mathlib.Tactic

/-!
The exact selected totals of the complete Winner9 row archive. Each block
is reduced separately before the 44 checked triples are summed. This
binds the two complete-seed increments to their original ledger slots.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedChronology

open scoped BigOperators
open P2Winner9CompleteSeedData P2Winner9LedgerCore

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

-- The archive module's local transparency settings do not survive an import.
-- Keep the complete array symbolic: only its named flatten equation is used below.
attribute [local irreducible] allRows blocks

abbrev SourceOwner := RowIndex

def q96 : Nat := 79228162514264337593543950336

def owner (i : RowIndex) : Nat := (entry i).parentId

def adoptedLogTotal : ℚ := ((∑ i : RowIndex, (entry i).logSelected : Nat) : ℚ) / q96

def curvatureSelectedTotal : ℚ :=
  ((∑ i : RowIndex, (entry i).curvatureSelected : Nat) : ℚ) / q96

def mixedSelectedTotal : ℚ :=
  ((∑ i : RowIndex, (entry i).mixedSelected : Nat) : ℚ) / q96

def curvatureGain : ℚ := curvatureSelectedTotal - adoptedLogTotal

def mixedGain : ℚ := mixedSelectedTotal - curvatureSelectedTotal

theorem all_actual_row_maxima (i : RowIndex) :
    (entry i).logSelected ≤ (entry i).curvatureSelected ∧
      (entry i).curvatureSelected ≤ (entry i).mixedSelected ∧
      (entry i).curvatureSelected = max (entry i).logSelected (entry i).curvatureRaw ∧
      (entry i).mixedSelected = max (entry i).curvatureSelected (entry i).mixedRaw := by
  rcases full_source_shapes_and_chronology.2.2 i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcurv, _, hmix⟩
  refine ⟨?_, ?_, hcurv, hmix⟩
  · rw [hcurv]
    exact le_max_left _ _
  · rw [hmix]
    exact le_max_left _ _

theorem owner_is_original_ordinal (i : RowIndex) : owner i = i.val :=
  (full_source_shapes_and_chronology.2.2 i).1

theorem source_owner_injective : Function.Injective owner := by
  intro i j h
  rw [owner_is_original_ordinal, owner_is_original_ordinal] at h
  exact Fin.ext h

section BlockTotals

private theorem block00_totals : selectedTotals P2Winner9CompleteSeedBlock00.rows =
    (23472340669864882376353, 23472378622558934965043, 23478830954858546063791) := by
  decide +kernel

private theorem block01_totals : selectedTotals P2Winner9CompleteSeedBlock01.rows =
    (37961236178173131925700, 37961236178173131925700, 37990838276900117269102) := by
  decide +kernel

private theorem block02_totals : selectedTotals P2Winner9CompleteSeedBlock02.rows =
    (7464490675265779390846, 7464490675265779390846, 7470982452737924538241) := by
  decide +kernel

private theorem block03_totals : selectedTotals P2Winner9CompleteSeedBlock03.rows =
    (41368514191038152263854, 41370010593343221008080, 41428885362563284577988) := by
  decide +kernel

private theorem block04_totals : selectedTotals P2Winner9CompleteSeedBlock04.rows =
    (38928431331336779969723, 38928431331336779969723, 38944092006855312449619) := by
  decide +kernel

private theorem block05_totals : selectedTotals P2Winner9CompleteSeedBlock05.rows =
    (15575963247763785032636, 15575963247763785032636, 15585360753377888569935) := by
  decide +kernel

private theorem block06_totals : selectedTotals P2Winner9CompleteSeedBlock06.rows =
    (13384493279641008893658, 13384493279641008893658, 13384645129545543244949) := by
  decide +kernel

private theorem block07_totals : selectedTotals P2Winner9CompleteSeedBlock07.rows =
    (18327564701173565912480, 18327564701173565912480, 18327704910430255162501) := by
  decide +kernel

private theorem block08_totals : selectedTotals P2Winner9CompleteSeedBlock08.rows =
    (4914453478717189030572, 4914453478717189030572, 4914453478717189030572) := by
  decide +kernel

private theorem block09_totals : selectedTotals P2Winner9CompleteSeedBlock09.rows =
    (3835773434880656628720, 3835773434880656628720, 3835777339016161886161) := by
  decide +kernel

private theorem block10_totals : selectedTotals P2Winner9CompleteSeedBlock10.rows =
    (5642522579940184607582, 5642522579940184607582, 5642522579940184607582) := by
  decide +kernel

private theorem block11_totals : selectedTotals P2Winner9CompleteSeedBlock11.rows =
    (9782585754775405066949, 9782585754775405066949, 9782658953281201131922) := by
  decide +kernel

private theorem block12_totals : selectedTotals P2Winner9CompleteSeedBlock12.rows =
    (1402966813545418479530, 1402966813545418479530, 1402967618714949940721) := by
  decide +kernel

private theorem block13_totals : selectedTotals P2Winner9CompleteSeedBlock13.rows =
    (8138409352254461905029, 8141321459492314957985, 8156615564351479361155) := by
  decide +kernel

private theorem block14_totals : selectedTotals P2Winner9CompleteSeedBlock14.rows =
    (12772258077869498879497, 12779918186479130339146, 12809496025274864536229) := by
  decide +kernel

private theorem block15_totals : selectedTotals P2Winner9CompleteSeedBlock15.rows =
    (31413728799414730627020, 31420324841888295064683, 31486646027900976621860) := by
  decide +kernel

private theorem block16_totals : selectedTotals P2Winner9CompleteSeedBlock16.rows =
    (20326472194721380351640, 20333700172735232120190, 20390953405138873247253) := by
  decide +kernel

private theorem block17_totals : selectedTotals P2Winner9CompleteSeedBlock17.rows =
    (11795586312283643743108, 11798165057004704041628, 11828294552522691944369) := by
  decide +kernel

private theorem block18_totals : selectedTotals P2Winner9CompleteSeedBlock18.rows =
    (5087828367751157360595, 5089603664810822657847, 5102244656657926969949) := by
  decide +kernel

private theorem block19_totals : selectedTotals P2Winner9CompleteSeedBlock19.rows =
    (1042264828363539039953, 1042264828363539039953, 1044972378309485455109) := by
  decide +kernel

private theorem block20_totals : selectedTotals P2Winner9CompleteSeedBlock20.rows =
    (630866307028643431743, 630943680631309749451, 632162763843805097249) := by
  decide +kernel

private theorem block21_totals : selectedTotals P2Winner9CompleteSeedBlock21.rows =
    (16802693089170608975577, 16811537776433176423088, 16861023024910819386066) := by
  decide +kernel

private theorem block22_totals : selectedTotals P2Winner9CompleteSeedBlock22.rows =
    (16721311405142649290479, 16721327593700201897578, 16723194236896703691353) := by
  decide +kernel

private theorem block23_totals : selectedTotals P2Winner9CompleteSeedBlock23.rows =
    (19356295855086162558734, 19356295855086162558734, 19356502580615741208921) := by
  decide +kernel

private theorem block24_totals : selectedTotals P2Winner9CompleteSeedBlock24.rows =
    (24916372258016779453808, 24916372258016779453808, 24920091346232458740778) := by
  decide +kernel

private theorem block25_totals : selectedTotals P2Winner9CompleteSeedBlock25.rows =
    (12750584829427893384858, 12750584829427893384858, 12755534624115811324716) := by
  decide +kernel

private theorem block26_totals : selectedTotals P2Winner9CompleteSeedBlock26.rows =
    (39788041815771875097246, 39788041815771875097246, 39804817071328438012354) := by
  decide +kernel

private theorem block27_totals : selectedTotals P2Winner9CompleteSeedBlock27.rows =
    (9132389158950565418761, 9132389158950565418761, 9141695358454591037819) := by
  decide +kernel

private theorem block28_totals : selectedTotals P2Winner9CompleteSeedBlock28.rows =
    (1598849770454114912995, 1598849770454114912995, 1598849969589472017299) := by
  decide +kernel

private theorem block29_totals : selectedTotals P2Winner9CompleteSeedBlock29.rows =
    (4349281273899781638475, 4358399072503213706329, 4369840629125522761979) := by
  decide +kernel

private theorem block30_totals : selectedTotals P2Winner9CompleteSeedBlock30.rows =
    (3294308572293444296779, 3297816004749484041069, 3305658461885773632830) := by
  decide +kernel

private theorem block31_totals : selectedTotals P2Winner9CompleteSeedBlock31.rows =
    (1396756511280395039476, 1397799226999661686831, 1401126720374824264526) := by
  decide +kernel

private theorem block32_totals : selectedTotals P2Winner9CompleteSeedBlock32.rows =
    (1729992461718335906190, 1734112237198580476678, 1738019115915945071854) := by
  decide +kernel

private theorem block33_totals : selectedTotals P2Winner9CompleteSeedBlock33.rows =
    (3328567398872256735997, 3338400416449609534695, 3349088952440691776549) := by
  decide +kernel

private theorem block34_totals : selectedTotals P2Winner9CompleteSeedBlock34.rows =
    (1068016614131450476498, 1071457988613460003043, 1074949099175937639928) := by
  decide +kernel

private theorem block35_totals : selectedTotals P2Winner9CompleteSeedBlock35.rows =
    (3445864289807612441262, 3450293579341156184424, 3458706869627221047337) := by
  decide +kernel

private theorem block36_totals : selectedTotals P2Winner9CompleteSeedBlock36.rows =
    (1008827585223533365073, 1010434353389839112779, 1012951814413001462954) := by
  decide +kernel

private theorem block37_totals : selectedTotals P2Winner9CompleteSeedBlock37.rows =
    (321558764049672281789, 322383533301502292607, 323318780820197354953) := by
  decide +kernel

private theorem block38_totals : selectedTotals P2Winner9CompleteSeedBlock38.rows =
    (74081549863773725601, 74177116201709527053, 74322069401935292384) := by
  decide +kernel

private theorem block39_totals : selectedTotals P2Winner9CompleteSeedBlock39.rows =
    (135912249020721812884, 135975908124197668233, 136047129283407839014) := by
  decide +kernel

private theorem block40_totals : selectedTotals P2Winner9CompleteSeedBlock40.rows =
    (531008403248710430918, 531097382581233733194, 531296476562599223066) := by
  decide +kernel

private theorem block41_totals : selectedTotals P2Winner9CompleteSeedBlock41.rows =
    (91852215918473974467, 91868623411137004121, 91910354421361355524) := by
  decide +kernel

private theorem block42_totals : selectedTotals P2Winner9CompleteSeedBlock42.rows =
    (71010741291057497808, 71010741291057497808, 71010741291057497808) := by
  decide +kernel

private theorem block43_totals : selectedTotals P2Winner9CompleteSeedBlock43.rows =
    (11779887571055696, 11779887571055696, 11779887571055696) := by
  decide +kernel

-- Each numerical reduction above is confined to one original block.  Once
-- those equalities are available, matching them must not unfold the row data.
attribute [local irreducible] selectedTotals
  P2Winner9CompleteSeedBlock00.rows
  P2Winner9CompleteSeedBlock01.rows
  P2Winner9CompleteSeedBlock02.rows
  P2Winner9CompleteSeedBlock03.rows
  P2Winner9CompleteSeedBlock04.rows
  P2Winner9CompleteSeedBlock05.rows
  P2Winner9CompleteSeedBlock06.rows
  P2Winner9CompleteSeedBlock07.rows
  P2Winner9CompleteSeedBlock08.rows
  P2Winner9CompleteSeedBlock09.rows
  P2Winner9CompleteSeedBlock10.rows
  P2Winner9CompleteSeedBlock11.rows
  P2Winner9CompleteSeedBlock12.rows
  P2Winner9CompleteSeedBlock13.rows
  P2Winner9CompleteSeedBlock14.rows
  P2Winner9CompleteSeedBlock15.rows
  P2Winner9CompleteSeedBlock16.rows
  P2Winner9CompleteSeedBlock17.rows
  P2Winner9CompleteSeedBlock18.rows
  P2Winner9CompleteSeedBlock19.rows
  P2Winner9CompleteSeedBlock20.rows
  P2Winner9CompleteSeedBlock21.rows
  P2Winner9CompleteSeedBlock22.rows
  P2Winner9CompleteSeedBlock23.rows
  P2Winner9CompleteSeedBlock24.rows
  P2Winner9CompleteSeedBlock25.rows
  P2Winner9CompleteSeedBlock26.rows
  P2Winner9CompleteSeedBlock27.rows
  P2Winner9CompleteSeedBlock28.rows
  P2Winner9CompleteSeedBlock29.rows
  P2Winner9CompleteSeedBlock30.rows
  P2Winner9CompleteSeedBlock31.rows
  P2Winner9CompleteSeedBlock32.rows
  P2Winner9CompleteSeedBlock33.rows
  P2Winner9CompleteSeedBlock34.rows
  P2Winner9CompleteSeedBlock35.rows
  P2Winner9CompleteSeedBlock36.rows
  P2Winner9CompleteSeedBlock37.rows
  P2Winner9CompleteSeedBlock38.rows
  P2Winner9CompleteSeedBlock39.rows
  P2Winner9CompleteSeedBlock40.rows
  P2Winner9CompleteSeedBlock41.rows
  P2Winner9CompleteSeedBlock42.rows
  P2Winner9CompleteSeedBlock43.rows

private theorem all_row_totals : selectedTotals allRows =
    (475182339168330434688559, 475259749604404591554030, 475741072397709744401965) := by
  rw [allRows, selectedTotals_flatten]
  simp only [blocks, List.toList_toArray, List.map_cons, List.map_nil,
    block00_totals, block01_totals, block02_totals, block03_totals, block04_totals,
    block05_totals, block06_totals, block07_totals, block08_totals, block09_totals,
    block10_totals, block11_totals, block12_totals, block13_totals, block14_totals,
    block15_totals, block16_totals, block17_totals, block18_totals, block19_totals,
    block20_totals, block21_totals, block22_totals, block23_totals, block24_totals,
    block25_totals, block26_totals, block27_totals, block28_totals, block29_totals,
    block30_totals, block31_totals, block32_totals, block33_totals, block34_totals,
    block35_totals, block36_totals, block37_totals, block38_totals, block39_totals,
    block40_totals, block41_totals, block42_totals, block43_totals]
  rfl

end BlockTotals

/-- The three complete selected stages, read from every original ordinal. -/
theorem selected_numerators_exact :
    (∑ i : RowIndex, (entry i).logSelected,
      ∑ i : RowIndex, (entry i).curvatureSelected,
      ∑ i : RowIndex, (entry i).mixedSelected) =
      (475182339168330434688559, 475259749604404591554030, 475741072397709744401965) := by
  calc
    _ = ∑ i : RowIndex, selectedNumerators (entry i) :=
      (sum_selectedNumerators_components (ι := RowIndex) entry).symm
    _ = ∑ i : RowIndex, selectedNumerators allRows[i.val]! :=
      Finset.sum_congr rfl fun i _ => congrArg selectedNumerators (entry_eq_allRows i)
    _ = selectedTotals allRows :=
      sum_selectedNumerators_eq (n := 11026) (rows := allRows)
        full_source_shapes_and_chronology.1
    _ = _ := all_row_totals

-- Project a symbolic triple before instantiating its coordinates with archive sums.
-- This keeps projection normalization independent of the 11,026-element index type.
private theorem nat_triple_components {a b c x y z : ℕ}
    (h : (a, b, c) = (x, y, z)) : a = x ∧ b = y ∧ c = z := by
  exact ⟨congrArg (fun t : ℕ × ℕ × ℕ => t.1) h,
    congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h,
    congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h⟩

theorem full_literal_totals :
    adoptedLogTotal = P2OriginalSeedChronologicalMaxArithmetic.adoptedLogTotal ∧
      curvatureSelectedTotal = P2OriginalSeedChronologicalMaxArithmetic.curvatureSelectedTotal ∧
      mixedSelectedTotal = P2OriginalSeedChronologicalMaxArithmetic.mixedSelectedTotal := by
  rcases nat_triple_components selected_numerators_exact with ⟨hl, hc, hm⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [adoptedLogTotal, hl]
    norm_num [q96, P2OriginalSeedChronologicalMaxArithmetic.adoptedLogTotal]
  · rw [curvatureSelectedTotal, hc]
    norm_num [q96, P2OriginalSeedChronologicalMaxArithmetic.curvatureSelectedTotal]
  · rw [mixedSelectedTotal, hm]
    norm_num [q96, P2OriginalSeedChronologicalMaxArithmetic.mixedSelectedTotal]

theorem full_seed_slot21 :
    curvatureGain = P2OriginalCertificateBudget.savingLower
      P2OriginalSeedChronologicalMaxArithmetic.slot21 := by
  unfold curvatureGain
  rw [full_literal_totals.2.1, full_literal_totals.1]
  exact P2OriginalSeedChronologicalMaxArithmetic.curvature_increment_exact

theorem full_seed_slot22 :
    mixedGain = P2OriginalCertificateBudget.savingLower
      P2OriginalSeedChronologicalMaxArithmetic.slot22 := by
  unfold mixedGain
  rw [full_literal_totals.2.2, full_literal_totals.2.1]
  exact P2OriginalSeedChronologicalMaxArithmetic.mixed_increment_exact

theorem actual_row_telescope (i : RowIndex) :
    ((entry i).mixedSelected : ℤ) - (entry i).logSelected =
      (((entry i).curvatureSelected : ℤ) - (entry i).logSelected) +
        (((entry i).mixedSelected : ℤ) - (entry i).curvatureSelected) := by ring

theorem full_seed_slot_telescope :
    mixedSelectedTotal - adoptedLogTotal =
      P2OriginalCertificateBudget.savingLower P2OriginalSeedChronologicalMaxArithmetic.slot21 +
      P2OriginalCertificateBudget.savingLower P2OriginalSeedChronologicalMaxArithmetic.slot22 := by
  rw [← full_seed_slot21, ← full_seed_slot22]
  unfold curvatureGain mixedGain
  ring

theorem actual_owner_stage_gains_nonneg (i : RowIndex) :
    (0 : ℤ) ≤ ((entry i).curvatureSelected : ℤ) - (entry i).logSelected ∧
      (0 : ℤ) ≤ ((entry i).mixedSelected : ℤ) - (entry i).curvatureSelected := by
  have h := all_actual_row_maxima i
  refine ⟨sub_nonneg.mpr ?_, sub_nonneg.mpr ?_⟩
  · exact_mod_cast h.1
  · exact_mod_cast h.2.1

/-- The selected sum in the real physical enclosure equals the log stage
with each subsequent ledger increment added exactly once. -/
theorem selected_real_sum_eq :
    (∑ i : RowIndex, ((entry i).mixedSelected : ℝ) / (q96 : ℝ)) =
      (adoptedLogTotal : ℝ) +
        (P2OriginalCertificateBudget.savingLower
          P2OriginalSeedChronologicalMaxArithmetic.slot21 : ℝ) +
        (P2OriginalCertificateBudget.savingLower
          P2OriginalSeedChronologicalMaxArithmetic.slot22 : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) full_seed_slot_telescope
  push_cast at h
  have hm :
      (mixedSelectedTotal : ℝ) =
        ∑ i : RowIndex, ((entry i).mixedSelected : ℝ) / (q96 : ℝ) := by
    unfold mixedSelectedTotal
    push_cast
    rw [Finset.sum_div]
  rw [← hm]
  linarith

end ImbalancedChen.P2Winner9CompleteSeedChronology
