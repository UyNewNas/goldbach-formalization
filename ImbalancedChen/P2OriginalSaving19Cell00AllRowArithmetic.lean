import ImbalancedChen.P2OriginalSaving19Cell00Row000OldFloor
import ImbalancedChen.P2OriginalSaving19Cell00Row001Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row002Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row003Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row004Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row005Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row006Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row007Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row008Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row009Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row010Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row011Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row012Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row013Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row014Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row015Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row016Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row017Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row018Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row019Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row020Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row021Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row022Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row023Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row024Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row025Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row026Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row027Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row028Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row029Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row030Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row031Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row032Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row033Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row034Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row035Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row036Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row037Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row038Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row039Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row040Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row041Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row042Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row043Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row044Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row045Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row046Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row047Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row048Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row049Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row050Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row051Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row052Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row053Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row054Arithmetic
import ImbalancedChen.P2OriginalSaving19Cell00Row055Arithmetic

/-! Finite assembly of the unchanged ten row-arithmetic clauses for all 56
actual cell00 rows. Each child certificate is reused opaquely. Only the old
moment Q96 floor is included; degree-six/Q80/new Q96 and integral soundness
are distinct remaining obligations. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Geometry00Decoding
open P2OriginalSaving19Geometry00BoundedAccess
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

theorem all_bounded_row_data_checks : ∀ r : Fin 56,
    RowDataChecksFor (boundedRowVertex r) (boundedRow r) := by
  intro r
  fin_cases r
  · exact P2OriginalSaving19Cell00Row000.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row001.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row002.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row003.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row004.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row005.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row006.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row007.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row008.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row009.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row010.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row011.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row012.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row013.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row014.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row015.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row016.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row017.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row018.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row019.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row020.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row021.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row022.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row023.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row024.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row025.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row026.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row027.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row028.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row029.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row030.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row031.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row032.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row033.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row034.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row035.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row036.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row037.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row038.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row039.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row040.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row041.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row042.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row043.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row044.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row045.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row046.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row047.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row048.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row049.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row050.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row051.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row052.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row053.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row054.bounded_row_data_checks
  · exact P2OriginalSaving19Cell00Row055.bounded_row_data_checks

theorem all_raw_row_data_checks (r : Fin 56) :
    RowDataChecksFor
      (fun i j => (concreteGeometry00.vertices[
        (concreteGeometry00.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!)
      (concreteGeometry00.rows[r.val]!) := by
  have hv : (fun i : Fin 9 => fun j : Fin 8 =>
      (concreteGeometry00.vertices[
        (concreteGeometry00.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!) =
      boundedRowVertex r := by
    funext i j
    exact raw_vertex_no_fallback r i j
  exact Eq.mpr (congrArg₂ RowDataChecksFor hv (row_lookup_no_fallback r))
    (all_bounded_row_data_checks r)

theorem all_moment_old_matches_geometry : ∀ r : Fin 56,
    (momentConcrete00.rows[r.val]!).oldFloorQ96 = (boundedRow r).jensenFloorQ96 := by
  intro r
  fin_cases r
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row000.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row000.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row000.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row001.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row001.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row001.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row002.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row002.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row002.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row003.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row003.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row003.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row004.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row004.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row004.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row005.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row005.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row005.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row006.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row006.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row006.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row007.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row007.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row007.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row008.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row008.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row008.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row009.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row009.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row009.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row010.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row010.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row010.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row011.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row011.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row011.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row012.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row012.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row012.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row013.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row013.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row013.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row014.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row014.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row014.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row015.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row015.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row015.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row016.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row016.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row016.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row017.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row017.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row017.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row018.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row018.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row018.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row019.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row019.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row019.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row020.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row020.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row020.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row021.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row021.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row021.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row022.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row022.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row022.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row023.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row023.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row023.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row024.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row024.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row024.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row025.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row025.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row025.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row026.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row026.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row026.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row027.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row027.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row027.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row028.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row028.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row028.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row029.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row029.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row029.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row030.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row030.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row030.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row031.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row031.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row031.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row032.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row032.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row032.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row033.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row033.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row033.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row034.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row034.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row034.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row035.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row035.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row035.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row036.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row036.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row036.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row037.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row037.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row037.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row038.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row038.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row038.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row039.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row039.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row039.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row040.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row040.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row040.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row041.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row041.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row041.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row042.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row042.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row042.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row043.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row043.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row043.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row044.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row044.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row044.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row045.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row045.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row045.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row046.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row046.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row046.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row047.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row047.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row047.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row048.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row048.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row048.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row049.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row049.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row049.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row050.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row050.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row050.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row051.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row051.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row051.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row052.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row052.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row052.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row053.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row053.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row053.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row054.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row054.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row054.boundedRow_eq.symm))
  · exact (congrArg (fun g => g.oldFloorQ96) P2OriginalSaving19Cell00Row055.raw_moment_row_eq).trans
      (P2OriginalSaving19Cell00Row055.moment_old_matches_geometry.trans
        (congrArg (fun g => g.jensenFloorQ96) P2OriginalSaving19Cell00Row055.boundedRow_eq.symm))

theorem all_moment_old_eq_evaluator : ∀ r : Fin 56,
    (momentConcrete00.rows[r.val]!).oldFloorQ96 =
      oldFloorQ96 (massOf (boundedRow r)) (meansOf (boundedRow r)) := by
  intro r
  fin_cases r
  · exact P2OriginalSaving19Cell00Row000.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row001.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row002.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row003.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row004.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row005.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row006.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row007.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row008.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row009.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row010.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row011.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row012.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row013.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row014.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row015.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row016.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row017.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row018.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row019.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row020.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row021.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row022.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row023.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row024.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row025.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row026.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row027.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row028.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row029.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row030.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row031.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row032.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row033.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row034.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row035.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row036.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row037.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row038.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row039.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row040.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row041.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row042.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row043.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row044.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row045.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row046.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row047.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row048.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row049.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row050.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row051.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row052.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row053.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row054.actual_moment_old_eq_bounded_evaluator
  · exact P2OriginalSaving19Cell00Row055.actual_moment_old_eq_bounded_evaluator

#print axioms all_bounded_row_data_checks
#print axioms all_raw_row_data_checks
#print axioms all_moment_old_matches_geometry
#print axioms all_moment_old_eq_evaluator

end ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic
