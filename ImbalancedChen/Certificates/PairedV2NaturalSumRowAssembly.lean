import ImbalancedChen.Certificates.PairedV2NaturalSumRows
import ImbalancedChen.Certificates.PairedV2FullCertificateData
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock00
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock01
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock02
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock03
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock04
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock05
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock06
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock07
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock08
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock09
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock10
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock11

/-! Original Row/list interface, assembled from per-strip kernel length facts.
The Fin.cases proof selects those facts; it does not decide all row data. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem approximation_lengths : ∀ i : Fin 186,
    (approximations i).length = 512 - firstU i :=
  Fin.cases (motive := fun i : Fin 186 =>
    (approximations i).length = 512 - firstU i) strip326_length (
  Fin.cases strip327_length (
  Fin.cases strip328_length (
  Fin.cases strip329_length (
  Fin.cases strip330_length (
  Fin.cases strip331_length (
  Fin.cases strip332_length (
  Fin.cases strip333_length (
  Fin.cases strip334_length (
  Fin.cases strip335_length (
  Fin.cases strip336_length (
  Fin.cases strip337_length (
  Fin.cases strip338_length (
  Fin.cases strip339_length (
  Fin.cases strip340_length (
  Fin.cases strip341_length (
  Fin.cases strip342_length (
  Fin.cases strip343_length (
  Fin.cases strip344_length (
  Fin.cases strip345_length (
  Fin.cases strip346_length (
  Fin.cases strip347_length (
  Fin.cases strip348_length (
  Fin.cases strip349_length (
  Fin.cases strip350_length (
  Fin.cases strip351_length (
  Fin.cases strip352_length (
  Fin.cases strip353_length (
  Fin.cases strip354_length (
  Fin.cases strip355_length (
  Fin.cases strip356_length (
  Fin.cases strip357_length (
  Fin.cases strip358_length (
  Fin.cases strip359_length (
  Fin.cases strip360_length (
  Fin.cases strip361_length (
  Fin.cases strip362_length (
  Fin.cases strip363_length (
  Fin.cases strip364_length (
  Fin.cases strip365_length (
  Fin.cases strip366_length (
  Fin.cases strip367_length (
  Fin.cases strip368_length (
  Fin.cases strip369_length (
  Fin.cases strip370_length (
  Fin.cases strip371_length (
  Fin.cases strip372_length (
  Fin.cases strip373_length (
  Fin.cases strip374_length (
  Fin.cases strip375_length (
  Fin.cases strip376_length (
  Fin.cases strip377_length (
  Fin.cases strip378_length (
  Fin.cases strip379_length (
  Fin.cases strip380_length (
  Fin.cases strip381_length (
  Fin.cases strip382_length (
  Fin.cases strip383_length (
  Fin.cases strip384_length (
  Fin.cases strip385_length (
  Fin.cases strip386_length (
  Fin.cases strip387_length (
  Fin.cases strip388_length (
  Fin.cases strip389_length (
  Fin.cases strip390_length (
  Fin.cases strip391_length (
  Fin.cases strip392_length (
  Fin.cases strip393_length (
  Fin.cases strip394_length (
  Fin.cases strip395_length (
  Fin.cases strip396_length (
  Fin.cases strip397_length (
  Fin.cases strip398_length (
  Fin.cases strip399_length (
  Fin.cases strip400_length (
  Fin.cases strip401_length (
  Fin.cases strip402_length (
  Fin.cases strip403_length (
  Fin.cases strip404_length (
  Fin.cases strip405_length (
  Fin.cases strip406_length (
  Fin.cases strip407_length (
  Fin.cases strip408_length (
  Fin.cases strip409_length (
  Fin.cases strip410_length (
  Fin.cases strip411_length (
  Fin.cases strip412_length (
  Fin.cases strip413_length (
  Fin.cases strip414_length (
  Fin.cases strip415_length (
  Fin.cases strip416_length (
  Fin.cases strip417_length (
  Fin.cases strip418_length (
  Fin.cases strip419_length (
  Fin.cases strip420_length (
  Fin.cases strip421_length (
  Fin.cases strip422_length (
  Fin.cases strip423_length (
  Fin.cases strip424_length (
  Fin.cases strip425_length (
  Fin.cases strip426_length (
  Fin.cases strip427_length (
  Fin.cases strip428_length (
  Fin.cases strip429_length (
  Fin.cases strip430_length (
  Fin.cases strip431_length (
  Fin.cases strip432_length (
  Fin.cases strip433_length (
  Fin.cases strip434_length (
  Fin.cases strip435_length (
  Fin.cases strip436_length (
  Fin.cases strip437_length (
  Fin.cases strip438_length (
  Fin.cases strip439_length (
  Fin.cases strip440_length (
  Fin.cases strip441_length (
  Fin.cases strip442_length (
  Fin.cases strip443_length (
  Fin.cases strip444_length (
  Fin.cases strip445_length (
  Fin.cases strip446_length (
  Fin.cases strip447_length (
  Fin.cases strip448_length (
  Fin.cases strip449_length (
  Fin.cases strip450_length (
  Fin.cases strip451_length (
  Fin.cases strip452_length (
  Fin.cases strip453_length (
  Fin.cases strip454_length (
  Fin.cases strip455_length (
  Fin.cases strip456_length (
  Fin.cases strip457_length (
  Fin.cases strip458_length (
  Fin.cases strip459_length (
  Fin.cases strip460_length (
  Fin.cases strip461_length (
  Fin.cases strip462_length (
  Fin.cases strip463_length (
  Fin.cases strip464_length (
  Fin.cases strip465_length (
  Fin.cases strip466_length (
  Fin.cases strip467_length (
  Fin.cases strip468_length (
  Fin.cases strip469_length (
  Fin.cases strip470_length (
  Fin.cases strip471_length (
  Fin.cases strip472_length (
  Fin.cases strip473_length (
  Fin.cases strip474_length (
  Fin.cases strip475_length (
  Fin.cases strip476_length (
  Fin.cases strip477_length (
  Fin.cases strip478_length (
  Fin.cases strip479_length (
  Fin.cases strip480_length (
  Fin.cases strip481_length (
  Fin.cases strip482_length (
  Fin.cases strip483_length (
  Fin.cases strip484_length (
  Fin.cases strip485_length (
  Fin.cases strip486_length (
  Fin.cases strip487_length (
  Fin.cases strip488_length (
  Fin.cases strip489_length (
  Fin.cases strip490_length (
  Fin.cases strip491_length (
  Fin.cases strip492_length (
  Fin.cases strip493_length (
  Fin.cases strip494_length (
  Fin.cases strip495_length (
  Fin.cases strip496_length (
  Fin.cases strip497_length (
  Fin.cases strip498_length (
  Fin.cases strip499_length (
  Fin.cases strip500_length (
  Fin.cases strip501_length (
  Fin.cases strip502_length (
  Fin.cases strip503_length (
  Fin.cases strip504_length (
  Fin.cases strip505_length (
  Fin.cases strip506_length (
  Fin.cases strip507_length (
  Fin.cases strip508_length (
  Fin.cases strip509_length (
  Fin.cases strip510_length (
  Fin.cases strip511_length (
    fun i : Fin 0 => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem strip_sum_eq_map (i : Fin 186) (f : Approximation → ℕ) :
    (∑ j : Fin (512 - firstU i), f (approximation ⟨i, j⟩)) =
      ((approximations i).map f).sum := by
  change (∑ j : Fin (512 - firstU i),
    f ((approximations i).getD j.val default)) = _
  simpa only [approximation_lengths i] using sum_getD_eq_map (approximations i) f

theorem sum_rows_eq_list (f : Approximation → ℕ) :
    (∑ r : Row, f (approximation r)) =
      ((List.ofFn approximations).map (fun xs => (xs.map f).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp_rw [strip_sum_eq_map]
  rw [← List.sum_ofFn, List.ofFn_comp']

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
