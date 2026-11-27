"""Exercise the real frozen-cache parser without producing a controller."""
import copy
import json
from pathlib import Path
import unittest

try:
    import cache_inputs
except ModuleNotFoundError:
    cache_inputs = None


PROBE = (Path(__file__).resolve().parent.parent /
         "p29-package-resume/docs/verification/20261127-p2-9-standard-package-resume/CACHE_PROBE_RESULT.json")


class CacheInputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = PROBE.read_bytes()
        cls.report = json.loads(cls.raw)

    def setUp(self):
        self.assertIsNotNone(cache_inputs, "cache-input validator is not implemented")

    def report_copy(self):
        return copy.deepcopy(self.report)

    def battery(self, report, module="Batteries", facet=".olean"):
        return next(row for row in report["accepted_cached_standard_facets"]
                    if row["original"]["module"] == module and row["original"]["facet"] == facet)

    def test_actual_report_selects_exact_batteries_and_excludes_44_analytic_rows(self):
        context = cache_inputs.load_cache_context(self.raw)
        rows = context["rows"]
        keys = [(row["original"]["module"], row["original"]["facet"]) for row in rows]
        self.assertEqual(len(self.report["accepted_cached_standard_facets"]), 1004)
        self.assertEqual(len(rows), 960)
        self.assertEqual(len({module for module, _ in keys}), 192)
        self.assertEqual(keys, sorted(keys))
        self.assertTrue(all(module == "Batteries" or module.startswith("Batteries.") for module, _ in keys))
        self.assertEqual({facet for _, facet in keys}, {".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"})
        self.assertEqual(context["provenance"]["excluded_standard_probe_rows"], 44)

    def test_public_loader_rejects_unpinned_or_reencoded_report(self):
        with self.assertRaisesRegex(ValueError, "actual cache probe"):
            cache_inputs.load_cache_context(self.raw + b"\n")
        with self.assertRaisesRegex(ValueError, "actual cache probe"):
            cache_inputs.load_cache_context(b"{}")

    def test_namespace_filter_does_not_accept_batteries_name_prefix(self):
        report = self.report_copy()
        excluded = next(row for row in report["accepted_cached_standard_facets"]
                        if row["original"]["module"] == "AnalyticNumberTheory")
        excluded["original"]["module"] = "BatteriesExtra"
        context = cache_inputs._validate_report(report)
        self.assertEqual(len(context["rows"]), 960)
        self.assertNotIn("BatteriesExtra", {row["original"]["module"] for row in context["rows"]})

    def test_duplicate_or_missing_batteries_facet_is_rejected(self):
        report = self.report_copy()
        rows = report["accepted_cached_standard_facets"]
        rows.append(copy.deepcopy(self.battery(report)))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            cache_inputs._validate_report(report)
        report = self.report_copy()
        report["accepted_cached_standard_facets"].remove(self.battery(report))
        with self.assertRaisesRegex(ValueError, "960|five facets"):
            cache_inputs._validate_report(report)

    def test_receipt_and_selected_original_identity_must_match(self):
        report = self.report_copy()
        self.battery(report)["original"]["identity"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "receipt.*identity"):
            cache_inputs._validate_report(report)

    def test_original_module_path_and_snapshot_are_required(self):
        report = self.report_copy()
        self.battery(report)["original"]["identity"]["path"] += ".wrong"
        with self.assertRaisesRegex(ValueError, "module/facet path"):
            cache_inputs._validate_report(report)
        report = self.report_copy()
        self.battery(report)["original"]["original_snapshot_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "original snapshot"):
            cache_inputs._validate_report(report)

    def test_accepted_table_pin_is_required(self):
        report = self.report_copy()
        report["original_derived_table"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "accepted derived table"):
            cache_inputs._validate_report(report)

    def test_missing_or_symlink_current_input_is_rejected(self):
        for field, value in [("exists", False), ("is_symlink", True)]:
            with self.subTest(field=field):
                report = self.report_copy()
                self.battery(report)["current"][field] = value
                with self.assertRaisesRegex(ValueError, "current.*regular"):
                    cache_inputs._validate_report(report)

    def test_current_path_and_stat_size_cannot_substitute_another_input(self):
        report = self.report_copy()
        self.battery(report)["current"]["resolved_path"] = "/other/Batteries.olean"
        with self.assertRaisesRegex(ValueError, "current.*path"):
            cache_inputs._validate_report(report)
        report = self.report_copy()
        self.battery(report)["current"]["stat"][2] += 1
        with self.assertRaisesRegex(ValueError, "current.*stat"):
            cache_inputs._validate_report(report)
        report = self.report_copy()
        self.battery(report)["current"]["stat"].pop()
        with self.assertRaisesRegex(ValueError, "current.*stat"):
            cache_inputs._validate_report(report)

    def test_metadata_and_receipt_hashes_are_not_all_current_hashes(self):
        context = cache_inputs.load_cache_context(self.raw)
        provenance = context["provenance"]
        self.assertEqual(provenance["current_exact_hash_facets"], 5)
        self.assertEqual(provenance["current_exact_hash_modules"], ["Batteries.Tactic.Lemma"])
        self.assertEqual(provenance["metadata_only_facets"], 955)
        self.assertIs(provenance["all_current_facets_hashed"], False)
        self.assertNotIn("current_exact_file", self.battery(context["report"]))

    def test_lemma_observed_hash_is_required_and_must_equal_original(self):
        report = self.report_copy()
        self.battery(report, "Batteries.Tactic.Lemma")["current_exact_file"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Lemma.*hash"):
            cache_inputs._validate_report(report)
        report = self.report_copy()
        self.battery(report, "Batteries.Tactic.Lemma").pop("current_exact_file")
        with self.assertRaisesRegex(ValueError, "Lemma.*hash"):
            cache_inputs._validate_report(report)

    def test_source_and_donor_require_pinned_heads_and_clean_tracked_diff(self):
        report = self.report_copy()
        report["source_roots"]["donor_root"]["git"]["HEAD"]["stdout"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "source/donor"):
            cache_inputs._validate_report(report)
        report = self.report_copy()
        report["source_roots"]["source_root"]["git"]["tracked_diff"]["stdout"] = " M Batteries.lean"
        with self.assertRaisesRegex(ValueError, "source/donor"):
            cache_inputs._validate_report(report)

    def test_receipt_payload_and_checkpoint_producer_pins_are_authenticated(self):
        report = self.report_copy()
        report["records"]["batteries_receipt"]["base64"] = "e30="
        with self.assertRaisesRegex(ValueError, "record payload"):
            cache_inputs._validate_report(report)
        for name in ["CHECKPOINT.json", "producer_script"]:
            with self.subTest(record=name):
                report = self.report_copy()
                report["records"][name]["sha256"] = "0" * 64
                with self.assertRaisesRegex(ValueError, "record pin"):
                    cache_inputs._validate_report(report)

    def test_absent_raw_snapshot_receipt_linkage_does_not_grant_or_block_authority(self):
        context = cache_inputs.load_cache_context(self.raw)
        provenance = context["provenance"]
        self.assertEqual(context["report"]["original_snapshot_file_entries"], {})
        self.assertIs(provenance["raw_snapshot_record_linkage_verified"], False)
        self.assertIs(provenance["raw_snapshot_linkage_required_for_selection"], False)
        self.assertIs(provenance["receipt_is_historical_qualification_authority"], False)
        self.assertEqual(provenance["selection_authority"], "accepted_original_derived_facet_table")
        self.assertEqual(json.loads(context["receipt_raw"]), context["receipt"])
        self.assertEqual(json.loads(context["request_raw"]), context["request"])
        self.assertEqual(set(context["record_raw"]), {"REQUEST.json", "SNAPSHOT_SHAPE.json", "batteries_receipt"})


if __name__ == "__main__":
    unittest.main()
