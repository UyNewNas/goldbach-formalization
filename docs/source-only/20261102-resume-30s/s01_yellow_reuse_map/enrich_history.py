import hashlib
import json
import pathlib

root = pathlib.Path(r"E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation")
d = root / "docs/source-only/20261102-resume-30s/s01_yellow_reuse_map"
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

hp = d / "HISTORICAL_EVIDENCE.json"
h = json.loads(hp.read_text(encoding="utf-8"))
for row in h["exact_same_source_receipts"]:
    receipt_path = root / pathlib.Path(row["receipt_path"])
    receipt = json.loads(receipt_path.read_text(encoding="utf-8-sig"))
    binding = receipt.get("binding", {})
    dependency_parts = binding.get("dependency_parts", {})
    for match in row["exact_source_matches"]:
        if match["kind"] == "module_source":
            parts = receipt.get("object_parts", {})
        else:
            parts = dependency_parts.get(match["module"], {})
        match["matched_olean_sha256"] = parts.get(".olean")
        match["receipt_scope"] = receipt.get("scope")
        match["reusable_compile_artifact"] = (
            row["status"] == "PASS"
            and row.get("exit_code") == 0
            and match.get("matched_olean_sha256") is not None
            and all(row.get("pin_equality", {}).values())
        )
hp.write_text(json.dumps(h, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

mp = d / "MAP.json"
m = json.loads(mp.read_text(encoding="utf-8"))
m["historical_evidence"]["sha256"] = sha(hp)
for node in m["yellow_nodes"]:
    for ev in node.get("historical_reused_source_evidence", []):
        for r in ev.get("passing_receipts", []):
            for histrow in h["exact_same_source_receipts"]:
                if r["receipt_path"] == histrow["receipt_path"]:
                    r["exact_source_matches"] = histrow["exact_source_matches"]
                    r["direct_dependencies"] = histrow.get("direct_dependencies")
mp.write_text(json.dumps(m, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

rp = d / "REGISTRY.json"
reg = json.loads(rp.read_text(encoding="utf-8"))
reg["historical_evidence"]["sha256"] = sha(hp)
reg["map"]["sha256"] = sha(mp)
rp.write_text(json.dumps(reg, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"historical_evidence_sha256": sha(hp), "map_sha256": sha(mp), "registry_sha256": sha(rp)}))
