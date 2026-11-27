"""Reuse existing symbolic transports at original cell index one."""
import hashlib
import json
from pathlib import Path
import re

from generate_fields import PACKAGE, REPO, NOTICE, descriptor, immutable_write

PINS = {
    "ImbalancedChen/P2Saving16Cell00PayloadBinding.lean":
        "61722aa2f8d764fa757245784217e2f9cd9442393333cb594e334b1883425c1b",
    "docs/source-only/20261126-p2-5-cell00-consumer/ImbalancedChen/P2Saving16Cell00Decoded.lean":
        "c91601b44d5b88f753ec2d7beb340a6161269c219bfe366690afdb5a6b3b9e6c",
    "docs/source-only/20261126-p2-5-cell00-parse-transport/ImbalancedChen/P2Saving16Cell00OriginalParse.lean":
        "522cf6bda9efdec24e9ba25c826a9eed29b06199f7f6af514e360c64369fb30d",
    "docs/source-only/20261126-p2-5-cell01-parser-typed/ImbalancedChen/P2Saving16Cell01DirectParse.lean":
        "bcd49a84496c676733fc39295159b27d472a72e47d7a619ea2d36dc212385928",
    "docs/source-only/20261126-p2-5-cell01-parser-typed/ImbalancedChen/P2Saving16Cell01OriginalJson.lean":
        "575bba2bf1813fb39a9086d36a4e5756510a7cce6517097536ad7f8cf2f37657",
}


def main():
    sources = {}
    for name, sha in PINS.items():
        data = (REPO / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != sha:
            raise ValueError(f"Changed existing transport/candidate: {name}")
        sources[name] = data.decode()
    paths = list(PINS)
    outputs = {}
    for name, donor in [("PayloadBinding", sources[paths[0]]),
                        ("Decoded", sources[paths[1]])]:
        source = donor.replace("Cell00", "Cell01").replace("cell00", "cell01")
        source = re.sub(r"/\-![\s\S]*?\-/\n", NOTICE, source, count=1)
        outputs[f"P2Saving16Cell01{name}"] = source

    donor = sources[paths[2]]
    helpers = donor[donor.index("private theorem parsedCell_of_parse_decode"):
                    donor.index("theorem cell00_original_decode")]
    helpers = helpers.replace("private theorem", "theorem")
    outputs["P2OriginalSaving16ArchiveCompose"] = (
        "import ImbalancedChen.P2OriginalSaving16FiniteCore\n\n" + NOTICE
        + "namespace ImbalancedChen.P2OriginalSaving16ArchiveCompose\n"
        + "open P2OriginalSaving19Archive (SourceJson)\n"
        + "open P2OriginalSaving16OriginalArchive\n"
        + "  (originalText decodeCell parsedCell parsedCellSuccess archive)\n\n"
        + "/- Public extraction of the three already written symbolic transports. -/\n"
        + helpers + "end ImbalancedChen.P2OriginalSaving16ArchiveCompose\n")
    body = donor[donor.index("theorem cell00_original_decode"):]
    body = (body.replace("Cell00", "Cell01").replace("cell00", "cell01")
            .replace("(0 : Fin 14)", "(1 : Fin 14)"))
    outputs["P2Saving16Cell01OriginalParse"] = (
        "import ImbalancedChen.P2OriginalSaving16ArchiveCompose\n"
        "import ImbalancedChen.P2Saving16Cell01OriginalJson\n"
        "import ImbalancedChen.P2Saving16Cell01Decoded\n\n" + NOTICE
        + "namespace ImbalancedChen.P2Saving16Cell01OriginalParse\n"
        + "open P2OriginalSaving16OriginalArchive (parsedCell parsedCellSuccess archive)\n"
        + "open P2OriginalSaving16ArchiveCompose\n"
        + "open P2Saving16Cell01Segments (rootValue)\n"
        + "open P2Saving16Cell01OriginalJson (cell01_original_json)\n"
        + "open P2Saving16Cell01Decoded (decodedCell01 cell01_decode)\n\n"
        + body)
    rows = []
    for module, source in outputs.items():
        path = PACKAGE / "ImbalancedChen" / (module + ".lean")
        immutable_write(path, source)
        row = descriptor(path)
        row["module"] = "ImbalancedChen." + module
        row["declarations_in_source"] = re.findall(
            r"^(?:noncomputable )?(?:theorem|def) (\w+)", source, re.M)
        rows.append(row)
    manifest = {
        "schema": "p25-cell01-transport-candidates-v1",
        "status": "SOURCE_ONLY_UNCOMPILED",
        "Lean_executed": False, "P2_5_proved": False,
        "canonical_cell_index": 1,
        "inputs": [descriptor(REPO / name) for name in PINS],
        "outputs": rows,
        "source_statements_do_not_supply": [
            "prior Cell01 parser acceptance", "simplexValid",
            "Q96 geometric arithmetic", "fourteen-cell aggregate", "prime-sum PP bound"],
    }
    immutable_write(PACKAGE / "TRANSPORT_MANIFEST.json", json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"new_transport_modules": len(rows),
                      "declarations_in_source": sum(len(r["declarations_in_source"]) for r in rows)}))


if __name__ == "__main__":
    main()
