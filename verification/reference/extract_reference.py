"""Refresh auditable VE-only excerpts from the user's existing certificates.

This is a maintenance command, not part of the numerical or Lean proof.
Each selected function is copied without editing its body. Only line endings
are normalized to LF; the manifest records full original byte SHA256 values.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


def selected_node(tree, name):
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
        if isinstance(node, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == name for t in node.targets
        ):
            return node
    raise ValueError(f"Missing source node: {name}")


def extract(source_dir, output_dir):
    dependency = source_dir / "certify_conservative_chen.py"
    dependency_text = dependency.read_text(encoding="utf-8")
    ceil_node = selected_node(ast.parse(dependency_text), "ceildiv")
    manifest = {
        "scope": "Only the integer VE interval arithmetic; no sieve or integral certificate.",
        "normalization": "UTF-8 source with CRLF normalized to LF; selected bodies unchanged.",
        "sources": {},
        "snapshots": {},
        "coordinate_initialization": (
            "NT=int(THETA*DEN), NMU=int(MU*DEN), after asserting denominator=1; "
            "these are the identical first two outputs of the original map(coord,...)."
        ),
        "extended_scope": (
            "phi_range is preserved verbatim, including its extension branch, but "
            "fixtures and the Lean bridge only use x0<NMU and x1<=NMU."
        ),
    }
    for path in (dependency, source_dir / "certify_variable_prefix.py",
                 source_dir / "certify_extended_prefix.py"):
        manifest["sources"][path.name] = {
            "original_path": str(path.resolve()),
            "sha256": sha(path.read_bytes()),
        }
    for kind in ("variable", "extended"):
        original = source_dir / f"certify_{kind}_prefix.py"
        source = original.read_text(encoding="utf-8")
        tree = ast.parse(source)
        selections = [("ceildiv", dependency.name, dependency_text, ceil_node)]
        selections += [(name, original.name, source, selected_node(tree, name))
                       for name in ("THETA", "MU", "DEN", "v_lo", "v_point_hi", "v_hi", "phi_range")]
        excerpts = []
        parts = [
            '"""VE-only exact source excerpts; see source_manifest.json for provenance."""',
            "from fractions import Fraction as F",
        ]
        for name, filename, text, node in selections:
            segment = ast.get_source_segment(text, node)
            assert segment is not None
            parts.append(segment)
            excerpts.append({
                "name": name,
                "source": filename,
                "start_line": node.lineno,
                "end_line": node.end_lineno,
                "sha256": sha(segment.encode("utf-8")),
            })
        output = output_dir / f"{kind}_prefix_ve.py"
        output.write_text("\n\n\n".join(parts) + "\n", encoding="utf-8", newline="\n")
        manifest["snapshots"][output.name] = {
            "sha256": sha(output.read_bytes()), "excerpts": excerpts,
        }
    (output_dir / "source_manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", required=True, type=Path)
    args = parser.parse_args()
    extract(args.source_dir, Path(__file__).resolve().parent)
