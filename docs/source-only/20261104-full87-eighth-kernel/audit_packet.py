#!/usr/bin/env python3
"""Lexical checks and independent exact-rational kernel regressions.

This is NOT a Lean parser, elaborator, kernel checker, numerical producer,
original-source membership test, or proof of a prime-mean estimate.
It reads only this packet. Failures abort without writing a passing report.
"""
from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
A = F(53, 13824)
B = 4 / A**9
C = 8 / A**10


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def lean_code(text: str) -> str:
    """Remove nested block comments, line comments and strings, retaining lines."""
    out: list[str] = []
    depth = 0
    string = False
    i = 0
    while i < len(text):
        ch = text[i]
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; out.extend("  "); i += 2
            elif two == "-/":
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if ch == "\n" else " "); i += 1
        elif string:
            if ch == "\\":
                out.extend("  "); i += 2
            else:
                if ch == '"': string = False
                out.append("\n" if ch == "\n" else " "); i += 1
        elif two == "/-":
            depth = 1; out.extend("  "); i += 2
        elif two == "--":
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out.extend(" " * (end - i)); i = end
        elif ch == '"':
            string = True; out.append(" "); i += 1
        else:
            out.append(ch); i += 1
    assert not depth and not string, "Unterminated comment or string"
    return "".join(out)


def check_source() -> dict:
    files: list[dict] = []
    graph: dict[str, list[str]] = {}
    for path in sorted(HERE.glob("*.lean")):
        data = path.read_bytes()
        code = lean_code(data.decode("utf-8"))
        escapes = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code)
        assert not escapes, (path.name, escapes)
        stack: list[str] = []
        close = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}
        for ch in code:
            if ch in "([{⟨": stack.append(ch)
            elif ch in close:
                assert stack and stack.pop() == close[ch], (path.name, ch)
        assert not stack, (path.name, stack)
        declarations = []
        for i, line in enumerate(code.splitlines(), 1):
            m = re.search(r"(?:^|\]\s+)(?:private\s+)?(def|theorem|lemma|abbrev|structure|inductive)\s+([^\s({:]+)", line)
            if m: declarations.append({"kind": m[1], "name": m[2], "line": i})
        names = [d["name"] for d in declarations]
        assert len(names) == len(set(names)), (path.name, "duplicate declaration")
        imports = re.findall(r"^import\s+(\S+)", code, flags=re.M)
        module = "ImbalancedChen." + path.stem
        graph[module] = imports
        files.append({"path": path.name, "module": module,
                      "lines": len(data.decode().splitlines()), "bytes": len(data),
                      "sha256": hashlib.sha256(data).hexdigest(), "git_blob_sha1": git_blob(data),
                      "imports": imports, "declarations": declarations})
    active: set[str] = set(); done: set[str] = set()
    def visit(node: str) -> None:
        if node in done or node not in graph: return
        assert node not in active, ("cycle", node)
        active.add(node)
        for child in graph[node]: visit(child)
        active.remove(node); done.add(node)
    for node in graph: visit(node)
    return {"files": files, "new_module_graph_acyclic": True,
            "lean_lines": sum(f["lines"] for f in files),
            "named_declarations": sum(len(f["declarations"]) for f in files)}


def down(n: int, x: F) -> F:
    y = (n + 1) * x
    return F(y.numerator // y.denominator - 1, n + 1)


def residual(s: F, j: F, p: F, m: F) -> F:
    assert p != s and m != s and j != 0
    return 4 * (m - p) / ((p - s) * (m - s) * j)


def regressions() -> dict:
    counts: Counter[str] = Counter()
    sample = None
    # Algebra over exact rationals, including negative S and small residuals.
    for sr in range(-3, 4):
        for jr in (1, 2, 5):
            for pr in (0, 1, 7):
                for mr in (1, 3, 11):
                    s = F(sr, 7); j = A**8 * jr
                    p = s + A + F(pr, 1000)
                    r = p + F(1, 1000)
                    m = r + F(mr, 300)
                    value = residual(s, j, r, m)
                    assert value == 4 * (1 / (r - s) - 1 / (m - s)) / j
                    assert 0 <= value <= B
                    assert value <= residual(s, j, p, m)
                    counts["residual_identity_bound_parent_cases"] += 1
                    for n in (999, 4095, 65535):
                        h = F(1, n + 1); low = down(n, m)
                        assert m - 2*h < low <= m - h
                        assert r < low  # every selected case genuinely meets the hypotheses
                        loss = value - residual(s, j, r, low)
                        assert loss == 4*(m-low)/((low-s)*(m-s)*j)
                        assert 0 < loss <= C*h
                        assert value <= residual(s, j, p, low) + C*h
                        counts["quantitative_endpoint_transport_cases"] += 1
                        if sample is None:
                            sample = {k: str(v) for k, v in {
                                "S": s, "J": j, "P": p, "R": r, "M": m,
                                "rounded_M": low, "actual_positive_loss": loss,
                                "uniform_bound": C*h}.items()}
    # Exact rounding walls, negative inputs, and n=0 are tested only for
    # the unrestricted floor identity, not claimed to be valid action trims.
    for n in (0, 1, 4, 16, 99):
        h = F(1, n + 1)
        for k in range(-8, 9):
            for offset in (-h/7, F(0), h/7):
                x = k*h + offset; y = down(n, x)
                assert x-2*h < y <= x-h
                if offset == 0: assert y == x-h
                counts["floor_boundary_cases"] += 1
    # Synthetic eight-coordinate cutoff tuples; these are NOT claims of
    # membership in the literal 87 polytopes or in an archive row.
    for k in range(1, 41):
        t = [A + F(k + 8-i, 1000) for i in range(8)]
        j = F(1)
        for x in t: j *= x
        assert all(x > A for x in t) and j >= A**8
        s = sum(t, F(0)); p = s + t[7] + F(1, 1000)
        r = p + F(1, 1000); m = r + F(1, 1000)
        assert t[7] < p-s <= r-s < m-s < 3*t[7]
        n = 99999; h = F(1, n+1); low = down(n, m)
        assert r < low
        assert residual(s, j, r, m) <= residual(s, j, p, low) + C*h
        counts["synthetic_eight_coordinate_cases"] += 1
    # A finite positive-measure model of the exact sum-integral budget.
    # It tests accounting, NOT Lebesgue integration or the Lean measure code.
    for keep_modulus in range(2, 12):
        source_loss = F(0); omitted = F(0); mass = F(0); box_omitted = F(0)
        n = 99999; h = F(1, n+1)
        for c in range(87):
            weight = F(c+1, 10000); j = A**8 * (c+1)
            s = F(c, 100); r = s + 2*A; m = r + A
            raw = residual(s, j, r, m)
            rounded = residual(s, j, r, down(n, m))
            retained = c % keep_modulus != 0
            source_loss += weight*(raw-rounded if retained else raw)
            omitted += F(0) if retained else weight*raw
            mass += weight
            if c % 13 == 0: box_omitted += weight*raw
        assert 0 <= source_loss <= omitted + C*h*mass
        assert source_loss + box_omitted <= omitted + box_omitted + C*h*mass
        counts["finite_measure_accounting_cases"] += 1
    return {"counts": dict(counts), "total_cases": sum(counts.values()),
            "scope": "independent rational model only; not original Source/archive evaluation",
            "nonzero_loss_example": sample,
            "constants": {"cutoff": str(A), "kernel_bound": str(B),
                          "rounding_constant": str(C),
                          "kernel_bound_scientific": f"{float(B):.6e}",
                          "rounding_constant_scientific": f"{float(C):.6e}"}}


def main() -> None:
    report = {"scope": "source hygiene and rational regression only",
              "lean_compiled": False, "kernel_replayed": False,
              "independent_review": False, "transitive_axioms_checked": False,
              "original_archive_loaded": False, "prime_mean_proved_by_audit": False,
              "audit_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              **check_source(), "regressions": regressions()}
    dest = HERE / "STATIC_QA.json"
    dest.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"lean_lines": report["lean_lines"],
                      "declarations": report["named_declarations"],
                      "tests": report["regressions"]["total_cases"],
                      "qa_sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}, ensure_ascii=False))


if __name__ == "__main__":
    main()
