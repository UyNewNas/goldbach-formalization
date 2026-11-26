# Cell05 remaining fields: authored source batches

These local candidates continue the unchanged original cell05 geometry input:
201042 bytes, 28 vertices and 56 simplex rows. The input is taken from the
published raw05 evidence archive and remains bound to its original packed
data, parser and decoder. Candidate generation and host shape assertions are
not Lean acceptance.

The separately frozen row workflow v3 and its 15 mathematical candidates are
left unchanged. This directory first constructs the other six arrays with
bounded parser leaves, independent typed leaves and balanced binary assembly.

| Batch | Scope | New owners |
|---|---|---:|
| a_vertices_facets | First five metadata fields, vertices, facet vertex arrays | 10 |
| b_active8 | Original active8 enumeration array | 22 |
| c_values_faces | Original vertex values and face ledger arrays | 27 |
| d_minima | Original constraint minima array | 14 |

Each batch archive supplies its exact Lean sources, a complete environment
ownership/type/axiom audit for every owner, source/import pins and supplier
pins. Accepted supplier object bytes must be reused. Dependencies with no
accepted object receipt are explicitly marked pending and cannot be treated
as accepted suppliers.

The first four array batches only need published accepted suppliers; they do
not depend on the still-unaccepted new row phase1 owners. The later full
geometry connection will require the completed row network and all field
arrays. Root schedules all new normal, independent kernel and full-owned
checks. This source-only package does not itself execute or schedule them.

The parser leaf budget is at most eight fragments per owner. A fragment has at
most two array entries and a 768-byte target, while an oversized single entry
uses the existing nested original-fragment proof templates. Typed leaves
import only the matching parser leaf. Binary nodes avoid cumulative prefix
imports. Original field order and all original array delimiters are retained.

Local finite shape candidates cover vertex dimension, vertex factor count,
facet vertex indices and face vertex indices. Later shape composition will
bind those facts to the actual decoded Geometry and reuse the row-local shape
theorems. No geometric or integral interpretation is claimed.

Generate and package one batch locally:

```sh
python3 tools/p26/scalable-cell05-fields/generate_arrays.py --batch a_vertices_facets
python3 tools/p26/scalable-cell05-fields/prepare_batch.py --batch a_vertices_facets
```

Both commands refuse to overwrite changed candidates. Every package is read
back against its member manifest before handoff. It contains no object bodies
and reports zero new Lean executions. New compiled evidence remains on the
cloud host and may be exported only as an on-host archive plus a small metadata
summary, following the current task's evidence-transfer boundary.
