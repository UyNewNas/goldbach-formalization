# P2.9 CoordinateCore — accepted

The existing source `58dc5b88daeb97e26a6a90153d0644a4c28c8a84` passed normal compilation, the named independent kernel checker and complete owned-declaration audit in P1 task `job_0669bcefd1614c419277f509c399904c`. The export-only task `job_032729d7e61c4c899af1213152e6ffc0` did not compile or replay it again.

The root reviewer verified the exact 62-member archive, every member size and SHA-256, the source Git object identity, original tool hashes, exact inventory and all six complete type strings and axiom records. The six declarations are two public theorems and four generated proofs. Only `Classical.choice`, `Quot.sound` and `propext` occur transitively.

For a natural tuple with at least two coordinates, each at least two, the source proves `2 * u i <= product u`; hence `product u <= 2 * N` implies `u i <= N`. It preserves repeated coordinates and the full product range up to `2*N`.

`ARCHIVE_TRANSPORT.json` lists the five binary parts in concatenation order. Their concatenation has 2,310,055 bytes and SHA-256 `b9a3a5b4a4afc3091d35e65dfac5463da2ff93ee869b10f1b690fd6084794523`. The complete archive includes original sources, outputs, validators, exact process logs, actual import bindings and the release seal. The six principal JSON receipts are also directly accessible here.

The frozen source's old SOURCE_ONLY comment is historical; this receipt qualifies those exact bytes. This acceptance adds one module and six owned declarations, bringing the tracked P2.9 increment to 13 modules and 144 owned declarations. It does not complete P2.9 or promote its board node. No whole-standard-import kernel replay is claimed.
