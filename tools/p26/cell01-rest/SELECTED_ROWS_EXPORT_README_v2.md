# Explicit historical bounded-audit source relocation

Version 2 preserves the accepted version 1 script and package. Its only new input is `--shared-bounded-audit-source` for the P1 `c-prefix-budget-pause` scenario. The original historical audit path must be absent. The supplied regular canonical file must match the immutable historical result bytes and SHA-256 exactly. The unchanged historical path/argv/receipt and the current provider identity are retained separately in the report; the current file is watched and exported.

This fixes the real P1 export failure recorded in `docs/verification/20261126-p26/cell01-C-prefix/FIRST_EXPORT_FAILURE.json`. No proof command is repeated. P3 tail keeps the original version 1 exporter. Eleven local regression groups and an independent tail-option refusal subprocess passed. The full selected-row proof and export boundaries remain unchanged.
