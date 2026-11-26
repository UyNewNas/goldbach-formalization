# Preserved join-only source preparation

This earlier source package prepares the Cell05 fields88 supplier join without
executing Lean. It was not deployed by the current continuation. The actual P2
dispatch instead uses the complete frozen package in
`../cell05-connections14-run-20261126/`, whose `stage_entry.py --preflight-only`
performs the supplier and runtime checks before the new proof steps.

The files here preserve the original preparation and its local package readback.
They are neither a cloud execution receipt nor evidence of new proof acceptance.
Resume the actual job recorded in `../cell05-deployment-20261126/`; do not deploy
this earlier package over that job's stage or provider.
