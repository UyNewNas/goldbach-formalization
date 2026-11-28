from pathlib import Path
import subprocess
ROOT=Path(__file__).resolve().parent
command=['python3','/workspace/blue-build-tools/serialize_validation_lane.py','--state','/workspace/blue-build-tools/member-runtime-evidence/state.json','--receipt',str(ROOT/'LANE_00003.json'),'python3','/workspace/blue-build-tools/run_guarded.py','--state','/workspace/blue-build-tools/member-runtime-evidence/state.json','lake','--no-build','env','python3','-B',str(ROOT/'readback_worker_00003.py')]
raise SystemExit(subprocess.call(command,cwd="/workspace/blue-member-build"))
