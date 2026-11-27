from pathlib import Path
import base64, hashlib, json, os, subprocess, sys
root=Path('/workspace/p34-parameter-derivative-probe-20261127-r3')
root.mkdir()
source=root/'P34ParameterDerivativeProbeR3.lean'
source.write_bytes(base64.b64decode('aW1wb3J0IE1hdGhsaWIuTnVtYmVyVGhlb3J5Lk1vZHVsYXJGb3Jtcy5FaXNlbnN0ZWluU2VyaWVzLlVuaWZvcm1Db252ZXJnZW5jZQppbXBvcnQgTWF0aGxpYi5UYWN0aWMKaW1wb3J0IE1hdGhsaWIuQW5hbHlzaXMuQ2FsY3VsdXMuU21vb3RoU2VyaWVzCmltcG9ydCBNYXRobGliLkFuYWx5c2lzLlNwZWNpYWxGdW5jdGlvbnMuRXhwRGVyaXYKaW1wb3J0IE1hdGhsaWIuQW5hbHlzaXMuU3BlY2lhbEZ1bmN0aW9ucy5Qb3cuUmVhbAppbXBvcnQgTWF0aGxpYi5BbmFseXNpcy5Db21wbGV4LkNhdWNoeUludGVncmFsCgovLSBEaWFnbm9zdGljIHJlZHVjdGlvbiBvZiBleGlzdGluZyBzb3VyY2UuIE5vIGZ1bGwtbW9kdWxlIGFjY2VwdGFuY2UuIC0vCgpuYW1lc3BhY2UgSW1iYWxhbmNlZENoZW4uUGFydDMuUHJpbWl0aXZlRWlzZW5zdGVpblBhcmFtZXRlckFuYWx5dGljCgpub25jb21wdXRhYmxlIHNlY3Rpb24KCm9wZW4gQ29tcGxleCBVcHBlckhhbGZQbGFuZSBFaXNlbnN0ZWluU2VyaWVzIFNldCBNZXRyaWMgVG9wb2xvZ3kKb3BlbiBzY29wZWQgVXBwZXJIYWxmUGxhbmUKCmFiYnJldiBQcmltaXRpdmVQYWlyIDo9IEVpc2Vuc3RlaW5TZXJpZXMuZ2FtbWFTZXQgMSAxIDAKCmRlZiBwb3NpdGl2ZUJhc2UgKHogOiDihI0pICh2IDogUHJpbWl0aXZlUGFpcikgOiDihJ0gOj0KICB6LmltIC8g4oCWKHYuMSAwIDog4oSCKSAqICh6IDog4oSCKSArICh2LjEgMSA6IOKEginigJYgXiAyCgpkZWYgY29tcGxleFNlZWQgKHogOiDihI0pICh2IDogUHJpbWl0aXZlUGFpcikgKHMgOiDihIIpIDog4oSCIDo9CiAgQ29tcGxleC5leHAgKHMgKiAoUmVhbC5sb2cgKHBvc2l0aXZlQmFzZSB6IHYpIDog4oSCKSkKCmRlZiBjb21wbGV4U2VlZERlcml2YXRpdmUgKHogOiDihI0pICh2IDogUHJpbWl0aXZlUGFpcikgKHMgOiDihIIpIDog4oSCIDo9CiAgKFJlYWwubG9nIChwb3NpdGl2ZUJhc2UgeiB2KSA6IOKEgikgKiBjb21wbGV4U2VlZCB6IHYgcwoKdGhlb3JlbSBjb21wbGV4U2VlZF9oYXNEZXJpdkF0ICh6IDog4oSNKSAodiA6IFByaW1pdGl2ZVBhaXIpIChzIDog4oSCKSA6CiAgICBIYXNEZXJpdkF0IChjb21wbGV4U2VlZCB6IHYpIChjb21wbGV4U2VlZERlcml2YXRpdmUgeiB2IHMpIHMgOj0gYnkKICB1bmZvbGQgY29tcGxleFNlZWREZXJpdmF0aXZlIGNvbXBsZXhTZWVkCiAgc2ltcGEgb25seSBbbXVsX2NvbW1dIHVzaW5nCiAgICAoaGFzRGVyaXZBdF9tdWxfY29uc3QgKHggOj0gcykgKFJlYWwubG9nIChwb3NpdGl2ZUJhc2UgeiB2KSA6IOKEgikpLmNleHAKCmVuZAoKZW5kIEltYmFsYW5jZWRDaGVuLlBhcnQzLlByaW1pdGl2ZUVpc2Vuc3RlaW5QYXJhbWV0ZXJBbmFseXRpYwo='))
assert hashlib.sha256(source.read_bytes()).hexdigest() == 'b7edd7388548793d6e561e1cbd7def32f565999257e6b4de74452872ae8e61ee'
toolchain=Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
lean=toolchain/'bin/lean'
assert hashlib.sha256(lean.read_bytes()).hexdigest() == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
mathlib=Path('/workspace/compile-deps/mathlib')
assert subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip() == 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
packages=['plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries','Cli']
roots=[mathlib/'.lake/packages'/p/'.lake/build/lib/lean' for p in packages]+[mathlib/'.lake/build/lib/lean']
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','LEAN4_','ELAN_','LAKE_'))}
env.update(LEAN_PATH=os.pathsep.join(map(str,roots)),LEAN_SYSROOT=str(toolchain))
command=[str(lean),'-t0','-j1','-M8000','-DwarningAsError=true',str(source)]
r=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log=('command='+json.dumps(command)+'\n').encode()+r.stdout
(root/'strict.log').write_bytes(log)
report={'diagnostic_only':True,'acceptance_credit':False,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'lean_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),'mathlib_commit':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','command':command,'exit_code':r.returncode,'log_sha256':hashlib.sha256(log).hexdigest()}
(root/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print('P34_DERIVATIVE_PROBE_REPORT '+json.dumps(report),flush=True)
print(log.decode(),end='',flush=True)
sys.exit(r.returncode)
