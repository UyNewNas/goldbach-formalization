from pathlib import Path
import base64,hashlib,json
p=Path('/workspace/p29-radial-profile-verification-20261125-pinbind-v4/portable/profile-complete-preset9-transfer/complete.part01')
def stamp(p):
 s=p.stat();return[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
before=stamp(p);b=p.read_bytes()
assert len(b)==2971860 and hashlib.sha256(b).hexdigest()=='f76de0ccc57603946395299fbc107c34cfcec2ea7ca7ef8fdc17e4d85f9fdba9'
assert stamp(p)==before
print('P29_COMPLETE_XZ9_PART '+json.dumps({'index':1,'byte_offset':5500000,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'path':str(p),'stat_before':before,'stat_after':stamp(p),'Lean_calls':0,'writes':0,'recompression':False,'repacking':False}),flush=True)
print('P29_COMPLETE_XZ9_DATA 1 '+base64.b64encode(b).decode(),flush=True)
