from pathlib import Path
import base64,hashlib,json,sys
sys.dont_write_bytecode=True
out=Path('/workspace/p29-nonunit-quotient-verification-20261126-0117dd4/norm-fqn-002')
archive=out/'portable/NONUNIT_QUOTIENT_COMPLETE_EVIDENCE.tar.xz'
sha=lambda b:hashlib.sha256(b).hexdigest()
def stamp(p):
 s=p.stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
before=stamp(archive);raw=archive.read_bytes()
assert len(raw)==7419000 and sha(raw)=='9db6e95658f7be4377b04f5affa0687df88dce03552863389d8696c6d24641bc'
assert PART_INDEX in [0,1]
offset=5500000*PART_INDEX;piece=raw[offset:offset+5500000]
assert len(piece)==[5500000,1919000][PART_INDEX]
metadata={'schema':'p29_nonunit_002_existing_archive_slice_v1','archive':{'path':str(archive),'bytes':len(raw),'sha256':sha(raw),'stat_before':before},'part_index':PART_INDEX,'offset':offset,'bytes':len(piece),'sha256':sha(piece),'members':81,'tar_repacked':False,'Lean_calls':0,'filesystem_writes':0,'old_supplier_new_credit':0}
if PART_INDEX==1:
 names=['VALIDATION_RESULTS.json','SOURCE_AND_OUTPUTS_AFTER.json','full-owned-DECLARATION_TYPES_AXIOMS.json','full-owned-INVENTORY_NAME_SET_CHECK.json','full-owned.log','normal-build.log','normal-build-process.json','named-kernel.log','named-kernel-process.json','CONSUMER_SETUP_IMPORT_MATCH.json','RESUME_CONTEXT.json','portable/COMPLETE_MEMBERS.json']
 files={}
 for name in names:
  p=out/name;s=stamp(p);b=p.read_bytes();assert stamp(p)==s
  files[name]={'bytes':len(b),'sha256':sha(b),'base64':base64.b64encode(b).decode()}
 assert files['VALIDATION_RESULTS.json']['sha256']=='b818e145c7356d3ce8a5d0e34b887058996ba6a86e9010900ff19536fe83f170'
 assert files['SOURCE_AND_OUTPUTS_AFTER.json']['sha256']=='7e11d3b1fde9b0940e11a65328f8aeec1c2a431600cb7fa0b950fd02e15f47d7'
 assert files['full-owned-DECLARATION_TYPES_AXIOMS.json']['sha256']=='d431589b7f7f4652c5b8d049b25cb6e8eb9972b2b025b73d4f9b0c0b46e6db2c'
 assert files['full-owned-INVENTORY_NAME_SET_CHECK.json']['sha256']=='96f3a4b729c8192b21db337c9cf93262070ba692b2a96b8c6bfc67b385f81266'
 assert sum(v['bytes']for v in files.values())<2000000
 small={'schema':'p29_nonunit_002_original_metadata_and_all_types_v1','original_job':'job_7cf32d1b62054782911b4fc114699b7e','files':files}
 print('P29_NONUNIT_002_SMALL '+json.dumps(small),flush=True)
assert stamp(archive)==before and sha(archive.read_bytes())==sha(raw)
metadata['archive']['stat_after']=stamp(archive);metadata['archive']['unchanged']=True
print('P29_NONUNIT_002_PART '+json.dumps(metadata),flush=True)
print('P29_NONUNIT_002_DATA '+str(PART_INDEX)+' '+base64.b64encode(piece).decode(),flush=True)
