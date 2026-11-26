from pathlib import Path,PurePosixPath
import base64,hashlib,io,json,lzma,tarfile
out=Path('/workspace/p29-radial-profile-verification-20261125-pinbind-v4/portable')
src=out/'PROFILE_NATURAL_COMPLETE_EVIDENCE.tar.xz'
dst=out/'PROFILE_NATURAL_COMPLETE_EVIDENCE.preset9.tar.xz'
parts_dir=out/'profile-complete-preset9-transfer'
assert not dst.exists()and not parts_dir.exists(),'Do not repeat the exact transfer.'
sha=lambda b:hashlib.sha256(b).hexdigest()
def stamp(p):
 s=p.stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
original_stat=stamp(src)
old=src.read_bytes()
assert len(old)==12081872 and sha(old)=='31480545fd0d2ad50c783df0cde0284094e7ca953cef38ce29d4eb420fefd9c7'
assert stamp(src)==original_stat
print(json.dumps({'stage':'original-archive-read','bytes':len(old),'sha256':sha(old),'new_Lean_calls':0}),flush=True)
tar_bytes=lzma.decompress(old)
tar_sha=sha(tar_bytes)
with tarfile.open(fileobj=io.BytesIO(tar_bytes),mode='r:')as t:
 members=t.getmembers()
 assert len(members)==85 and len({m.name for m in members})==85
 assert all(m.isfile()and not PurePosixPath(m.name).is_absolute()and '..'not in PurePosixPath(m.name).parts for m in members)
 manifest_bytes=t.extractfile('COMPLETE_MEMBERS.json').read()
 manifest=json.loads(manifest_bytes)
 assert len(manifest)==84 and set(manifest)=={m.name for m in members}-{'COMPLETE_MEMBERS.json'}
 member_names=[m.name for m in members]
print(json.dumps({'stage':'same-original-tar-decoded','tar_bytes':len(tar_bytes),'tar_sha256':tar_sha,'members':85,'manifest_entries':84,'compression_next':'xz preset 9; no repacking'}),flush=True)
new=lzma.compress(tar_bytes,format=lzma.FORMAT_XZ,preset=9)
assert lzma.decompress(new)==tar_bytes
assert stamp(src)==original_stat and sha(src.read_bytes())==sha(old),'Original archive changed during transfer preparation'
with dst.open('xb')as f:f.write(new)
parts_dir.mkdir()
piece_size=5500000
parts=[]
for index,offset in enumerate(range(0,len(new),piece_size)):
 piece=new[offset:offset+piece_size]
 p=parts_dir/f'complete.part{index:02}'
 with p.open('xb')as f:f.write(piece)
 parts.append({'index':index,'byte_offset':offset,'bytes':len(piece),'sha256':sha(piece),'path':str(p)})
emitted=[];used=0
for p in parts:
 if used+p['bytes']<=5600000:emitted.append(p['index']);used+=p['bytes']
metadata={'schema':'p29_p1_complete_same_tar_preset9_transport_v1','original_archive':{'path':str(src),'bytes':len(old),'sha256':sha(old),'stat_unchanged':True},'tar_bytes':len(tar_bytes),'tar_sha256':tar_sha,'new_archive':{'path':str(dst),'bytes':len(new),'sha256':sha(new),'compression':'xz preset 9'},'same_original_tar_bytes_verified':True,'tar_repacked':False,'members':85,'member_names':member_names,'complete_manifest_entries':84,'complete_manifest_sha256':sha(manifest_bytes),'parts':parts,'emitted_indices':emitted,'pending_indices':[p['index']for p in parts if p['index']not in emitted],'emitted_archive_bytes':used,'stdout_archive_byte_budget':5600000,'exporter_sha256':sha(SOURCE_TEXT.encode()),'Lean_calls':0,'old_source_or_object_writes':0,'original_archive_writes':0,'new_formal_credit':0}
with(parts_dir/'TRANSFER_MANIFEST.json').open('x')as f:json.dump(metadata,f,indent=2);f.write('\n')
print('P29_COMPLETE_TRANSFER '+json.dumps(metadata),flush=True)
for p in parts:
 if p['index']in emitted:
  piece=new[p['byte_offset']:p['byte_offset']+p['bytes']]
  print('P29_COMPLETE_XZ9_PART '+json.dumps(p),flush=True)
  print('P29_COMPLETE_XZ9_DATA '+str(p['index'])+' '+base64.b64encode(piece).decode(),flush=True)
