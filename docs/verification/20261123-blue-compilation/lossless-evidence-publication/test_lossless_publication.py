"""Synthetic temporary fixtures only; no publisher main, production data or formal tools."""
import copy,gzip,hashlib,importlib.util,io,json,os,shutil,sys,tempfile,unittest
from pathlib import Path
HERE=Path(__file__).parent
sys.path.insert(0,str(HERE))
spec=importlib.util.spec_from_file_location('isolated_publisher',HERE/'publish_verified_member_batch.candidate.py')
pub=importlib.util.module_from_spec(spec);spec.loader.exec_module(pub)
import restore_lossless_evidence as lib

class LosslessEvidence(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.tmp=tempfile.TemporaryDirectory(prefix='lossless-synthetic-source-');cls.p=Path(cls.tmp.name);cls.source=cls.p/'source';cls.source.mkdir()
  h=hashlib.sha256();size=0;block=b'{"type":"original bytes"}\r\n'*2048
  with (cls.source/'OWNED_EXPORTS.json').open('wb') as f:
   while size<=lib.MIN_BYTES:f.write(block);h.update(block);size+=len(block)
  cls.rec={'path':'OWNED_EXPORTS.json','bytes':size,'sha256':h.hexdigest()};cls.seed=cls.p/'seed'
  row=pub.copy_publication_artifact(cls.source,cls.seed,cls.rec)
  lib.finish_publication(cls.seed,[row],'1'*64,[])
  cls.meta=json.loads((cls.seed/'LOSSLESS_ARTIFACTS.json').read_text())
 @classmethod
 def tearDownClass(cls):cls.tmp.cleanup()
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(prefix='lossless-safety-');self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name);self.bundle=self.root/'bundle';self.bundle.mkdir()
  shutil.copyfile(self.seed/'OWNED_EXPORTS.json.gz',self.bundle/'OWNED_EXPORTS.json.gz');self.m=copy.deepcopy(self.meta);self.save()
 def save(self):(self.bundle/'LOSSLESS_ARTIFACTS.json').write_text(json.dumps(self.m))
 def restore(self,output=None,maximum=None):return lib.restore(self.bundle/'LOSSLESS_ARTIFACTS.json',output or self.root/'restored',max_total_bytes=self.rec['bytes'] if maximum is None else maximum)
 def reject(self,**kw):
  self.save()
  with self.assertRaises((ValueError,OSError,EOFError,gzip.BadGzipFile)):self.restore(**kw)
  self.assertFalse((self.root/'restored'/self.rec['path']).exists())
 def rebind(self):
  size,digest=lib.digest_file(self.bundle/'OWNED_EXPORTS.json.gz');self.m['artifacts'][0]['carrier'].update(bytes=size,sha256=digest)
 def test_exact_roundtrip_preserves_raw_and_reports_actual_paths(self):
  self.assertEqual(self.restore()['restored_files'],1)
  for p in [self.source/self.rec['path'],self.root/'restored'/self.rec['path']]:self.assertEqual(lib.digest_file(p),(self.rec['bytes'],self.rec['sha256']))
  self.assertFalse((self.bundle/self.rec['path']).exists());self.assertTrue(self.m['raw_paths_in_original_manifest_require_restoration'])
 def test_deterministic_carrier_header_and_bytes(self):
  dest=self.root/'second';row=pub.copy_publication_artifact(self.source,dest,self.rec);self.assertEqual(row,self.meta['artifacts'][0])
  b=(self.seed/'OWNED_EXPORTS.json.gz').read_bytes();self.assertEqual(b,(dest/'OWNED_EXPORTS.json.gz').read_bytes());self.assertEqual(b[:8],b'\x1f\x8b\x08\x00\x00\x00\x00\x00')
 def test_small_and_lean_files_remain_exact_regular_copies(self):
  source=self.root/'small';source.mkdir()
  for name,data in [('OWNED_EXPORTS.json',b'{"owned":[]}\r\n'),('candidate.lean',b'theorem x : True := by trivial\n')]:
   with self.subTest(name=name):
    (source/name).write_bytes(data);r={'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()};row=pub.copy_publication_artifact(source,self.root/'small-copy',r)
    self.assertEqual(row,{'raw':r,'repository':r});self.assertEqual((self.root/'small-copy'/name).read_bytes(),data);self.assertFalse((self.root/'small-copy'/(name+'.gz')).exists())
 def test_only_three_exact_basenames_above_strict_threshold(self):
  for name in lib.NAMES:self.assertTrue(lib.is_large_evidence(dict(self.rec,path='M/'+name)));self.assertFalse(lib.is_large_evidence(dict(self.rec,path=name,bytes=lib.MIN_BYTES)))
  for name in ['candidate.lean','PUBLICATION_FILES.json','normal.log','kernel.log','xOWNED_EXPORTS.json','OWNED_EXPORTS.json.backup','types-axioms.log.olean']:
   with self.subTest(name=name):
    self.assertFalse(lib.is_large_evidence(dict(self.rec,path=name)))
    with self.assertRaises(ValueError):lib.create_carrier(self.source,self.root/'unsupported',dict(self.rec,path=name))
 def test_compressed_sha_mismatch(self):self.m['artifacts'][0]['carrier']['sha256']='0'*64;self.reject()
 def test_compressed_size_mismatch(self):self.m['artifacts'][0]['carrier']['bytes']+=1;self.reject()
 def test_crc_corrupt_even_with_compressed_hash_rebound(self):
  p=self.bundle/'OWNED_EXPORTS.json.gz';b=bytearray(p.read_bytes());b[-8]^=1;p.write_bytes(b);self.rebind();self.reject()
 def test_truncated_gzip_even_with_compressed_hash_rebound(self):
  p=self.bundle/'OWNED_EXPORTS.json.gz';p.write_bytes(p.read_bytes()[:-10]);self.rebind();self.reject()
 def test_wrong_raw_sha(self):self.m['artifacts'][0]['raw']['sha256']='0'*64;self.reject()
 def test_expansion_past_exact_expected_bytes(self):self.m['artifacts'][0]['raw']['bytes']-=1;self.reject()
 def test_configured_total_limit_precedes_output_creation(self):self.reject(maximum=self.rec['bytes']-1);self.assertFalse((self.root/'restored').exists())
 def test_raw_parent_traversal(self):
  r=self.m['artifacts'][0];r['raw']['path']='../OWNED_EXPORTS.json';r['carrier']['path']=r['raw']['path']+'.gz';self.reject()
 def test_absolute_raw_path(self):
  r=self.m['artifacts'][0];r['raw']['path']=str(self.root/'OWNED_EXPORTS.json');r['carrier']['path']=r['raw']['path']+'.gz';self.reject()
 def test_noncanonical_and_windows_escape_paths(self):
  for p in ['M\\OWNED_EXPORTS.json','M//OWNED_EXPORTS.json','./OWNED_EXPORTS.json']:
   with self.assertRaises(ValueError):lib.is_large_evidence(dict(self.rec,path=p))
 def test_carrier_path_escape(self):self.m['artifacts'][0]['carrier']['path']='../OWNED_EXPORTS.json.gz';self.reject()
 def test_carrier_file_symlink(self):
  p=self.bundle/'OWNED_EXPORTS.json.gz';target=self.root/'outside.gz';p.rename(target);before=target.read_bytes();p.symlink_to(target);self.reject();self.assertEqual(before,target.read_bytes())
 def test_carrier_parent_symlink(self):
  (self.bundle/'link').symlink_to(self.bundle,target_is_directory=True);r=self.m['artifacts'][0];r['raw']['path']='link/OWNED_EXPORTS.json';r['carrier']['path']=r['raw']['path']+'.gz';self.reject()
 def test_existing_output_file_not_clobbered(self):
  output=self.root/'existing';output.mkdir();p=output/self.rec['path'];p.write_bytes(b'keep');self.reject(output=output);self.assertEqual(p.read_bytes(),b'keep')
 def test_symlink_output_directory(self):
  target=self.root/'outside';target.mkdir();p=self.root/'output-link';p.symlink_to(target,target_is_directory=True);self.reject(output=p);self.assertEqual(list(target.iterdir()),[])
 def test_symlink_output_parent(self):
  target=self.root/'outside';target.mkdir();p=self.root/'parent-link';p.symlink_to(target,target_is_directory=True);self.reject(output=p/'new');self.assertEqual(list(target.iterdir()),[])
 def test_nondeterministic_header_rejected(self):
  p=self.bundle/'OWNED_EXPORTS.json.gz';b=bytearray(p.read_bytes());b[4]=1;p.write_bytes(b);self.rebind();self.reject()
 def test_duplicate_restored_path(self):self.m['artifacts'].append(copy.deepcopy(self.m['artifacts'][0]));self.reject(maximum=self.rec['bytes']*2)
 def test_unsupported_restored_source_name(self):
  r=self.m['artifacts'][0];r['raw']['path']='candidate.lean';r['carrier']['path']='candidate.lean.gz';self.reject()
 def test_wrong_raw_source_never_leaves_carrier(self):
  with self.assertRaises(ValueError):pub.copy_publication_artifact(self.source,self.root/'bad',dict(self.rec,sha256='0'*64))
  self.assertFalse((self.root/'bad/OWNED_EXPORTS.json.gz').exists());self.assertEqual(list((self.root/'bad').glob('.lossless-*')),[])
 def test_raw_source_symlink(self):
  source=self.root/'link-source';source.mkdir();(source/self.rec['path']).symlink_to(self.source/self.rec['path'])
  with self.assertRaises(OSError):pub.copy_publication_artifact(source,self.root/'bad',self.rec)
  self.assertFalse((self.root/'bad/OWNED_EXPORTS.json.gz').exists())
 def test_carrier_destination_parent_symlink(self):
  target=self.root/'outside';target.mkdir();p=self.root/'dest-link';p.symlink_to(target,target_is_directory=True)
  with self.assertRaises(OSError):pub.copy_publication_artifact(self.source,p/'new',self.rec)
  self.assertEqual(list(target.iterdir()),[])
 def test_existing_raw_destination_is_not_removed(self):
  dest=self.root/'raw-exists';dest.mkdir();os.link(self.source/self.rec['path'],dest/self.rec['path'])
  with self.assertRaises(ValueError):pub.copy_publication_artifact(self.source,dest,self.rec)
  self.assertEqual(lib.digest_file(dest/self.rec['path']),(self.rec['bytes'],self.rec['sha256']))
 def test_existing_identical_carrier_is_not_rewritten(self):
  p=self.bundle/'OWNED_EXPORTS.json.gz';before=p.stat();row=pub.copy_publication_artifact(self.source,self.bundle,self.rec);after=p.stat()
  self.assertEqual((before.st_ino,before.st_mtime_ns),(after.st_ino,after.st_mtime_ns));self.assertEqual(row,self.m['artifacts'][0])
 def test_carrier_and_metadata_collision_preflight(self):
  for name in ['OWNED_EXPORTS.json.gz','LOSSLESS_ARTIFACTS.json','restore_lossless_evidence.py']:
   with self.assertRaises(ValueError):pub.preflight_publication_carriers(self.source,self.root/'new',[self.rec,{'path':name,'bytes':0,'sha256':hashlib.sha256(b'').hexdigest()}])
 def test_original_raw_hash_gate_stays_strict(self):
  with self.assertRaises(ValueError):pub.prepare_publication_files(self.source,{'files':[dict(self.rec,sha256='0'*64)]},{'status':'PASS_','findings':[]})
 def test_stream_read_size_limit(self):
  with self.assertRaises(ValueError):lib.digest_stream(io.BytesIO(b'1234'),max_bytes=3)
 def test_carrier_fifo_is_rejected_without_blocking(self):
  p=self.bundle/'OWNED_EXPORTS.json.gz';p.unlink();os.mkfifo(p)
  self.reject()
 def test_mapping_metadata_size_limit(self):
  (self.bundle/'LOSSLESS_ARTIFACTS.json').write_bytes(b' '*(lib.MAX_MANIFEST_BYTES+1))
  with self.assertRaises(ValueError):self.restore()
  self.assertFalse((self.root/'restored').exists())

if __name__=='__main__':unittest.main()
