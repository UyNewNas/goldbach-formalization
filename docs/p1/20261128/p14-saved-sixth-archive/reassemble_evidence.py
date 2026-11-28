"""Reassemble the exact sealed ZIP from its Git-stored transport parts. No Lean runs."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,tempfile,zipfile
if not __debug__:
 raise SystemExit('Integrity checks require Python without -O/PYTHONOPTIMIZE')

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--repository',type=Path,default=Path.cwd());parser.add_argument('--revision',default='HEAD');parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
 spec=json.loads(Path(__file__).with_name('GITHUB_PARTS.json').read_text());master=spec['master'];output=args.output
 if output.exists():
  assert output.is_file() and output.stat().st_size==master['bytes'] and hashlib.file_digest(output.open('rb'),'sha256').hexdigest()==master['sha256'],'existing output differs; refusing overwrite'
  print('ALREADY_PRESENT',output);return
 output.parent.mkdir(parents=True,exist_ok=True)
 handle=tempfile.NamedTemporaryFile(prefix='.p1-evidence-',suffix='.tmp',dir=output.parent,delete=False);tmp=Path(handle.name);whole=hashlib.sha256();total=0
 try:
  with handle:
   for part in spec['parts']:
    assert part['offset']==total
    process=subprocess.Popen(['git','-C',str(args.repository),'show',args.revision+':'+spec['git_directory']+'/'+part['file']],stdout=subprocess.PIPE)
    digest=hashlib.sha256();size=0
    try:
     while True:
      data=process.stdout.read(1024*1024)
      if not data:break
      size+=len(data);assert size<=part['bytes'];digest.update(data);whole.update(data);handle.write(data)
    finally:
     process.stdout.close()
     if size>part['bytes'] and process.poll() is None:process.terminate()
     returncode=process.wait()
    assert returncode==0
    assert size==part['bytes'] and digest.hexdigest()==part['sha256'];total+=size
  assert total==master['bytes'] and whole.hexdigest()==master['sha256']
  with zipfile.ZipFile(tmp) as archive:
   bad_member=archive.testzip()
   assert bad_member is None
  # Atomic no-clobber publication on the output directory's own filesystem.
  os.link(tmp,output);tmp.unlink();print('PASS_REASSEMBLED',output,total,whole.hexdigest())
 finally:
  if tmp.exists():tmp.unlink()
if __name__=='__main__':main()
