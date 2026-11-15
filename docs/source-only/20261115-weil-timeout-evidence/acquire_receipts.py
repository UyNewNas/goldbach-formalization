"""Read-only bounded evidence acquisition; never compiles or promotes reuse."""
import os,json,urllib.request,urllib.error,io,zipfile,hashlib,pathlib,resource
resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
REPO='UyNewNas/goldbach-formalization';RUN=43733580621;HEAD='b641b1f45475161ffef0a2225dced502071ff0eb'
ANCHORS=[(14175843899,2459824201,'25284ae68e6183f27f631037499fba69e7e01ad0ac4eddde3b85499db665d4e6'),(14175749285,1892998503,'880974d14f0774eff76e6e25bf8f91d8d3fe082880cc982a4e03bfc6e4363628')]
OUT=pathlib.Path(os.environ['OUT']);OUT.mkdir(parents=True,exist_ok=False)
def api(path):
 req=urllib.request.Request('https://api.github.com/repos/'+REPO+'/'+path,headers={'Authorization':'Bearer '+os.environ['GH_TOKEN'],'Accept':'application/vnd.github+json'})
 with urllib.request.build_opener(NoRedirect).open(req,timeout=60) as response:
  body=response.read(8*1024**2+1);assert len(body)<=8*1024**2
 return json.loads(body)
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**k):return None
def signed(a):
 req=urllib.request.Request('https://api.github.com/repos/'+REPO+'/actions/artifacts/'+str(a)+'/zip',headers={'Authorization':'Bearer '+os.environ['GH_TOKEN']})
 try:urllib.request.build_opener(NoRedirect).open(req,timeout=60)
 except urllib.error.HTTPError as e:
  if e.code not in (301,302,303,307,308):raise
  url=e.headers['Location'];assert url.startswith('https://');return url
 raise RuntimeError('Expected artifact redirect')
BUDGET={'range_bytes':0,'extracted_bytes':0}
class Ranges(io.RawIOBase):
 def __init__(self,url,size):self.url=url;self.size=size;self.pos=0;self.used=0;self.receipts=[]
 def seekable(self):return True
 def readable(self):return True
 def tell(self):return self.pos
 def seek(self,n,whence=0):
  self.pos=n if whence==0 else self.pos+n if whence==1 else self.size+n
  if not 0<=self.pos<=self.size:raise ValueError('range position')
  return self.pos
 def read(self,n=-1):
  if n<0:n=self.size-self.pos
  n=min(n,self.size-self.pos)
  if n==0:return b''
  if n>32*1024**2 or BUDGET['range_bytes']+n>192*1024**2:raise ValueError('bounded acquisition limit')
  start=self.pos;req=urllib.request.Request(self.url,headers={'Range':f'bytes={start}-{start+n-1}'})
  with urllib.request.urlopen(req,timeout=120) as r:
   assert r.status==206 and r.headers['Content-Range']==f'bytes {start}-{start+n-1}/{self.size}'
   b=r.read(n+1)
  assert len(b)==n;self.pos+=n;self.used+=n;BUDGET['range_bytes']+=n;self.receipts.append({'offset':start,'bytes':n,'sha256':hashlib.sha256(b).hexdigest()});return b
run=api('actions/runs/'+str(RUN));assert run['status']=='completed' and run['head_sha']==HEAD
(OUT/'producer.json').write_text(json.dumps(run,indent=2))
report=[]
for aid,size,digest in ANCHORS:
 meta=api('actions/artifacts/'+str(aid));assert meta['id']==aid and not meta['expired'] and meta['size_in_bytes']==size and meta['digest']=='sha256:'+digest
 assert meta['workflow_run']['id']==RUN and meta['workflow_run']['head_sha']==HEAD
 folder=OUT/str(aid);folder.mkdir();(folder/'metadata.json').write_text(json.dumps(meta,indent=2));reader=Ranges(signed(aid),size)
 z=zipfile.ZipFile(reader);infos=z.infolist();assert len({i.filename for i in infos})==len(infos)
 (folder/'members.json').write_text(json.dumps([{'name':i.filename,'bytes':i.file_size,'compressed':i.compress_size,'crc':i.CRC,'offset':i.header_offset} for i in infos],indent=2))
 selected=[];total=0
 for i in sorted(infos,key=lambda x:(not any(t in x.filename.lower() for t in ['checkpoint','manifest','raw_capture','retention','runtime','collector']),x.filename)):
  if i.is_dir() or not i.filename.endswith(('.json','.jsonl','.log','.stdout','.stderr')):continue
  if i.file_size>32*1024**2 or BUDGET['extracted_bytes']+i.file_size>128*1024**2:continue
  b=z.read(i);assert len(b)==i.file_size;total+=len(b);BUDGET['extracted_bytes']+=len(b);name=hashlib.sha256(i.filename.encode()).hexdigest()+'.data';(folder/name).write_bytes(b)
  selected.append({'member':i.filename,'local':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 (folder/'selected.json').write_text(json.dumps(selected,indent=2));(folder/'ranges.json').write_text(json.dumps(reader.receipts,indent=2));report.append({'artifact':aid,'metadata_digest':digest,'whole_digest_recomputed':False,'range_bytes':reader.used,'selected_bytes':total,'members':len(infos),'selected':len(selected)})
(OUT/'RESULT.json').write_text(json.dumps({'status':'RAW_EVIDENCE_ONLY_NOT_REUSE_OR_PROOF_ACCEPTANCE','artifacts':report,'compiler_events':0,'global_budget_used':BUDGET,'checkpoint_classifications_modified':False},indent=2))
