"""Exact AST definitions copied from the reviewed R3 shared reader only.
No CacheSession, compiler, guard, phase, setup or proof code is imported.
"""
import hashlib
import json
import os
from pathlib import Path
import struct
import threading
import urllib.error
import urllib.request
import zlib

def require(ok, text):
    if not ok: raise ValueError(text)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl): return None


class ArchiveReader:
    def __init__(self, anchor):
        self.anchor=anchor; self.token=os.environ['GH_TOKEN']
        self.api='https://api.github.com/repos/'+os.environ['GITHUB_REPOSITORY']+'/actions/artifacts/'+str(anchor['artifact'])
        with self.request(self.api) as response:metadata=json.load(response)
        require(metadata['id']==anchor['artifact'] and not metadata['expired'] and metadata['size_in_bytes']==anchor['artifactBytes']
                and metadata['digest']=='sha256:'+anchor['githubWholeArtifactDigest']
                and metadata['workflow_run']['id']==anchor['run'], 'Historical GitHub artifact identity changed')
        self.metadata=metadata;self.redirect_lock=threading.Lock();self.refresh_redirect()

    def refresh_redirect(self):
        request=urllib.request.Request(self.api+'/zip',headers=self.headers())
        try: urllib.request.build_opener(NoRedirect()).open(request,timeout=60)
        except urllib.error.HTTPError as error:
            require(error.code==302 and error.headers.get('Location','').startswith('https://'),'No authenticated artifact redirect')
            self.url=error.headers['Location']
        else: raise ValueError('Expected a redirect; never stream a whole archive accidentally')

    def headers(self): return {'Authorization':'Bearer '+self.token,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'}
    def request(self,url): return urllib.request.urlopen(urllib.request.Request(url,headers=self.headers()),timeout=60)

    def part(self,start,size):
        end=start+size-1
        previous=self.url
        request=urllib.request.Request(previous,headers={'Range':f'bytes={start}-{end}'})
        try:response=urllib.request.urlopen(request,timeout=120)
        except urllib.error.HTTPError as error:
            require(error.code in {401,403},'Artifact range request failed; no unbounded fallback')
            # GitHub redirects expire after roughly ten minutes. Renew only the
            # same immutable artifact URL, then retry this exact failed range.
            # Concurrent readers reuse the first worker's renewed redirect.
            with self.redirect_lock:
                if self.url==previous:self.refresh_redirect()
            response=urllib.request.urlopen(urllib.request.Request(self.url,headers={'Range':f'bytes={start}-{end}'}),timeout=120)
        with response:
            require(response.status==206 and response.headers.get('Content-Range')==f'bytes {start}-{end}/{self.anchor["artifactBytes"]}',
                    'Exact bounded HTTP range required; no whole-archive fallback')
            data=response.read(size+1);require(len(data)==size,'Wrong range length');return data

    def fetch(self,name,row,destination):
        e=row['zip']; head=self.part(e['h'],30)
        signature,version,flags,method,mtime,mdate,crc,compressed,plain,nlen,xlen=struct.unpack('<IHHHHHIIIHH',head)
        require(signature==0x04034b50 and method==e['c']==0 and not flags&1,'Unsupported/encrypted ZIP member')
        actual=self.part(e['h']+30,nlen+xlen)
        require(actual[:nlen].decode()==name and e['s']==e['z']==row['bytes'],'Wrong ZIP member name/size')
        if not flags&8: require((crc,compressed,plain)==(e['crc'],e['z'],e['s']),'Local/central member disagreement')
        target=destination/name;require(target.resolve().is_relative_to(destination.resolve()),'Unsafe member path')
        target.parent.mkdir(parents=True,exist_ok=True);require(not target.exists(),'Existing cache payload')
        pos=e['h']+30+nlen+xlen;remaining=row['bytes'];check=hashlib.sha256();crc_actual=0
        with target.open('xb') as output:
            while remaining:
                data=self.part(pos,min(8*1024*1024,remaining));output.write(data);check.update(data);crc_actual=zlib.crc32(data,crc_actual)
                remaining-=len(data);pos+=len(data)
        require(check.hexdigest()==row['sha256'] and crc_actual==e['crc'],'Payload SHA/CRC changed')
        return {'member':name,'bytes':row['bytes'],'sha256':row['sha256']}
