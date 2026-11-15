"""Finite original R3 data export only. No compiler, toolchain, or object loader.

Imports only stdlib and exact extracted metadata-reader definitions. Never
executes the historical shared engine, collector, fixture, guard or proof code.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import struct
import sys
import urllib.error
import urllib.parse
import urllib.request
import zlib

from original_archive_reader import ArchiveReader, NoRedirect, require

REPO='UyNewNas/goldbach-formalization'
HEAD='2960e200301de4189c1c2793b918fc8aa7666930'
PRODUCER_RUN=43657752592
BRANCH='refs/heads/ci/weil-r3-evidence-20261115'
MIB=1024*1024
CHUNK=4*MIB
TOTAL=160*MIB
ANCHORS={14141463081:(2232962772,'b9b8f4ffc0a5b8a3b2d4de94c0b374f349cff9349af1b0f01db07d302546f497'),
         14141522967:(1708124564,'19f758a2991cf96e6aa88dd65ef0ceae2f9071549923f77e4634cab4460585ae')}
HERE=Path(__file__).resolve().parent


class Hold(Exception):
    """Contains only a static safe code, never a transport URL or token."""


def check(condition,code):
    if not condition: raise Hold(code)


def digest(data): return hashlib.sha256(data).hexdigest()
def canonical(value): return digest(json.dumps(value,sort_keys=True).encode())
def load(path): return json.loads(Path(path).read_text(encoding='utf-8'))


def receipt_header(value,kind):
    normal=(kind=='length' and re.fullmatch('[0-9]{1,20}',value) is not None
        or kind=='range' and re.fullmatch('bytes [0-9]{1,20}-[0-9]{1,20}/[0-9]{1,20}',value) is not None
        or kind=='encoding' and value in {'identity','gzip','deflate','br','zstd'})
    return value if normal or value=='' else dict(invalid_header_value_sha256=digest(value.encode()))


def write_bytes(path,raw):
    path=Path(path); path.parent.mkdir(parents=True,exist_ok=True)
    check(not path.is_symlink() and not path.exists(),'REFUSE_OUTPUT_OVERWRITE')
    with path.open('xb') as output: output.write(raw)
    return dict(path=path.as_posix(),bytes=len(raw),sha256=digest(raw))


def write_json(path,value):
    return write_bytes(path,(json.dumps(value,indent=2)+'\n').encode())


class Journal:
    def __init__(self,output):
        self.output=output; self.total_network_bytes=0; self.uncompressed_bytes=0
        self.reserved_network_bytes=0
        self.sequence=0; self.saved={}; self.records=[]; self.failures=[]
        self.complete_selection=False
        self.proposed_name_inventory=[]
        self.path=output/'GET_BOUNDARIES.jsonl'
        with self.path.open('xb'): pass

    def event(self,value):
        with self.path.open('ab') as stream: stream.write((json.dumps(value,sort_keys=True)+'\n').encode())

    def start(self,artifact,kind,expected_bytes=None,start=None):
        self.sequence+=1
        row=dict(get=self.sequence,artifact=artifact,operation=kind,
                 expected_body_bytes=expected_bytes,range_start=start,
                 token_or_signed_URL_recorded=False)
        self.event(dict(row,state='REQUEST_STARTED')); return row

    def preflight_network(self,size):
        check(isinstance(size,int) and size>=0 and self.reserved_network_bytes+size<=TOTAL,'TOTAL_NETWORK_CAP_HOLD')

    def reserve_network(self,size):
        # A failed read may have consumed bytes not returned by the HTTP stack.
        # Never refund this upper bound, so partial/error paths cannot evade cap.
        self.preflight_network(size); self.reserved_network_bytes+=size

    def body(self,row,raw):
        self.total_network_bytes+=len(raw)
        check(self.total_network_bytes<=self.reserved_network_bytes<=TOTAL,'NETWORK_ACCOUNTING_CHANGED')
        self.event(dict(row,state='BODY_ACQUIRED',body_bytes=len(raw),body_sha256=digest(raw),
                        cumulative_network_bytes=self.total_network_bytes))

    def preflight_uncompressed(self,size):
        check(isinstance(size,int) and size>=0 and self.uncompressed_bytes+size<=TOTAL,'TOTAL_UNCOMPRESSED_CAP_HOLD')

    def failure(self,code,**scope):
        row=dict(code=code,**scope); self.failures.append(row)
        self.event(dict(state='HOLD',body_bytes_at_this_event=0,**row))


class MetadataResponse:
    """Bounded adapter for the original ArchiveReader.__init__ json.load call."""
    def __init__(self,response,size,reader,event):
        self.response=response; self.size=size; self.reader=reader; self.event=event; self.used=False
    def __enter__(self): return self
    def __exit__(self,*unused): self.response.close()
    def read(self,*unused):
        check(not self.used,'API_METADATA_SECOND_READ_DENIED'); self.used=True
        limit=self.size if self.size is not None else MIB+1
        self.reader.journal.reserve_network(limit)
        try: raw=self.response.read(limit)
        except Exception as error:
            partial=getattr(error,'partial',b'')
            if isinstance(partial,bytes) and partial:
                check(len(partial)<=limit,'API_EXCEPTION_PARTIAL_OVER_CAP')
                self.reader.journal.body(self.event,partial)
                write_bytes(self.reader.journal.output/'quarantine'/('api-get-'+str(self.event['get'])+'.bin'),partial)
            raise Hold('API_METADATA_READ_FAILED_UPPER_BOUND_RESERVED') from None
        self.reader.journal.body(self.event,raw)
        write_bytes(self.reader.journal.output/'api'/(str(self.reader.anchor['artifact'])+'.json'),raw)
        check((self.size is None and len(raw)<=MIB) or len(raw)==self.size,'API_METADATA_LENGTH_CHANGED')
        return raw


class StrictArchiveReader(ArchiveReader):
    """Same original reader; tighter pre-body transport and explicit receipts.

    Known-SHA payloads use the inherited exact original fetch implementation.
    Its logical8MiB request is split into <=4MiB HTTP ranges by this part method.
    No full archive GET is available; the authenticated /zip GET consumes no body.
    """
    def __init__(self,anchor,journal):
        self.journal=journal
        check(anchor['artifact'] in ANCHORS,'UNAPPROVED_ARTIFACT')
        total,sha=ANCHORS[anchor['artifact']]
        check(anchor['artifactBytes']==total and anchor['githubWholeArtifactDigest']==sha
              and anchor['run']==PRODUCER_RUN and anchor['head_sha']==HEAD,'ANCHOR_CHANGED')
        super().__init__(anchor)
        check(self.metadata['workflow_run']['head_sha']==HEAD
              and self.metadata['workflow_run']['head_branch']=='ci/weil34-26a6-20261115',
              'OFFICIAL_PRODUCER_HEAD_OR_BRANCH_CHANGED')

    def request(self,url):
        check(url==self.api and url==f'https://api.github.com/repos/{REPO}/actions/artifacts/{self.anchor["artifact"]}',
              'METADATA_API_ORIGIN_CHANGED')
        event=self.journal.start(self.anchor['artifact'],'OFFICIAL_API_METADATA')
        try:
            response=urllib.request.build_opener(NoRedirect()).open(
                urllib.request.Request(url,headers=dict(self.headers(),**{'Accept-Encoding':'identity'})),timeout=60)
        except Exception as error:
            self.journal.event(dict(event,state='NO_HEADERS_NETWORK_FAILURE',body_bytes=0,error_type=type(error).__name__))
            raise Hold('OFFICIAL_METADATA_TRANSPORT_HOLD') from None
        length=response.headers.get('Content-Length','')
        self.journal.event(dict(event,state='HEADERS_BEFORE_BODY',status=response.status,
            content_length=receipt_header(length,'length'),
            content_encoding=receipt_header(response.headers.get('Content-Encoding','identity'),'encoding'),body_bytes=0))
        try:
            check(response.status==200 and (length=='' or length.isdigit() and int(length)<=MIB)
                  and response.headers.get('Content-Encoding','identity').lower()=='identity',
                  'OFFICIAL_METADATA_HEADERS_REJECTED_BEFORE_BODY')
            self.journal.preflight_network(int(length) if length else MIB+1)
        except Exception:
            response.close(); raise
        return MetadataResponse(response,int(length) if length else None,self,event)

    def refresh_redirect(self):
        event=self.journal.start(self.anchor['artifact'],'AUTHENTICATED_ZIP_REDIRECT_NO_BODY',0)
        try:
            response=urllib.request.build_opener(NoRedirect()).open(
                urllib.request.Request(self.api+'/zip',headers=self.headers()),timeout=60)
        except urllib.error.HTTPError as error:
            status=error.code; location=error.headers.get('Location',''); error.close()
            self.journal.event(dict(event,state='HEADERS_NO_BODY',status=status,body_bytes=0))
            parsed=urllib.parse.urlsplit(location)
            check(status==302 and parsed.scheme=='https' and bool(parsed.netloc)
                  and parsed.username is None and parsed.password is None and not parsed.fragment,
                  'AUTHENTICATED_REDIRECT_REJECTED_NO_BODY')
            self.url=location
        except Exception as error:
            self.journal.event(dict(event,state='NO_HEADERS_NETWORK_FAILURE',body_bytes=0,error_type=type(error).__name__))
            raise Hold('REDIRECT_TRANSPORT_HOLD') from None
        else:
            status=response.status; response.close()
            self.journal.event(dict(event,state='NON_REDIRECT_NO_BODY',status=status,body_bytes=0))
            raise Hold('NON_REDIRECT_WHOLE_BODY_NOT_READ')

    def part(self,start,size):
        total=self.anchor['artifactBytes']
        check(type(start) is int and type(size) is int and start>=0 and size>0 and start+size<=total,
              'RANGE_BOUNDS_REJECTED')
        self.journal.preflight_network(size)
        pieces=[]
        try:
            for offset in range(start,start+size,CHUNK):
                pieces.append(self.one_range(offset,min(CHUNK,start+size-offset)))
        except Exception:
            if pieces:
                write_bytes(self.journal.output/'quarantine'/str(self.anchor['artifact'])/
                    ('part-'+str(start)+'-through-get-'+str(self.journal.sequence)+'.bin'),b''.join(pieces))
            raise
        return b''.join(pieces)

    def one_range(self,start,size):
        check(0<size<=CHUNK,'HTTP_CHUNK_OVER4MIB')
        end=start+size-1; event=self.journal.start(self.anchor['artifact'],'EXACT_RANGE',size,start)
        self.journal.preflight_network(size)
        opener=urllib.request.build_opener(NoRedirect())
        for attempt in range(2):
            try:
                response=opener.open(urllib.request.Request(self.url,headers={
                    'Range':f'bytes={start}-{end}','Accept-Encoding':'identity'}),timeout=120)
                break
            except urllib.error.HTTPError as error:
                status=error.code; error.close()
                self.journal.event(dict(event,state='HTTP_ERROR_NO_BODY',status=status,attempt=attempt,body_bytes=0))
                if attempt==0 and status in {401,403}:
                    self.refresh_redirect(); continue
                raise Hold('EXACT_RANGE_HTTP_HOLD_NO_FALLBACK') from None
            except Exception as error:
                self.journal.event(dict(event,state='NO_HEADERS_NETWORK_FAILURE',body_bytes=0,error_type=type(error).__name__))
                raise Hold('EXACT_RANGE_NETWORK_HOLD_NO_FALLBACK') from None
        with response:
            length=response.headers.get('Content-Length','')
            content_range=response.headers.get('Content-Range','')
            encoding=response.headers.get('Content-Encoding','identity').lower()
            self.journal.event(dict(event,state='HEADERS_BEFORE_BODY',status=response.status,
                content_range=receipt_header(content_range,'range'),content_length=receipt_header(length,'length'),
                content_encoding=receipt_header(encoding,'encoding'),body_bytes=0))
            check(response.status==206 and content_range==f'bytes {start}-{end}/{self.anchor["artifactBytes"]}'
                  and length==str(size) and encoding=='identity','EXACT206_IDENTITY_HEADERS_REJECTED_BEFORE_BODY')
            self.journal.reserve_network(size)
            try: raw=response.read(size)
            except Exception as error:
                partial=getattr(error,'partial',b'')
                if isinstance(partial,bytes) and partial:
                    check(len(partial)<=size,'RANGE_EXCEPTION_PARTIAL_OVER_CAP')
                    self.journal.body(event,partial)
                    write_bytes(self.journal.output/'quarantine'/str(self.anchor['artifact'])/
                        ('get-'+str(event['get'])+'.bin'),partial)
                self.journal.event(dict(event,state='BODY_READ_FAILED_UPPER_BOUND_RESERVED',body_maximum_bytes=size,
                                        error_type=type(error).__name__))
                raise Hold('EXACT_RANGE_READ_FAILED_UPPER_BOUND_RESERVED') from None
            self.journal.body(event,raw)
            if len(raw)!=size:
                write_bytes(self.journal.output/'quarantine'/str(self.anchor['artifact'])/
                    ('get-'+str(event['get'])+'.bin'),raw)
                raise Hold('EXACT_RANGE_LENGTH_CHANGED')
            return raw


def safe_member(name):
    check(isinstance(name,str) and name and '\0' not in name and '\\' not in name,'UNSAFE_ZIP_MEMBER')
    path=PurePosixPath(name)
    check(not path.is_absolute() and '..' not in path.parts and ':' not in name
          and name.lstrip('/')==name and not name.startswith('./'),'UNSAFE_ZIP_PATH')


def zip64_values(extra,plain,compressed,offset,disk):
    position=0; item=None
    while position<len(extra):
        check(position+4<=len(extra),'MALFORMED_CENTRAL_EXTRA')
        tag,size=struct.unpack_from('<HH',extra,position); position+=4
        check(position+size<=len(extra),'TRUNCATED_CENTRAL_EXTRA')
        if tag==1:
            check(item is None,'DUPLICATE_ZIP64_EXTRA'); item=extra[position:position+size]
        position+=size
    values=[plain,compressed,offset,disk]; cursor=0
    for index,width in [(0,8),(1,8),(2,8),(3,4)]:
        sentinel=0xffff if index==3 else 0xffffffff
        if values[index]==sentinel:
            check(item is not None and cursor+width<=len(item),'MISSING_ZIP64_CENTRAL_VALUE')
            values[index]=int.from_bytes(item[cursor:cursor+width],'little'); cursor+=width
    return values


def directory(reader,journal):
    artifact=reader.anchor['artifact']; total=reader.anchor['artifactBytes']
    size=min(total,65557); tail=reader.part(total-size,size)
    root=journal.output/'metadata'/str(artifact)
    write_bytes(root/'EOCD_TAIL.bin',tail)
    position=tail.rfind(b'PK\x05\x06')
    check(position>=0 and position+22<=len(tail),'EOCD_NOT_FOUND')
    fields=struct.unpack_from('<IHHHHIIH',tail,position)
    signature,disk,central_disk,disk_entries,entries,central_size,central_offset,comment=fields
    check(position+22+comment==len(tail) and disk==central_disk==0 and disk_entries==entries,'EOCD_MULTIDISK_OR_TRAILING_BYTES')
    eocd_offset=total-size+position; boundary=eocd_offset
    write_bytes(root/'EOCD.bin',tail[position:])
    if entries==0xffff or central_size==0xffffffff or central_offset==0xffffffff:
        check(eocd_offset>=20,'ZIP64_LOCATOR_MISSING')
        locator=reader.part(eocd_offset-20,20)
        sig,locator_disk,record_offset,disks=struct.unpack('<IIQI',locator)
        check(sig==0x07064b50 and locator_disk==0 and disks==1,'ZIP64_LOCATOR_CHANGED')
        first=reader.part(record_offset,56)
        sig,record_size,made,needed,disk,central_disk,disk_entries,entries,central_size,central_offset=struct.unpack('<IQHHIIQQQQ',first)
        check(sig==0x06064b50 and 44<=record_size<=65524 and disk==central_disk==0 and disk_entries==entries,'ZIP64_EOCD_REJECTED')
        check(record_offset+12+record_size==eocd_offset-20,'ZIP64_EOCD_BOUNDARY_CHANGED')
        record=first if record_size==44 else reader.part(record_offset,12+record_size)
        write_bytes(root/'ZIP64_LOCATOR.bin',locator); write_bytes(root/'ZIP64_EOCD.bin',record)
        boundary=record_offset
    check(0<central_size<=16*MIB and central_offset>=0 and central_offset+central_size<=boundary,
          'CENTRAL_DIRECTORY_BOUNDS_OR_CAP_HOLD')
    central=reader.part(central_offset,central_size)
    write_bytes(root/'CENTRAL_DIRECTORY.bin',central)
    result={}; position=0
    while position<len(central):
        check(position+46<=len(central),'TRUNCATED_CENTRAL_HEADER')
        item=struct.unpack_from('<IHHHHHHIIIHHHHHII',central,position)
        sig,made,needed,flags,method,mtime,mdate,crc,compressed,plain,nlen,xlen,clen,disk,internal,external,offset=item
        check(sig==0x02014b50 and position+46+nlen+xlen+clen<=len(central),'CENTRAL_HEADER_CHANGED')
        raw_name=central[position+46:position+46+nlen]
        try: name=raw_name.decode('utf-8' if flags&0x800 else 'cp437')
        except UnicodeError: raise Hold('UNDECODABLE_ZIP_NAME') from None
        safe_member(name)
        mode=external>>16
        check(not stat.S_ISLNK(mode) and (stat.S_IFMT(mode) in {0,stat.S_IFREG,stat.S_IFDIR}),
              'ZIP_SYMLINK_OR_NONREGULAR_MEMBER_DENIED')
        extra=central[position+46+nlen:position+46+nlen+xlen]
        plain,compressed,offset,disk=zip64_values(extra,plain,compressed,offset,disk)
        check(disk==0 and name not in result and offset<central_offset,'DUPLICATE_OR_MULTIDISK_ZIP_MEMBER')
        result[name]=dict(member=name,bytes=plain,flags=flags,mode=mode,is_directory=name.endswith('/'),
            zip=dict(h=offset,c=method,crc=crc,z=compressed,s=plain),central_offset=central_offset)
        position+=46+nlen+xlen+clen
    check(len(result)==entries,'CENTRAL_ENTRY_CENSUS_CHANGED')
    write_json(root/'CANDIDATE_INVENTORY.json',dict(artifact=artifact,entries=list(result.values()),
        official_origin_metadata_only=True,whole_archive_digest_recomputed=False,
        central_directory_sha256=digest(central),central_directory_bytes=len(central),
        payloads_not_automatically_selected=True,root_local_physical_availability='UNKNOWN'))
    return result


def selected_entry(inventory,name):
    check(name in inventory,'EXACT_MEMBER_MISSING_NO_ALIAS')
    row=inventory[name]; safe_member(name)
    check(not row['is_directory'] and row['zip']['c']==0 and not row['flags']&1,
          'ONLY_ORIGINAL_REVIEWED_STORED_MEMBER_READER_PERMITTED')
    check(row['zip']['z']==row['bytes'] and row['zip']['h']+30+row['bytes']<=row['central_offset'],
          'SELECTED_STORED_MEMBER_BOUNDS_CHANGED')
    check(not name.lower().endswith(('.tar','.tar.gz','.tgz','.zip')),'NESTED_TAR_OR_CONTAINER_BODY_DENIED')
    return row


def metadata_member(reader,inventory,name,journal):
    """Original stored-member algorithm with expected SHA explicitly UNKNOWN.

    CRC/length/local-central identity remain mandatory; the computed SHA is a
    new acquisition identity, never used as a fabricated prior expected SHA.
    """
    artifact=reader.anchor['artifact']; key=(artifact,name)
    if key in journal.saved: return journal.saved[key]
    row=selected_entry(inventory,name); e=row['zip']; journal.preflight_uncompressed(row['bytes'])
    head=reader.part(e['h'],30)
    signature,version,flags,method,mtime,mdate,crc,compressed,plain,nlen,xlen=struct.unpack('<IHHHHHIIIHH',head)
    check(signature==0x04034b50 and method==e['c']==0 and not flags&1,'METADATA_LOCAL_HEADER_REJECTED')
    actual=reader.part(e['h']+30,nlen+xlen)
    check(actual[:nlen].decode('utf-8' if flags&0x800 else 'cp437')==name and e['s']==e['z']==row['bytes'],
          'METADATA_LOCAL_NAME_OR_SIZE_CHANGED')
    if not flags&8:
        check((crc,compressed,plain)==(e['crc'],e['z'],e['s']),'METADATA_LOCAL_CENTRAL_DISAGREEMENT')
    position=e['h']+30+nlen+xlen
    check(position+row['bytes']<=row['central_offset'],'METADATA_PAYLOAD_ESCAPES_DATA_AREA')
    target=journal.output/'original-metadata'/str(artifact)/name
    target.parent.mkdir(parents=True,exist_ok=True); check(not target.exists(),'METADATA_OVERWRITE_DENIED')
    remaining=row['bytes']; checksum=hashlib.sha256(); crc_actual=0; count=0
    with target.open('xb') as output:
        while remaining:
            raw=reader.part(position,min(CHUNK,remaining)); output.write(raw); checksum.update(raw)
            crc_actual=zlib.crc32(raw,crc_actual); remaining-=len(raw); position+=len(raw); count+=len(raw)
    check(count==row['bytes'] and crc_actual==e['crc'],'METADATA_CRC_OR_LENGTH_CHANGED')
    journal.uncompressed_bytes+=count
    result=dict(artifact=artifact,member=name,path=target.as_posix(),bytes=count,sha256=checksum.hexdigest(),
        expected_sha256=None,expected_sha_authority='UNKNOWN_FIRST_OFFICIAL_ORIGIN_ORIGINAL_ACQUISITION',
        crc32=f'{crc_actual:08x}',zip=e,official_producer_head=HEAD,official_producer_run=PRODUCER_RUN,
        status='REMOTE_OFFICIAL_ORIGIN_ORIGINAL_ACQUIRED_NOT_ADMISSION_ROOT_LOCAL_UNKNOWN',
        root_local_physical_availability='UNKNOWN',whole_archive_digest_recomputed=False)
    journal.saved[key]=result; journal.records.append(result); return result


def known_member(reader,inventory,name,expected,journal,original_path=None):
    artifact=reader.anchor['artifact']; key=(artifact,name); row=selected_entry(inventory,name)
    check(re.fullmatch('[0-9a-f]{64}',expected['sha256']) is not None,'EXPECTED_EXTERNAL_SHA_MISSING')
    if expected.get('bytes') is not None: check(expected['bytes']==row['bytes'],'EXTERNAL_EXPECTED_LENGTH_CHANGED')
    if key in journal.saved:
        result=journal.saved[key]
        check(result['sha256']==expected['sha256'] and result['bytes']==row['bytes'],'DEDUP_IDENTITY_CONFLICT')
        journal.event(dict(state='EXACT_ORIGINAL_MEMBER_DEDUP',artifact=artifact,member=name,
                           original_path=original_path,sha256=result['sha256']))
        return result
    journal.preflight_uncompressed(row['bytes'])
    # Do not let a malicious local filename/extra-length move the original
    # reader's payload window into the central directory or another archive.
    head=reader.part(row['zip']['h'],30)
    local=struct.unpack('<IHHHHHIIIHH',head)
    check(local[0]==0x04034b50 and row['zip']['h']+30+local[-2]+local[-1]+row['bytes']<=row['central_offset'],
          'KNOWN_PAYLOAD_LOCAL_WINDOW_OUT_OF_DATA_BOUNDS')
    destination=journal.output/'raw'/str(artifact); destination.mkdir(parents=True,exist_ok=True)
    # The exact original fetch body verifies local header/name, original stored
    # CRC, length and externally expected SHA. Only part() transport is stricter.
    super(StrictArchiveReader,reader).fetch(name,dict(row,sha256=expected['sha256']),destination)
    target=destination/name
    result=dict(artifact=artifact,member=name,path=target.as_posix(),bytes=row['bytes'],sha256=expected['sha256'],
        expected_sha256=expected['sha256'],expected_sha_authority=expected['expected_identity_authority'],
        original_path=original_path,crc32=f'{row["zip"]["crc"]:08x}',zip=row['zip'],
        official_producer_head=HEAD,official_producer_run=PRODUCER_RUN,
        status='REMOTE_ORIGINAL_BYTES_MATCH_EXPECTED_IDENTITY_CARRIER_ONLY_ROOT_LOCAL_UNKNOWN',
        root_local_physical_availability='UNKNOWN',whole_archive_digest_recomputed=False)
    journal.uncompressed_bytes+=row['bytes']; journal.saved[key]=result; journal.records.append(result)
    return result


def raw_index(path):
    result={}
    with Path(path).open('r',encoding='utf-8') as stream:
        for line in stream:
            check(len(line)<=MIB and line.strip(),'RAW_INDEX_TRUNCATED_OR_UNKNOWN_LINE')
            value=json.loads(line)
            check(isinstance(value,dict) and all(k in value for k in ['original_path','resolved_path','bytes','sha256']),
                  'RAW_INDEX_SCHEMA_UNKNOWN_NO_GUESSED_FIELDS')
            name=value['original_path']; old=result.get(name)
            if old:
                check(all(old[k]==value[k] for k in ['original_path','resolved_path','bytes','sha256']),
                      'RAW_JOURNAL_CONTENT_IDENTITY_CHANGED')
                if 'payload' in old: check(value.get('payload')==old['payload'],'RAW_JOURNAL_PAYLOAD_CHANGED')
            result[name]=value
    return result


def original_payload(cp,index,expected):
    path=expected['original_path']; check(path in cp['files'] and path in index,'FINITE_ORIGINAL_PATH_MISSING')
    row=cp['files'][path]; previous=index[path]
    check(row.get('original_path')==path and all(row[k]==previous[k] for k in ['original_path','resolved_path','bytes','sha256']),
          'CP_RAW_INDEX_ORIGINAL_IDENTITY_DISAGREEMENT')
    payload=row.get('payload')
    check(isinstance(payload,str) and payload==previous.get('payload')
          and re.fullmatch('objects/[0-9a-f]{64}',payload) is not None
          and payload.split('/')[1]==row['sha256'],'EXACT_ORIGINAL_PAYLOAD_MAP_MISSING')
    if expected.get('sha256') is not None: check(row['sha256']==expected['sha256'],'TRUSTED_LIGHT_OR_LEDGER_SHA_CHANGED')
    if expected.get('bytes') is not None: check(row['bytes']==expected['bytes'],'TRUSTED_LEDGER_LENGTH_CHANGED')
    authority=(expected['expected_identity_authority'] if expected.get('sha256') is not None else
               'GENUINE_ORIGINAL_CP_RAW_FILES_FIRST_ACQUISITION_NOT_A_PRIOR_T02_HASH')
    return payload,dict(bytes=row['bytes'],sha256=row['sha256'],expected_identity_authority=authority)


def bind_manifest():
    check(os.environ.get('GITHUB_ACTIONS')=='true' and sys.platform=='linux'
          and os.environ.get('GITHUB_REPOSITORY')==REPO
          and os.environ.get('GITHUB_EVENT_NAME')=='push' and os.environ.get('GITHUB_REF')==BRANCH,
          'EXACT_GITHUB_DATA_BRANCH_CALLER_REQUIRED')
    control=load(HERE/'EXPORT_CONTROL.json'); raw=(HERE/'INPUT_MANIFEST.json').read_bytes(); manifest=json.loads(raw)
    check(control['driverReady'] is True and control['execute']=='ALLOW_REVIEWED_DATA_EXPORT_ONLY',
          'PENDING_ROOT_T02_SOURCE_AND_ACTUAL_TREE_REVIEW')
    check(control['repository']==REPO and control['expected_base']==HEAD and control['branch']==BRANCH,
          'ROOT_EXPORT_CALLER_BINDING_CHANGED')
    check(control['input_manifest_sha256']==digest(raw),'ROOT_INPUT_MANIFEST_PIN_CHANGED')
    for name in ['export_evidence.py','original_archive_reader.py']:
        check(control['source_sha256'][name]==digest((HERE/name).read_bytes()),'ROOT_EXPORT_SOURCE_PIN_CHANGED')
    workspace=Path(os.environ['GITHUB_WORKSPACE']).resolve()
    reviewed={x['path']:x for x in control['reviewed_workflows']}
    present={p.relative_to(workspace).as_posix() for ext in ['*.yml','*.yaml']
             for p in (workspace/'.github/workflows').glob(ext)}
    check(len(reviewed)==len(control['reviewed_workflows'])==6 and set(reviewed)==present,
          'EXACT_COMPLETE_SIX_WORKFLOW_PROJECTION_REQUIRED')
    for path,row in reviewed.items():
        raw_workflow=(workspace/path).read_bytes()
        check(len(raw_workflow)==row['bytes'] and digest(raw_workflow)==row['sha256'],
              'REVIEWED_WORKFLOW_BYTES_CHANGED')
    check(manifest['repository']==REPO and manifest['producer_binding']['driver_commit']==HEAD
          and manifest['producer_binding']['run_id']==str(PRODUCER_RUN),'ORIGINAL_PRODUCER_CHANGED')
    check([(a['role'],a['artifact']) for a in manifest['anchors']]==[('CP',14141463081),('PROOF',14141522967)],
          'EXACT_TWO_ORIGINAL_ARCHIVES_REQUIRED')
    check(manifest['original_proposed_requests']==dict(
        CP=['CHECKPOINT.json','STANDARD_IMPORTED_SNAPSHOT.json','RAW_INPUTS_INDEX.jsonl'],
        PROOF=['CACHE_CHECKPOINT_RETENTION.json','CHECKPOINT_SUMMARY.json','RETAINED_OBJECTS.json'])
        and manifest['exact_writer_authorized_requests']==dict(
        CP=['CHECKPOINT.json','RAW_FILES.jsonl','SNAPSHOT_ACQUISITION.json'],
        PROOF=['WEIL_RETENTION.json','CHECKPOINT_SUMMARY.json']),
        'EXACT_METADATA_NAME_ALLOWLIST_CHANGED_NO_DYNAMIC_OBJECTS')
    limits=manifest['limits']
    check(limits==dict(range_chunk_bytes=CHUNK,total_network_and_uncompressed_bytes=TOTAL,
        CP_metadata_aggregate_bytes=64*MIB,PROOF_metadata_aggregate_bytes=32*MIB,
        central_directory_bytes_each=16*MIB,api_metadata_bytes_each=MIB),'HARD_LIMIT_MANIFEST_CHANGED')
    project='/home/runner/work/_temp/t01-project/'
    exact=set()
    for module in manifest['modules']:
        check(module.startswith('LeanPool.KloostermanWeil.') and module not in {
              'LeanPool.KloostermanWeil.Stepanov.Algebra','LeanPool.KloostermanWeil.Carlitz.ClassGhost'},
              'ONLY_ACTUAL_R3_SUCCESSFUL14_MODULES_PERMITTED')
        relative=module.replace('.','/')
        exact.add(project+relative+'.lean')
        exact.add(project+'.lake/build/ir/'+relative+'.setup.json')
        exact.update(project+'.lake/build/lib/lean/'+relative+s for s in
                     ['.olean','.olean.server','.olean.private','.ir.sig','.ir','.ilean'])
    check(len(exact)==112 and {x['original_path'] for x in manifest['known_objects']}==exact,
          'FINITE_SOURCE_SETUP_ALL6_OUTPUT_ORIGINAL_PATH_SET_CHANGED')
    check({x['original_path'] for x in manifest['exact_CP_log_difference']}=={
        project+'T01_PROVENANCE.json',
        '/home/runner/work/_temp/weil34-evidence/CHECKPOINT_COLLECTOR_INPUT.json',
        '/home/runner/work/_temp/weil34-evidence/WEIL_RAW_CAPTURE.json',
        '/home/runner/work/_temp/weil34-evidence/cache-processes/bootstrap-loader-map.stdout',
        '/home/runner/work/_temp/weil34-evidence/cache-processes/runtime-audit.stdout'},
        'FINITE_ORIGINAL_LOG_DIFFERENCE_SET_CHANGED')
    return manifest


def export(manifest,journal):
    readers={}; inventories={}; metadata={}
    for anchor in manifest['anchors']:
        role=anchor['role']
        try:
            reader=StrictArchiveReader(anchor,journal); inventory=directory(reader,journal)
            readers[role]=reader; inventories[role]=inventory
            original=manifest['original_proposed_requests'][role]
            actual=manifest['exact_writer_authorized_requests'][role]
            requested=list(dict.fromkeys([*original,*actual]))
            status=[dict(member=n,exact_central_name_present=n in inventory,
                required_actual_writer_name=n in actual,alias_used=False,expected_sha256=None,
                obsolete_proposal_body_selected=n in actual) for n in requested]
            write_json(journal.output/'metadata'/str(anchor['artifact'])/'EXACT_REQUEST_INVENTORY.json',status)
            for row in status:
                if row['member'] in original:
                    journal.proposed_name_inventory.append(dict(artifact=anchor['artifact'],**row,
                        precedence='ROOT_CORRECTED_ACTUAL_WRITER_SET_IS_REQUIRED_OLD_PROPOSAL_IS_INVENTORY_ONLY'))
            # ROOT explicitly corrected the writer names. Missing old proposal
            # names neither alias the actual names nor block finite real export.
            existing=[n for n in actual if n in inventory]
            cap=64*MIB if role=='CP' else 32*MIB
            capped=list(existing)
            if role=='PROOF' and 'checkpoint-collection.log' in inventory:
                capped.append('checkpoint-collection.log')
            check(sum(inventory[n]['bytes'] for n in set(capped))<=cap,'METADATA_GROUP_AGGREGATE_CAP_HOLD')
            metadata[role]={}
            for name in existing:
                metadata[role][name]=metadata_member(reader,inventory,name,journal)
        except Exception as error:
            journal.failure(str(error) if isinstance(error,Hold) else type(error).__name__,artifact=anchor['artifact'],phase='OFFICIAL_DIRECTORY_OR_METADATA')
    check('CP' in readers and 'PROOF' in readers,'ONE_OR_BOTH_OFFICIAL_ARCHIVES_UNAVAILABLE')
    required_CP=['CHECKPOINT.json','RAW_FILES.jsonl','SNAPSHOT_ACQUISITION.json']
    required_PROOF=['WEIL_RETENTION.json','CHECKPOINT_SUMMARY.json']
    check(all(n in metadata.get('CP',{}) for n in required_CP)
          and all(n in metadata.get('PROOF',{}) for n in required_PROOF),
          'REQUIRED_EXACT_WRITER_METADATA_MISSING_HOLD_NO_SCHEMA_GUESS')
    cp=load(metadata['CP']['CHECKPOINT.json']['path'])
    check(cp['schema']==manifest['checkpoint_schema'] and cp['source_commit']==manifest['producer_binding']['source_commit']
          and str(cp['run_id'])==str(PRODUCER_RUN) and str(cp['run_attempt'])=='1'
          and cp['source_identity_sha256']==manifest['trusted_source_graph_sha256']
          and canonical(cp['runtime_state'])==manifest['trusted_runtime_state_canonical_sha256'],
          'ORIGINAL_CHECKPOINT_LIGHT_SOURCE_RUNTIME_BINDING_CHANGED')
    snapshot=load(metadata['CP']['SNAPSHOT_ACQUISITION.json']['path'])
    check(snapshot['raw_index']=='RAW_FILES.jsonl' and snapshot['acquisition_phase_complete'] is True
          and snapshot['kernel_verified'] is False,'EXACT_SNAPSHOT_RAW_INDEX_SCHEMA_CHANGED')
    index=raw_index(metadata['CP']['RAW_FILES.jsonl']['path'])
    selected=[*manifest['known_objects'],*manifest['exact_CP_log_difference']]
    check(len(manifest['modules'])==14 and len(manifest['known_objects'])==112
          and len({x['original_path'] for x in selected})==len(selected),'FINITE_SELECTION_CENSUS_CHANGED')
    exported={}
    for expected in selected:
        path=expected['original_path']
        try:
            payload,identity=original_payload(cp,index,expected)
            exported[path]=known_member(readers['CP'],inventories['CP'],payload,identity,journal,path)
        except Exception as error:
            journal.failure(str(error) if isinstance(error,Hold) else type(error).__name__,original_path=path,phase='FINITE_ORIGINAL_MEMBER')
    ret_record=metadata['PROOF']['WEIL_RETENTION.json']; ret=load(ret_record['path'])
    cp_record=metadata['CP']['CHECKPOINT.json']; summary_record=metadata['PROOF']['CHECKPOINT_SUMMARY.json']
    check(ret['binding']==manifest['producer_binding'] and ret['exit_code']==0 and not ret['integrity_errors']
          and ret['checkpoint_sha256']==cp_record['sha256'] and ret['root_source_count']==34
          and ret['root_source_rows_sha256']==manifest['trusted_source_graph_sha256']
          and ret['collector_sha256']=='773e4eab588c0d196c5b7ad86a3a0f90a6a0fe1c225baa7559b2b1380e853a76'
          and ret['collector_bytes']==32993 and ret['actual_collector_summary_sha256']==summary_record['sha256'],
          'ORIGINAL_COLLECTOR_POSTCHECKPOINT_CHAIN_HOLD')
    known_member(readers['PROOF'],inventories['PROOF'],'checkpoint-collection.log',dict(
        bytes=None,sha256=ret['stdout_sha256'],expected_identity_authority='GENUINE_ORIGINAL_WEIL_RETENTION_UNKNOWN_FIRST_METADATA'),journal)
    summary=load(summary_record['path'])
    check(summary==ret['actual_collector_summary'] and summary['checkpoint_sha256']==cp_record['sha256']
          and summary['green'] is False,'ORIGINAL_ACTUAL_SUMMARY_CHANGED')
    required_paths=[x['original_path'] for x in selected]
    check(all(path in exported for path in required_paths),'FINITE14_SOURCE_SETUP_SIXFACETS_OR_REQUIRED_LOG_INCOMPLETE')
    oldlogs='/home/runner/work/_temp/weil34-evidence/'
    provenance=exported['/home/runner/work/_temp/t01-project/T01_PROVENANCE.json']
    collector=exported[oldlogs+'CHECKPOINT_COLLECTOR_INPUT.json']; capture_record=exported[oldlogs+'WEIL_RAW_CAPTURE.json']
    check(provenance['sha256']==ret['provenance_sha256'] and collector['sha256']==ret['collector_manifest_sha256']
          and capture_record['sha256']==ret['raw_capture_sha256'],'ORIGINAL_PROVENANCE_MANIFEST_CAPTURE_HASH_CHAIN_CHANGED')
    prov=load(provenance['path']); capture=load(capture_record['path']); original_manifest=load(collector['path'])
    check(prov['binding']==manifest['producer_binding'] and canonical(prov['modules'])==manifest['trusted_full_source_rows_sha256']
          and canonical(original_manifest['files'])==manifest['trusted_source_graph_sha256']
          and capture['binding']==manifest['producer_binding'] and not capture['integrity_errors'],
          'ORIGINAL_SOURCE_GRAPH_OR_RAW_CAPTURE_SCHEMA_CHANGED')
    captured={x['path']:x for x in capture['files']}
    for expected in manifest['known_objects']:
        path=expected['original_path']
        check(path in captured and all(captured[path][k]==expected[k] for k in ['bytes','sha256']),
              'ORIGINAL_SELECTED_SOURCE_SETUP_OUTPUT_NOT_IN_CAPTURE_METADATA')
    tar_path=oldlogs+capture['archive']
    check(tar_path in cp['files'] and cp['files'][tar_path]['sha256']==capture['archive_sha256'],
          'ORIGINAL_NESTED_TAR_HASH_LINK_CHANGED')
    write_json(journal.output/'ORIGINAL_CROSS_LINKS.json',dict(status='ORIGINAL_COMPONENT_CROSS_LINKS_ONLY_NOT_MATH_ALLOWLIST',
        checkpoint_sha256=cp_record['sha256'],retention_sha256=ret_record['sha256'],
        producer_binding=manifest['producer_binding'],raw_capture_sha256=capture_record['sha256'],
        nested_tar_body_requested=False,nested_tar_sha_recomputed=False,
        original_classifications_modified=False,root_local_physical_availability='UNKNOWN'))
    journal.complete_selection=True


def main():
    # Even caller/metadata failures retain a receipt. No old original is erased.
    temporary=Path(os.environ['RUNNER_TEMP']).resolve(); output=temporary/'weil-r3-evidence-export'
    workspace=Path(os.environ['GITHUB_WORKSPACE']).resolve()
    check(not output.exists() and output.is_relative_to(temporary) and not output.is_relative_to(workspace),
          'FRESH_DISJOINT_CARRIER_OUTPUT_REQUIRED')
    output.mkdir(); journal=Journal(output); manifest=None
    try:
        manifest=bind_manifest(); export(manifest,journal)
    except Exception as error:
        journal.failure(str(error) if isinstance(error,Hold) else type(error).__name__,phase='EXPORT_HOLD')
    finally:
        available=[]
        verified={row['path'] for row in journal.records}
        # Enumerate only our fresh carrier output, never archive objects or the
        # original29k standard/private inputs. Failed partial bodies stay visible.
        for path in sorted(output.rglob('*')):
            if path.is_file() and not path.is_symlink():
                with path.open('rb') as stream: actual_sha=hashlib.file_digest(stream,'sha256').hexdigest()
                available.append(dict(path=path.relative_to(output).as_posix(),bytes=path.stat().st_size,
                    sha256=actual_sha,remote_expected_member_identity_verified=path.as_posix() in verified,
                    root_local_physical_availability='UNKNOWN'))
        write_json(output/'AVAILABLE_OUTPUT_BYTES.json',dict(status='REMOTE_CARRIER_OUTPUT_INVENTORY_ONLY',files=available,
            unverified_or_partial_files_preserved=True,proof_acceptance=False))
        receipt=dict(schema='weil-r3-finite-original-export-carrier-receipt-v1',
            status='HOLD_WITH_AVAILABLE_ORIGINAL_BYTES_RETAINED' if journal.failures else 'FINITE_ORIGINAL_BYTES_EXPORTED_CARRIER_ONLY',
            carrier=dict(repository=os.environ.get('GITHUB_REPOSITORY'),driver_commit=os.environ.get('GITHUB_SHA'),
                run_id=os.environ.get('GITHUB_RUN_ID'),run_attempt=os.environ.get('GITHUB_RUN_ATTEMPT'),
                actual_parent_runtime_verified=False),
            original_producer=dict(repository=REPO,driver_commit=HEAD,run_id=str(PRODUCER_RUN)),
            originals=journal.records,failures=journal.failures,total_network_body_bytes=journal.total_network_bytes,
            original_proposed_name_inventory=journal.proposed_name_inventory,
            total_network_body_bytes_reserved_upper_bound=journal.reserved_network_bytes,
            successfully_verified_selected_uncompressed_bytes=journal.uncompressed_bytes,
            all_selected_uncompressed_bytes_upper_bound=journal.reserved_network_bytes,
            GET_boundary_receipt='GET_BOUNDARIES.jsonl',
            whole_CP_or_proof_archive_downloaded=False,whole_archive_digest_recomputed=False,
            nested_tar_body_downloaded=False,mathematical_compiler_events=0,
            toolchain_installed_or_loaded=False,olean_or_IR_loaded=False,
            consumer_admission=False,proof_acceptance=False,new_proof_producer=False,
            old_CP_classifications_modified=False,reuseReady=False,root_local_physical_availability='UNKNOWN',
            finite_selected_original_payload_set_exported_remotely=journal.complete_selection,
            available_partial_original_files_retained_on_failure=True,
            input_manifest_sha256=digest((HERE/'INPUT_MANIFEST.json').read_bytes()))
        write_json(output/'EXPORT_RECEIPT.json',receipt)
        summary=dict(status=receipt['status'],original_files=len(journal.records),
            total_network_body_bytes=journal.total_network_bytes,mathematical_compiler_events=0,
            not_admission=True,not_proof_acceptance=True,reuseReady=False)
        print(json.dumps(summary,sort_keys=True))
        summary_path=os.environ.get('GITHUB_STEP_SUMMARY')
        if summary_path:
            with Path(summary_path).open('a',encoding='utf-8') as stream:
                stream.write('Original R3 bytes carrier only. Mathematical compiler events: 0. '
                    'No admission or proof acceptance; reuseReady=false. Status: '+receipt['status']+'\n')
    return 1 if journal.failures else 0


if __name__=='__main__':
    raise SystemExit(main())
