"""Strict original-R3 receipt decoder; byte carrier is never proof producer.

R1 uses its unchanged original V1 gate. This adapter is called only by the R3
context after current acquisition/fixtures. No compiler or proof helper runs.
"""
import hashlib
import json
from pathlib import Path
import shutil
import zlib

import qualified_algebra as qa
from coherent_cache import checked,read,require,sha
from weil_scope import BUNDLE,SOURCE

CARRIER=dict(artifact=14145156509,run=43672488484,
    head_sha='8b35c104fa4268924bfae649599164529ecac68f',artifactBytes=69369690,
    githubWholeArtifactDigest='63e95726be44c8cdedccf9691fbb71bfbac4551fb2beaa8d70955bfe3923fb58')
ORIGINAL_HEAD='2960e200301de4189c1c2793b918fc8aa7666930'
ORIGINAL_RUN=43657752592
DATA_AL_SHA='3ee55e22807f5f818634e6726d4e4e3205ba205624c9ba41903ade4575fdcaaa'


def check_receipt(value,authority):
    require(value['schema']=='weil-r3-finite-original-export-carrier-receipt-v1',
            'R4 genuine carrier receipt schema required; no projected old V1 receipt')
    require(value['carrier']==dict(repository='UyNewNas/goldbach-formalization',driver_commit=CARRIER['head_sha'],
                run_id=str(CARRIER['run']),run_attempt='1',actual_parent_runtime_verified=False)
            and value['original_producer']==dict(repository='UyNewNas/goldbach-formalization',
                driver_commit=ORIGINAL_HEAD,run_id=str(ORIGINAL_RUN)),
            'R4 carrier and original proof producer must remain distinct')
    require(value['status']=='FINITE_ORIGINAL_BYTES_EXPORTED_CARRIER_ONLY' and not value['failures']
            and value['finite_selected_original_payload_set_exported_remotely'] is True
            and value['whole_CP_or_proof_archive_downloaded'] is False
            and value['whole_archive_digest_recomputed'] is False and value['nested_tar_body_downloaded'] is False
            and value['mathematical_compiler_events']==0 and value['toolchain_installed_or_loaded'] is False
            and value['olean_or_IR_loaded'] is False and value['consumer_admission'] is False
            and value['proof_acceptance'] is False and value['new_proof_producer'] is False
            and value['old_CP_classifications_modified'] is False and value['reuseReady'] is False,
            'R4 partial/carrier qualification or whole-archive promotion denied')
    require(authority['carrier_anchor']==CARRIER and authority['carrier_is_not_proof_producer'] is True
            and authority['original_binding']['driver_commit']==ORIGINAL_HEAD
            and authority['original_binding']['run_id']==str(ORIGINAL_RUN),
            'R4 exact carrier authority and original binding changed')


def check_api(value,anchor):
    require(value['id']==anchor['artifact'] and value['size_in_bytes']==anchor['artifactBytes']
            and value['digest']=='sha256:'+anchor['githubWholeArtifactDigest']
            and value['workflow_run']['id']==anchor['run']
            and value['workflow_run']['head_sha']==anchor['head_sha'] and value['expired'] is False,
            'R4 original/carrier official artifact identity changed')


def journal_groups(events,anchors,receipt):
    groups={}; total=0
    for event in events:
        require(event.get('token_or_signed_URL_recorded') is False,
                'R4 original GET boundary contains an unapproved event')
        groups.setdefault(event['get'],[]).append(event)
    require(set(groups)==set(range(1,len(groups)+1)),'R4 original GET sequence is incomplete')
    for rows in groups.values():
        first=rows[0];artifact=first['artifact']
        require(first['state']=='REQUEST_STARTED' and artifact in anchors,
                'R4 original GET start/producer binding changed')
        operation=first['operation']
        require(all(e['artifact']==artifact and e['operation']==operation for e in rows),
                'R4 original GET records were rebound')
        if operation=='AUTHENTICATED_ZIP_REDIRECT_NO_BODY':
            require(len(rows)==2 and rows[1]['state']=='HEADERS_NO_BODY'
                    and rows[1]['status']==302 and rows[1]['body_bytes']==0,
                    'R4 original redirect consumed bytes or changed identity')
            continue
        require(len(rows)==3 and rows[1]['state']=='HEADERS_BEFORE_BODY'
                and rows[2]['state']=='BODY_ACQUIRED','R4 original GET partial or missing boundary rejected')
        header,body=rows[1:];size=body['body_bytes']
        require(header['content_encoding']=='identity' and header['body_bytes']==0
                and header['content_length']==str(size),'R4 original GET identity/length changed')
        if operation=='EXACT_RANGE':
            start=first['range_start'];declared=first['expected_body_bytes'];limit=anchors[artifact]['artifactBytes']
            require(type(start) is int and 0<declared<=4*1024*1024 and size==declared
                    and start>=0 and start+size<=limit and header['status']==206
                    and header['content_range']==f'bytes {start}-{start+size-1}/{limit}',
                    'R4 original GET strict206/range cap changed before body')
        else:
            require(operation=='OFFICIAL_API_METADATA' and header['status']==200 and size<=1024*1024,
                    'R4 original GET unsupported operation denied')
        total+=size
        require(body['cumulative_network_bytes']==total,'R4 original GET cumulative body count changed')
    require(total==receipt['total_network_body_bytes']==receipt['total_network_body_bytes_reserved_upper_bound']
            and total<=160*1024*1024,'R4 original GET aggregate cap/partial accounting changed')
    return groups


def check_record(pin,record):
    require(all(record[k]==pin[k] for k in ['artifact','member','bytes','sha256','zip'])
            and record['official_producer_head']==ORIGINAL_HEAD and record['official_producer_run']==ORIGINAL_RUN,
            'R4 carrier original member hash/length/CRC/offset identity changed')
    require(record['expected_sha256']==pin['expected_sha256_at_first_export']
            and record['expected_sha_authority']==pin['expected_sha_authority_at_first_export'],
            'R4 first-origin metadata digest cannot become a prior expected hash')
    require(record.get('original_path')==pin['original_path']
            and record['path']=='/home/runner/work/_temp/weil-r3-evidence-export/'+pin['carrier_member'],
            'R4 exact finite original/member/carrier path changed')


def check_payload(raw,pin,groups):
    require(len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],
            'R4 authentic original payload length/SHA mismatch')
    require(zlib.crc32(raw)&0xffffffff==pin['zip']['crc']
            and pin['zip']['s']==pin['zip']['z']==len(raw) and pin['zip']['c']==0,
            'R4 authentic original payload CRC/stored size mismatch')
    current=pin['original_data_start'];begin=current
    for get in pin['data_gets']:
        rows=groups[get];body=rows[-1]
        require(rows[0]['artifact']==pin['artifact'] and rows[0]['operation']=='EXACT_RANGE'
                and rows[0]['range_start']==current,'R4 original payload GET offsets are not contiguous')
        size=body['body_bytes'];part=raw[current-begin:current-begin+size]
        require(len(part)==size and hashlib.sha256(part).hexdigest()==body['body_sha256'],
                'R4 original GET body differs from authentic original payload bytes')
        current+=size
    require(current==begin+len(raw),'R4 original GET coverage is partial')
    for get in pin['local_header_gets']:
        rows=groups[get]
        require(rows[0]['artifact']==pin['artifact'] and rows[0]['range_start']==pin['zip']['h']
                and rows[-1]['body_bytes']==30,'R4 original local header GET offset changed')
    for get in pin['name_extra_gets']:
        rows=groups[get]
        require(rows[0]['artifact']==pin['artifact'] and rows[0]['range_start']==pin['zip']['h']+30
                and rows[-1]['body_bytes']==begin-pin['zip']['h']-30,
                'R4 original local name/extra GET offset changed')


def raw_records(path):
    rows={}
    for line in Path(path).read_text(encoding='utf-8').splitlines():
        value=json.loads(line);name=value['original_path'];old=rows.get(name)
        if old:
            require(all(old[k]==value[k] for k in ['original_path','resolved_path','bytes','sha256']),
                    'R4 original RAW journal content identity changed')
            if 'payload' in old: require(value.get('payload')==old['payload'],'R4 original RAW journal payload changed')
        rows[name]=value
    return rows


def check_mapping(cp,raw,pin):
    path=pin['original_path']
    require(path in cp['files'] and path in raw,'R4 finite original path absent from CP/RAW index')
    value=cp['files'][path];previous=raw[path]
    require(value['original_path']==path and previous['original_path']==path
            and all(value[k]==previous[k]==pin[k] for k in ['bytes','sha256'])
            and value['resolved_path']==previous['resolved_path']
            and value.get('payload')==previous.get('payload')==pin['member']
            and pin['member']=='objects/'+pin['sha256'],
            'R4 original path to payload/hash mapping changed')


def check_classes(modules,expected):
    actual=[{k:r[k] for k in ['module','classification','completed_guarded_compile_candidate','kernel_verified']} for r in modules]
    require(actual==expected,'R4 original collector classifications/completed/kernel flags changed')


def check_data_review(value,authority):
    require(value['schema']=='t02-weil-r3-original14-physical-evidence-allowlist-v1'
            and value['status']=='PASS_FINITE_ORIGINAL14_PHYSICAL_EVIDENCE_AVAILABLE_CURRENT_R4_RUNTIME_HOLD'
            and value['original_producer']==authority['original_binding']
            and value['carrier']['artifact']==CARRIER['artifact'] and value['carrier']['run']==CARRIER['run']
            and value['carrier']['head']==CARRIER['head_sha'] and value['carrier']['bytes']==CARRIER['artifactBytes']
            and value['carrier']['sha256']==CARRIER['githubWholeArtifactDigest']
            and value['carrier']['is_proof_producer'] is False
            and value['selected_originals']==123 and value['selected_CP_original_paths']==117
            and value['current_R4_source_identity_draft_freeze_sha256']=='370699cbc0f25b87b58336f0419b4e39e3ac31cacc9e3ea0500927006249664c'
            and authority['source_commit_current']==SOURCE=='9c26636f2bf35991f0fb16e4fe76eb165bdee056',
            'R4 independent original physical data review binding changed')
    require(value['data_allowlist'] is True and value['allow_next_candidate_to_bind_exact_historical_bytes'] is True
            and value['allow_dispatch'] is False and value['reuseReady'] is False and value['driverReady'] is False
            and value['current_R4_setup_generated_or_compared'] is False
            and value['current_R4_ABI_and_complete_private_loaded_inputs_verified'] is False
            and value['current_consumer_admission'] is False and value['full34_proof_pass'] is False
            and value['new_proof_credit']==0,
            'R4 historical data availability cannot become current setup/ABI/proof acceptance')


def check_review_components(authority,pins,transport,streams):
    require(pins['original_binding']==authority['original_binding'] and pins['carrier_sha256']==CARRIER['githubWholeArtifactDigest']
            and pins['current_setup_generated_or_compared'] is False and pins['reuseReady'] is False,
            'R4 independently reviewed original physical pins changed')
    expected={}
    for row in pins['selected117']:
        expected[(row['original_artifact'],row['original_member'])]=dict(artifact=row['original_artifact'],member=row['original_member'],
            bytes=row['bytes'],sha256=row['sha256'],zip=row['original_zip'],carrier_member=row['carrier_member'],original_path=row['original_path'])
    for row in pins['metadata_and_postcollector']:
        expected[(row['artifact'],row['member'])]=dict(**{k:row[k] for k in ['artifact','member','bytes','sha256','zip','carrier_member']},original_path=None)
    require(len(expected)==123,'R4 independent physical finite set changed')
    bindings={(x['artifact'],x['member']):x for x in transport['original_body_GET_bindings']}
    for row in authority['originals']:
        key=(row['artifact'],row['member'])
        require(key in expected and all(row[k]==expected[key][k] for k in expected[key]),
                'R4 current original authority differs from independent original physical pins')
        binding=bindings[key]
        require(row['local_header_gets']==binding['local_header_gets']
                and row['name_extra_gets']==[binding['name_get']] and row['data_gets']==binding['body_gets']
                and row['bytes']==binding['bytes'] and row['sha256']==binding['sha256'],
                'R4 original transport GET bindings differ from independent data review')
    require(not transport['failures'] and transport['GET_requests']==498 and transport['network_body_bytes']==66521780
            and transport['current_R4_runtime_verified'] is False,
            'R4 independent original transport availability review changed')
    require(streams['original_head']==ORIGINAL_HEAD and streams['original_run']==ORIGINAL_RUN
            and streams['count']==19 and streams['all_available'] is True,
            'R4 independent historical nonempty raw stream availability changed')
    known={x['path']:x for x in streams['streams']}
    for row in authority['deduplicated_authentic_prior_R1_streams']:
        require(row['original_path'] in known and all(row[k]==known[row['original_path']][k] for k in ['bytes','sha256']),
                'R4 same-hash original stream donor is outside independent historical pins')


def check_stream_donor(original_path,cp_row,pin):
    require(original_path==pin['original_path'] and cp_row['original_path']==original_path
            and all(cp_row[k]==pin[k] for k in ['bytes','sha256'])
            and cp_row['payload']=='objects/'+pin['sha256'],
            'R4 original stream donor path/hash identity changed')


class CarrierOriginals:
    def __init__(self,context):
        self.context=context;self.root=context.inputs;self.used={};self.original_files={}
        pin=context.selected['carrier_authority'];path=BUNDLE/pin['bundle_relative_path'];checked(path,pin)
        self.authority=read(path);a=self.authority
        require(a['historical_original_data_reviewed'] is True and a['current_consumer_qualified'] is False
                and a['reuseReady'] is False and a['independent_data_allowlist'] is not None,
                'R4 HOLD: independent genuine original physical data review missing')
        local_authority=qa.relative(self.root,'acquisition/carrier/R3_CARRIER_AUTHORITY.json')
        checked(local_authority,pin);self.keep(local_authority)
        for row in a['frozen_receipts']:
            target=qa.relative(self.root,row['input_relative_path']);checked(target,row);self.keep(target)
        review=a['independent_data_allowlist'];review_path=qa.relative(self.root,review['input_relative_path']);checked(review_path,review)
        value=read(review_path)
        require(sha(review_path)==DATA_AL_SHA and value['status']==review['expected_status'],
                'R4 independent physical data review authority changed')
        check_data_review(value,a)
        components=a['independent_review_components']
        def component(name):
            row=components[name];target=qa.relative(self.root,row['input_relative_path']);checked(target,row)
            signed=next(x for x in value['review_artifacts'] if x['path']==name)
            require(row['sha256']==signed['sha256'] and row['bytes']==signed['bytes'],
                    'R4 physical review component is not pinned by the independent allowlist')
            return read(target)
        check_review_components(a,component('ORIGINAL14_PHYSICAL_PINS.json'),
            component('TRANSPORT_AND_FINAL_AVAILABILITY_CHECKS.json'),component('HISTORICAL_NONEMPTY_RAW_STREAMS_NOW_AVAILABLE.json'))
        self.keep(review_path)
        receipt_path=qa.relative(self.root,'acquisition/carrier/EXPORT_RECEIPT.json')
        self.receipt=read(receipt_path);check_receipt(self.receipt,a)
        official=read(qa.relative(self.root,'acquisition/carrier/CARRIER_OFFICIAL_METADATA.connector.json'))['structuredContent']['artifacts']
        require(len(official)==1,'R4 exact carrier official metadata singleton required');check_api(official[0],CARRIER)
        anchors={x['artifact']:x for x in a['original_anchors']}
        for artifact,anchor in anchors.items():
            require(anchor['head_sha']==ORIGINAL_HEAD and anchor['run']==ORIGINAL_RUN,
                    'R4 original anchor cannot become the carrier producer')
            check_api(read(qa.relative(self.root,'acquisition/carrier/api/'+str(artifact)+'.json')),anchor)
        events=[json.loads(x) for x in qa.relative(self.root,'acquisition/carrier/GET_BOUNDARIES.jsonl').read_text().splitlines()]
        groups=journal_groups(events,anchors,self.receipt)
        records={(r['artifact'],r['member']):r for r in self.receipt['originals']}
        pins={(r['artifact'],r['member']):r for r in a['originals']}
        require(len(records)==len(self.receipt['originals'])==len(pins)==123
                and set(records)==set(pins),'R4 exact123 original finite records required')
        self.pins=pins
        for key,pin in pins.items():
            check_record(pin,records[key]);body_path=qa.relative(self.root,pin['input_relative_path']);checked(body_path,pin)
            check_payload(body_path.read_bytes(),pin,groups);self.keep_original(body_path)
        raw=a['raw_CP_index'];cp=read(qa.relative(self.root,raw['checkpoint_input']))
        require(cp['schema']=='t01-coherent-build-checkpoint-v3' and cp['source_commit']==a['original_binding']['source_commit']
                and str(cp['run_id'])==str(ORIGINAL_RUN) and str(cp['run_attempt'])=='1',
                'R4 original CP source/run/attempt binding changed')
        index=raw_records(qa.relative(self.root,raw['raw_index_input']))
        selected=[r for r in a['originals'] if r['original_path'] is not None]
        require(len(selected)==117,'R4 exact117 source/setup/output/log original paths required')
        for pin in selected:check_mapping(cp,index,pin)
        check_classes(cp['modules'],a['original_module_classifications'])
        snapshot=read(qa.relative(self.root,raw['snapshot_input']))
        require(snapshot['raw_index']=='RAW_FILES.jsonl' and snapshot['acquisition_phase_complete'] is True
                and snapshot['kernel_verified'] is False,'R4 original snapshot RAW index binding changed')

    def keep(self,path):
        self.used[str(path)]=qa.file_record(path)

    def keep_original(self,path):
        self.original_files[str(path)]=qa.file_record(path)

    def authentication_inputs(self):
        return list(self.used.values())

    def original(self,row):
        key=(row['artifact'],row['member'])
        require(key in self.pins,'R4 selected original is outside the exact finite carrier set')
        pin=self.pins[key]
        require(all(row[k]==pin[k] for k in ['bytes','sha256','input_relative_path']),
                'R4 selected original path/body differs from genuine carrier authority')
        anchor=next(x for x in self.authority['original_anchors'] if x['artifact']==row['artifact'])
        require(row['archive_sha256']==anchor['githubWholeArtifactDigest']
                and row['authenticated_acquisition_receipt_sha256']==sha(qa.relative(self.root,'acquisition/carrier/EXPORT_RECEIPT.json'))
                and row['acquisition_receipt_relative_path']=='acquisition/carrier/EXPORT_RECEIPT.json'
                and row['authentic_receipt_schema']==self.receipt['schema'],
                'R4 selected original acquisition receipt/anchor changed')
        path=qa.relative(self.root,row['input_relative_path']);checked(path,row);self.keep_original(path)
        return path

    def deduplicate_prior_stream(self,old_path,cp_row):
        pins=[x for x in self.authority['deduplicated_authentic_prior_R1_streams'] if x['original_path']==old_path]
        if not pins:return
        require(len(pins)==1,'R4 duplicate historical stream donor pin')
        pin=pins[0];check_stream_donor(old_path,cp_row,pin)
        target=qa.relative(self.root,'raw/'+cp_row['payload'])
        donor=qa.relative(self.root.parent,pin['donor_input_relative_path']);checked(donor,pin)
        if target.exists():
            checked(target,pin)
        else:
            require(not target.exists(),'R4 original stream donor overwrite denied')
            target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(donor,target);checked(target,pin)
        self.keep_original(donor);self.keep_original(target)


if __name__=='__main__':
    raise SystemExit('Library only; no local candidate/helper or object execution is permitted')
