"""GitHub-only real carrier-decoder negatives; fake bytes earn no reuse credit."""
import copy
import hashlib
import json
import os
from pathlib import Path
import unittest
import zlib

if os.environ.get('GITHUB_ACTIONS')!='true':
    raise SystemExit('Never execute bound-input fixtures locally')

import carrier_originals as co
from weil_scope import BUNDLE


class R4BoundInputCases(unittest.TestCase):
    def authority(self):
        return json.loads((BUNDLE/'direct-reuse/R3_CARRIER_AUTHORITY.json').read_text())

    def receipt(self):
        return json.loads((BUNDLE/'direct-reuse/acquisition/carrier/EXPORT_RECEIPT.json').read_text())

    def test_bound_wrong_receipt_schema_rejected(self):
        value=self.receipt();value['schema']='READ_ONLY_STORED_ZIP_PHYSICAL_MEMBER_RANGE_RECEIPT_V1'
        with self.assertRaisesRegex(ValueError,'^R4 genuine carrier receipt schema required; no projected old V1 receipt$'):
            co.check_receipt(value,self.authority())

    def test_bound_carrier_cannot_become_original_producer(self):
        value=self.receipt();value['original_producer']['driver_commit']=co.CARRIER['head_sha']
        with self.assertRaisesRegex(ValueError,'^R4 carrier and original proof producer must remain distinct$'):
            co.check_receipt(value,self.authority())

    def test_bound_partial_export_rejected(self):
        value=self.receipt();value['finite_selected_original_payload_set_exported_remotely']=False
        with self.assertRaisesRegex(ValueError,'^R4 partial/carrier qualification or whole-archive promotion denied$'):
            co.check_receipt(value,self.authority())

    def test_bound_wrong_official_carrier_hash_rejected(self):
        value=json.loads((BUNDLE/'direct-reuse/acquisition/carrier/CARRIER_OFFICIAL_METADATA.connector.json').read_text())['structuredContent']['artifacts'][0]
        value['digest']='sha256:'+'0'*64
        with self.assertRaisesRegex(ValueError,'^R4 original/carrier official artifact identity changed$'):
            co.check_api(value,co.CARRIER)

    def test_bound_metadata_first_hash_cannot_be_relabelled_prior(self):
        value=self.receipt();record=copy.deepcopy(value['originals'][0]);pin=self.authority()['originals'][0]
        self.assertIsNone(record['expected_sha256']);record['expected_sha256']=record['sha256']
        with self.assertRaisesRegex(ValueError,'^R4 first-origin metadata digest cannot become a prior expected hash$'):
            co.check_record(pin,record)

    def test_bound_original_member_offset_mutation_rejected(self):
        value=self.receipt();record=copy.deepcopy(value['originals'][0]);pin=self.authority()['originals'][0]
        record['zip']['h']+=1
        with self.assertRaisesRegex(ValueError,'^R4 carrier original member hash/length/CRC/offset identity changed$'):
            co.check_record(pin,record)

    def test_bound_carrier_original_path_alias_rejected(self):
        record=copy.deepcopy(self.receipt()['originals'][5]);pin=self.authority()['originals'][5]
        record['original_path']='/FAKE/another-source.lean'
        with self.assertRaisesRegex(ValueError,'^R4 exact finite original/member/carrier path changed$'):
            co.check_record(pin,record)

    def fake_payload(self):
        raw=b'FAKE ONLY';pin=dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),
            artifact=14141463081,zip=dict(c=0,crc=zlib.crc32(raw)&0xffffffff,s=len(raw),z=len(raw),h=0),
            original_data_start=100,data_gets=[1],local_header_gets=[],name_extra_gets=[])
        groups={1:[dict(artifact=pin['artifact'],operation='EXACT_RANGE',range_start=100),
            dict(state='BODY_ACQUIRED',body_bytes=len(raw),body_sha256=pin['sha256'])]}
        return raw,pin,groups

    def test_bound_changed_actual_original_body_rejected(self):
        raw,pin,groups=self.fake_payload()
        with self.assertRaisesRegex(ValueError,'^R4 authentic original payload length/SHA mismatch$'):
            co.check_payload(b'CHANGED!!',pin,groups)

    def test_bound_original_CRC_mismatch_rejected(self):
        raw,pin,groups=self.fake_payload();pin['zip']['crc']^=1
        with self.assertRaisesRegex(ValueError,'^R4 authentic original payload CRC/stored size mismatch$'):
            co.check_payload(raw,pin,groups)

    def test_bound_GET_body_hash_mismatch_rejected(self):
        raw,pin,groups=self.fake_payload();groups[1][-1]['body_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'^R4 original GET body differs from authentic original payload bytes$'):
            co.check_payload(raw,pin,groups)

    def test_bound_original_GET_200_before_body_rejected(self):
        events=[json.loads(x) for x in (BUNDLE/'direct-reuse/acquisition/carrier/GET_BOUNDARIES.jsonl').read_text().splitlines()]
        target=next(x for x in events if x['operation']=='EXACT_RANGE' and x['state']=='HEADERS_BEFORE_BODY');target['status']=200
        anchors={x['artifact']:x for x in self.authority()['original_anchors']}
        with self.assertRaisesRegex(ValueError,'^R4 original GET strict206/range cap changed before body$'):
            co.journal_groups(events,anchors,self.receipt())

    def test_bound_original_CP_path_to_payload_mismatch_rejected(self):
        pin=dict(original_path='/FAKE/Source.lean',member='objects/'+'a'*64,bytes=1,sha256='a'*64)
        row=dict(original_path=pin['original_path'],resolved_path=pin['original_path'],bytes=1,sha256='a'*64,payload='objects/'+'b'*64)
        cp=dict(files={pin['original_path']:row});raw={pin['original_path']:copy.deepcopy(row)}
        with self.assertRaisesRegex(ValueError,'^R4 original path to payload/hash mapping changed$'):
            co.check_mapping(cp,raw,pin)

    def test_bound_original_collector_flag_promotion_rejected(self):
        expected=self.authority()['original_module_classifications'];changed=copy.deepcopy(expected)
        changed[0]['completed_guarded_compile_candidate']=True
        with self.assertRaisesRegex(ValueError,'^R4 original collector classifications/completed/kernel flags changed$'):
            co.check_classes(changed,expected)

    def test_bound_historical_review_cannot_pay_current_ABI(self):
        value=json.loads((BUNDLE/'direct-reuse/review/original-R3/ALLOWLIST.json').read_text())
        value['current_R4_ABI_and_complete_private_loaded_inputs_verified']=True
        with self.assertRaisesRegex(ValueError,'^R4 historical data availability cannot become current setup/ABI/proof acceptance$'):
            co.check_data_review(value,self.authority())

    def test_bound_prior_stream_donor_wrong_original_path_rejected(self):
        pin=dict(original_path='/FAKE/process.stdout',bytes=1,sha256='a'*64)
        row=dict(original_path='/FAKE/other.stdout',bytes=1,sha256='a'*64,payload='objects/'+'a'*64)
        with self.assertRaisesRegex(ValueError,'^R4 original stream donor path/hash identity changed$'):
            co.check_stream_donor(row['original_path'],row,pin)
