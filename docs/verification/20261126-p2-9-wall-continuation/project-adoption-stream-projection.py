"""Read one pinned original adoption JSON once; emit a bounded metadata projection.
No registry/source/object/log reads, no receipt dereference, no Lean or filesystem writes.
"""
import base64, codecs, hashlib, io, json, math, os, sys, tarfile
from pathlib import Path

INPUT_PATH = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/project-adoptions/attempt-001/PROJECT_CACHE_ADOPTION.json')
EXPECTED_FILE_BYTES = 882795159
EXPECTED_FILE_SHA256 = 'c481b63afedeb846f3a07371518c692b3ce71eeb2050fe48b9fc2b527a763269'
EXPECTED_PREFIX_SHA256 = 'c6199ac7c13e3eb83551d0621c4172e8025034f166c670949f956d201ac56721'
EXPECTED_IDENTITY = {'resolved_path': '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/project-adoptions/attempt-001/PROJECT_CACHE_ADOPTION.json', 'lstat': {'st_dev': 27, 'st_ino': 917723, 'st_mode': 33152, 'st_size': 882795159, 'st_mtime_ns': 1795519130822356563, 'st_ctime_ns': 1795519130822356563}, 'stat': {'st_dev': 27, 'st_ino': 917723, 'st_mode': 33152, 'st_size': 882795159, 'st_mtime_ns': 1795519130822356563, 'st_ctime_ns': 1795519130822356563}}
BASE_JSON_STREAM_FILE_SHA256 = '07200ca08452f61d0185371215e8644742d17e88ac9273cf536ba180d961b6d9'
CANDIDATE_RECORD_MAP_SHA256 = '7abe7d6109098c5c283f4f216555cf40795a2c8fc23324825ed4283e07b97478'
CANDIDATE_MODULES = (
    'ImbalancedChen.ActualGridEnvelopes',
    'ImbalancedChen.ActualPrimeBoxMass',
    'ImbalancedChen.ActualPrimeBoxTestFunctions',
    'ImbalancedChen.ActualPrimePolyhedralTestFunctions',
    'ImbalancedChen.ActualPrimeReciprocalMass',
    'ImbalancedChen.AffinePrimeGates',
    'ImbalancedChen.AffinePrimeWallReserve',
    'ImbalancedChen.BadSourceLocalization',
    'ImbalancedChen.BoundaryArbitraryLog',
    'ImbalancedChen.BoundaryCellContainment',
    'ImbalancedChen.BoundaryGlobalCaps',
    'ImbalancedChen.BoundaryGridBudget',
    'ImbalancedChen.BoundaryLogMesh',
    'ImbalancedChen.ChenInitialCorrectionBudget',
    'ImbalancedChen.ChenInitialPrimeSource',
    'ImbalancedChen.ChenPrimeHarmonicFinite',
    'ImbalancedChen.ChenQuotientPrimeSource',
    'ImbalancedChen.CoprimeRecentering',
    'ImbalancedChen.Counting',
    'ImbalancedChen.CurvedDiscrepancyReduction',
    'ImbalancedChen.CurvedRegionDiscrepancy',
    'ImbalancedChen.FinitePrimeGeometryCore',
    'ImbalancedChen.FiniteSieveModel',
    'ImbalancedChen.FirstExitDepthSplice',
    'ImbalancedChen.FirstExitPresieveProjection',
    'ImbalancedChen.FirstExitTree',
    'ImbalancedChen.HalfProductGeometry',
    'ImbalancedChen.HalfProductSource',
    'ImbalancedChen.LogCutoffError',
    'ImbalancedChen.LogMeshGridCount',
    'ImbalancedChen.LogPrimeBoxIntegral',
    'ImbalancedChen.LogPrimeBoxMesh',
    'ImbalancedChen.MultiplicativeGridPartition',
    'ImbalancedChen.Multiplicity',
    'ImbalancedChen.NormalizationGrowth',
    'ImbalancedChen.OrderedBad',
    'ImbalancedChen.Part5OriginalH430FullMemberMeasurable',
    'ImbalancedChen.PowerErrorBudget',
    'ImbalancedChen.QuotientChenElevenSum',
    'ImbalancedChen.QuotientChenFourCounts',
    'ImbalancedChen.QuotientChenFourPrime',
    'ImbalancedChen.QuotientChenInitialCounts',
    'ImbalancedChen.QuotientChenNinthSwitch',
    'ImbalancedChen.QuotientChenPositiveBound',
    'ImbalancedChen.QuotientChenSummedBridge',
    'ImbalancedChen.QuotientChenSwitchGeometry',
    'ImbalancedChen.QuotientChenWeightCases',
    'ImbalancedChen.RationalPowers',
    'ImbalancedChen.RectangleDiscrepancyAssembly',
    'ImbalancedChen.RetainedModuli',
    'ImbalancedChen.RoughPrimeUniverse',
    'ImbalancedChen.RoughSquareException',
    'ImbalancedChen.SieveSourceCoprimality',
    'ImbalancedChen.SingularSeries',
    'ImbalancedChen.TotientReciprocalBudget',
)

class JsonStream:
    """Use the standard JSON decoder for one bounded graph row at a time."""
    def __init__(self, source):
        self.source = source
        self.buffer = ""
        self.position = 0
        self.eof = False
        self.decoder = json.JSONDecoder()

    def more(self):
        self.buffer = self.buffer[self.position:]
        self.position = 0
        block = self.source.read(65536)
        self.buffer += block
        if not block:
            self.eof = True

    def peek(self):
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position] in " \r\n\t":
                self.position += 1
            if self.position < len(self.buffer):
                return self.buffer[self.position]
            if self.eof:
                return None
            self.more()

    def expect(self, token):
        assert self.peek() == token, ("Unexpected JSON delimiter", token, self.peek())
        self.position += 1

    def value(self):
        assert self.peek() is not None, "Unexpected JSON EOF"
        while True:
            try:
                value, end = self.decoder.raw_decode(self.buffer, self.position)
            except json.JSONDecodeError:
                if self.eof:
                    raise
                self.more()
                continue
            # A scalar number may continue in the next block.
            if end == len(self.buffer) and not self.eof:
                self.more()
                continue
            # raw_decode may accept the integer prefix of a split decimal or
            # exponent (for example, "1." or "1e-"). Wait for a complete value
            # followed by a structural delimiter, rather than accepting it.
            if end < len(self.buffer) and self.buffer[end] not in " \r\n\t,]}:":
                if not self.eof:
                    self.more()
                    continue
                raise json.JSONDecodeError("Invalid value delimiter", self.buffer, end)
            self.position = end
            return value

class ProjectionBound(Exception):
    pass


class HashedUtf8Reader:
    """One binary pass, strict incremental UTF-8, and the whole-file digest."""
    def __init__(self, source, byte_limit, chunk_size=65536):
        self.source, self.byte_limit, self.chunk_size = source, byte_limit, chunk_size
        self.decoder = codecs.getincrementaldecoder('utf-8')('strict')
        self.digest = hashlib.sha256()
        self.prefix_digest = hashlib.sha256()
        self.bytes_read = 0
        self.eof = False

    def raw_block(self, size):
        block = self.source.read(min(size, self.byte_limit - self.bytes_read + 1))
        before = self.bytes_read
        self.bytes_read += len(block)
        self.digest.update(block)
        if before < 65536:
            self.prefix_digest.update(block[:65536 - before])
        if self.bytes_read > self.byte_limit:
            raise ProjectionBound('input grew beyond the fixed original byte count')
        return block

    def read(self, size):
        if self.eof:
            return ''
        while True:
            block = self.raw_block(min(size, self.chunk_size))
            if not block:
                self.eof = True
                return self.decoder.decode(b'', final=True)
            text = self.decoder.decode(block, final=False)
            if text:
                return text

    def drain_hash_only(self):
        while not self.eof:
            if not self.raw_block(65536):
                self.eof = True


class RawCapture:
    def __init__(self, offset, limit):
        self.offset, self.limit, self.count = offset, limit, 0
        self.digest = hashlib.sha256()
        self.prefix = bytearray()

    def feed(self, raw):
        self.count += len(raw)
        self.digest.update(raw)
        available = max(0, self.limit - len(self.prefix))
        self.prefix.extend(raw[:available])

    def finish(self):
        return {'original_byte_offset': self.offset, 'original_value_bytes': self.count,
                'original_value_sha256': self.digest.hexdigest()}


class BoundedJsonStream(JsonStream):
    """Preserve JsonStream unchanged; account for original UTF-8 byte slices."""
    def __init__(self, source, scalar_char_limit=1048576):
        super().__init__(source)
        self.scalar_char_limit = scalar_char_limit
        self.accounted_position = 0
        self.consumed_bytes = 0
        self.captures = []

    def flush_consumed(self):
        raw = self.buffer[self.accounted_position:self.position].encode('utf-8')
        if raw:
            for capture in self.captures:
                capture.feed(raw)
            self.consumed_bytes += len(raw)
        self.accounted_position = self.position

    def more(self):
        self.flush_consumed()
        super().more()
        self.accounted_position = 0
        if len(self.buffer) > self.scalar_char_limit:
            raise ProjectionBound('single undecoded scalar exceeded the bounded buffer')

    def begin_capture(self, limit):
        self.peek()
        self.flush_consumed()
        capture = RawCapture(self.consumed_bytes, limit)
        self.captures.append(capture)
        return capture

    def end_capture(self, capture):
        self.flush_consumed()
        assert self.captures.pop() is capture
        return capture.finish()


def json_key(stream):
    assert stream.peek() == '"', 'JSON object key must start with a quote'
    value = stream.value()
    assert isinstance(value, str), 'JSON object key is not a string'
    return value


def walk_value(stream, observer=None, path=(), depth=0):
    """Validate object/array framing without materializing their children."""
    if depth > 128:
        raise ProjectionBound('JSON nesting exceeded 128')
    token = stream.peek()
    if token in ('{', '['):
        is_object = token == '{'
        close = '}' if is_object else ']'
        stream.expect(token)
        count = 0
        if stream.peek() != close:
            while True:
                key = json_key(stream) if is_object else count
                if is_object:
                    stream.expect(':')
                child_path = path + (key,) if observer is not None else ()
                walk_value(stream, observer, child_path, depth + 1)
                count += 1
                if stream.peek() != ',':
                    break
                stream.expect(',')
        stream.expect(close)
        return {'kind': 'object' if is_object else 'array', 'direct_entries': count}
    assert token is not None, 'JSON value missing at EOF'
    value = stream.value()
    assert not isinstance(value, (dict, list)), 'containers must use structural walk'
    if isinstance(value, float):
        assert math.isfinite(value), 'non-finite JSON scalar'
    if observer is not None:
        observer(path, value)
    kind = ('null' if value is None else 'boolean' if isinstance(value, bool) else
            'string' if isinstance(value, str) else 'number')
    return {'kind': kind}


class AdoptionProjection:
    def __init__(self, stream, candidates, field_limit=65536, total_limit=4194304):
        self.stream, self.candidates = stream, set(candidates)
        self.field_limit, self.remaining = field_limit, total_limit
        self.adopted_keys, self.selected, self.root_fields = [], {}, []
        self.receipt_pointers, self.pointer_omissions = [], 0
        self.pointer_bytes, self.key_bytes = 0, 0
        self.metadata_omissions = 0
        self.root_keys = []
        self.adopted_seen = False

    def account_key(self, key):
        self.key_bytes += len(key.encode('utf-8'))
        if self.key_bytes > 1048576:
            raise ProjectionBound('retained root/adopted/selected field keys exceeded 1 MiB')

    def pointer(self, path, value):
        if not isinstance(value, str) or not value.endswith('.json'):
            return
        words = ('path', 'file', 'receipt', 'qualification', 'audit', 'report', 'artifact')
        if not any(any(w in str(p).lower() for w in words) for p in path):
            return
        if (len(self.receipt_pointers) >= 256 or len(value) > 8192 or
                sum(len(str(p)) for p in path) > 8192):
            self.pointer_omissions += 1
            return
        pointer = {'json_path': list(path), 'explicit_value': value, 'dereferenced': False}
        size = len(json.dumps(pointer).encode())
        if size + self.pointer_bytes > 65536:
            self.pointer_omissions += 1
            return
        self.pointer_bytes += size
        self.receipt_pointers.append(pointer)

    def metadata_value(self, path):
        cap = self.stream.begin_capture(min(self.field_limit, self.remaining))
        shape = walk_value(self.stream, self.pointer, path)
        result = self.stream.end_capture(cap)
        result.update(shape)
        complete = cap.count <= cap.limit
        result['original_value_json_captured_complete'] = complete
        if complete:
            result['original_value_json'] = bytes(cap.prefix).decode('utf-8')
            self.remaining -= cap.count
        else:
            result['omitted_reason'] = 'bounded_metadata_capture'
            self.metadata_omissions += 1
        return result

    def selected_entry(self, module):
        row_capture = self.stream.begin_capture(0)
        row = {'metadata_fields': [], 'omitted_actual_import_maps': []}
        if self.stream.peek() != '{':
            row['non_object_entry'] = self.metadata_value(('adopted', module))
        else:
            self.stream.expect('{')
            seen = set()
            if self.stream.peek() != '}':
                while True:
                    key = json_key(self.stream)
                    self.account_key(key)
                    assert key not in seen, 'duplicate selected-entry field'
                    seen.add(key)
                    if len(seen) > 4096:
                        raise ProjectionBound('too many selected-entry metadata fields')
                    self.stream.expect(':')
                    if key == 'actual_import_map':
                        cap = self.stream.begin_capture(0)
                        shape = walk_value(self.stream)
                        item = self.stream.end_capture(cap)
                        item.update(shape)
                        item.update({'field': key, 'body_omitted': True,
                                     'reason': 'intentional_actual_import_map_body_omission'})
                        row['omitted_actual_import_maps'].append(item)
                    else:
                        item = self.metadata_value(('adopted', module, key))
                        item['field'] = key
                        row['metadata_fields'].append(item)
                    if self.stream.peek() != ',':
                        break
                    self.stream.expect(',')
            self.stream.expect('}')
            row['direct_field_count'] = len(seen)
        row['original_entry_identity'] = self.stream.end_capture(row_capture)
        return row

    def adopted(self):
        assert not self.adopted_seen, 'duplicate root adopted field'
        self.adopted_seen = True
        self.stream.expect('{')
        seen = set()
        if self.stream.peek() != '}':
            while True:
                module = json_key(self.stream)
                self.account_key(module)
                assert module not in seen, 'duplicate adopted module key'
                seen.add(module)
                if len(seen) > 5000:
                    raise ProjectionBound('adopted key list exceeded its 5000-key bound')
                self.adopted_keys.append(module)
                self.stream.expect(':')
                if module in self.candidates:
                    self.selected[module] = self.selected_entry(module)
                else:
                    walk_value(self.stream)
                if self.stream.peek() != ',':
                    break
                self.stream.expect(',')
        self.stream.expect('}')

    def document(self):
        self.stream.expect('{')
        seen = set()
        if self.stream.peek() != '}':
            while True:
                key = json_key(self.stream)
                self.account_key(key)
                assert key not in seen, 'duplicate root JSON field'
                seen.add(key)
                if len(seen) > 4096:
                    raise ProjectionBound('too many root metadata fields')
                self.root_keys.append(key)
                self.stream.expect(':')
                if key == 'adopted':
                    self.adopted()
                else:
                    item = self.metadata_value((key,))
                    item['field'] = key
                    self.root_fields.append(item)
                if self.stream.peek() != ',':
                    break
                self.stream.expect(',')
        self.stream.expect('}')
        assert self.stream.peek() is None, 'trailing non-whitespace after JSON document'
        self.stream.flush_consumed()
        assert self.adopted_seen, 'root adopted map not present'

    def result(self, complete):
        return {'json_projection_parse_complete': complete,
                'root_keys': self.root_keys,
                'adopted_direct_keys': self.adopted_keys,
                'adopted_direct_key_count': len(self.adopted_keys),
                'candidate_modules': sorted(self.candidates),
                'candidate_keys_seen': sorted(self.candidates.intersection(self.adopted_keys)),
                'selected_metadata_entries_completed': sorted(self.selected),
                'candidate_keys_absent': sorted(self.candidates - set(self.adopted_keys)) if complete else None,
                'selected_entries': self.selected, 'non_adopted_root_metadata': self.root_fields,
                'explicit_JSON_receipt_like_pointers': self.receipt_pointers,
                'receipt_like_pointers_not_dereferenced': True,
                'pointer_bound_omissions': self.pointer_omissions,
                'metadata_capture_bound_omissions': self.metadata_omissions,
                'not_full_actual_import_graph_reception': True,
                'not_kernel_or_owned_qualification': True}


def file_identity(st):
    return {k: getattr(st, k) for k in ('st_dev', 'st_ino', 'st_mode', 'st_size',
                                       'st_mtime_ns', 'st_ctime_ns')}


def file_snapshot(path):
    return {'resolved_path': str(path.resolve(strict=True)),
            'lstat': file_identity(path.lstat()), 'stat': file_identity(path.stat())}


def output_projection(report):
    """A complete bounded projection is sent, never a silent truncated archive."""
    def encoded():
        return json.dumps(report, ensure_ascii=True, indent=2).encode() + b'\n'

    fields = []
    projection = report.get('projection', {})
    fields.extend(projection.get('non_adopted_root_metadata', []))
    for row in projection.get('selected_entries', {}).values():
        fields.extend(row['metadata_fields'])
        if 'non_object_entry' in row:
            fields.append(row['non_object_entry'])
    removable = sorted((field for field in fields if 'original_value_json' in field),
                       key=lambda field: len(field['original_value_json']), reverse=True)
    removed = 0
    raw = encoded()
    while len(raw) > 900000 and removable:
        field = removable.pop(0)
        del field['original_value_json']
        field['original_value_json_captured_complete'] = False
        field['omitted_reason'] = 'bounded_projection_transport'
        removed += 1
        raw = encoded()
    report['transport_metadata_value_omissions'] = removed
    raw = encoded()
    if len(raw) > 1000000:
        # Preserve this failure honestly; never print an over-limit payload.
        meta = {'schema': report['schema'], 'status': 'PROJECTION_TRANSPORT_BOUND_EXCEEDED',
                'full_projection_bytes': len(raw),
                'full_projection_sha256': hashlib.sha256(raw).hexdigest(),
                'full_projection_transmitted': False,
                'input': report.get('input'), 'errors': report.get('errors'),
                'whole_file_sha256_verified': report.get('whole_file_sha256_verified'),
                'new_Lean_invocations': 0, 'remote_filesystem_writes': 0}
        print('P29_ADOPTION_STREAM_META ' + json.dumps(meta, separators=(',', ':')))
        return 4
    manifest = {'PROJECT_ADOPTION_PROJECTION.json': {
        'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}}
    manifest_raw = json.dumps(manifest, sort_keys=True, indent=2).encode() + b'\n'
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode='w:xz', preset=6) as archive:
        for name, payload in [('PROJECT_ADOPTION_PROJECTION.json', raw),
                              ('MANIFEST.json', manifest_raw)]:
            info = tarfile.TarInfo(name)
            info.size, info.mtime, info.mode = len(payload), 0, 0o444
            archive.addfile(info, io.BytesIO(payload))
    packed = buf.getvalue()
    assert len(packed) <= 1350000, 'bounded projection archive limit'
    meta = {'schema': report['schema'], 'status': report['status'],
            'input_path': str(INPUT_PATH), 'input_bytes': report.get('input_bytes_read'),
            'whole_file_sha256': report.get('whole_file_sha256'),
            'whole_file_sha256_verified': report.get('whole_file_sha256_verified'),
            'json_projection_parse_complete': projection.get('json_projection_parse_complete', False),
            'adopted_direct_key_count': projection.get('adopted_direct_key_count'),
            'candidate_keys_seen': projection.get('candidate_keys_seen', []),
            'candidate_keys_absent': projection.get('candidate_keys_absent'),
            'archive_bytes': len(packed), 'archive_sha256': hashlib.sha256(packed).hexdigest(),
            'manifest_sha256': hashlib.sha256(manifest_raw).hexdigest(),
            'archive_members': 2, 'complete_archive_transmitted': True,
            'whole_original_JSON_transmitted': False,
            'metadata_capture_bound_omissions': projection.get('metadata_capture_bound_omissions', 0),
            'transport_metadata_value_omissions': removed,
            'errors': report['errors'], 'new_Lean_invocations': 0,
            'remote_filesystem_writes': 0, 'new_formal_credit': 0}
    output = ('P29_ADOPTION_STREAM_META ' + json.dumps(meta, separators=(',', ':')) + '\n' +
              'P29_ADOPTION_STREAM_ARCHIVE_BASE64 ' + base64.b64encode(packed).decode() + '\n')
    assert len(output.encode()) < 1900000
    sys.stdout.write(output)
    return 0 if not report['errors'] else 1


def main():
    report = {'schema': 'p29_original_project_adoption_stream_projection_v1',
              'script_sha256': hashlib.sha256(globals().get('SOURCE_TEXT', '').encode()).hexdigest(),
              'reused_JsonStream_source_sha256': BASE_JSON_STREAM_FILE_SHA256,
              'candidate_source_record_map_sha256': CANDIDATE_RECORD_MAP_SHA256,
              'candidate_count': len(CANDIDATE_MODULES),
              'expected_file_bytes': EXPECTED_FILE_BYTES,
              'expected_file_sha256': EXPECTED_FILE_SHA256,
              'input_path': str(INPUT_PATH), 'errors': [],
              'new_Lean_invocations': 0, 'remote_filesystem_writes': 0,
              'registry_reads': 0, 'project_object_source_log_reads': 0,
              'receipt_pointer_dereferences': 0, 'new_formal_credit': 0,
              'not_complete_source_object_receiver_qualification': True,
              'not_new_kernel_or_full_owned_audit': True,
              'bounds': {'scalar_chars': 1048576, 'metadata_value_bytes': 65536,
                         'total_metadata_capture_bytes': 4194304, 'adopted_keys': 5000,
                         'retained_key_bytes': 1048576,
                         'receipt_like_pointers': 256, 'receipt_pointer_bytes': 65536,
                         'nesting': 128}}
    reader = collector = None
    parsed = False
    try:
        before = file_snapshot(INPUT_PATH)
        report['input'] = {'before': before}
        assert before == EXPECTED_IDENTITY, 'fixed original adoption identity changed before read'
        with INPUT_PATH.open('rb') as f:
            assert file_identity(os.fstat(f.fileno())) == before['stat']
            reader = HashedUtf8Reader(f, EXPECTED_FILE_BYTES)
            stream = BoundedJsonStream(reader)
            collector = AdoptionProjection(stream, CANDIDATE_MODULES)
            try:
                collector.document()
                parsed = True
                assert stream.consumed_bytes == reader.bytes_read, 'UTF-8 byte accounting mismatch'
            except Exception as exc:
                parsed = False
                report['errors'].append('bounded_JSON_projection: ' + type(exc).__name__ + ': ' + str(exc))
            # After a projection bound/error, finish only the same pass's SHA.
            reader.drain_hash_only()
            report['input']['after_fstat'] = file_identity(os.fstat(f.fileno()))
        after = file_snapshot(INPUT_PATH)
        report['input'].update({'after': after, 'stable_identity': before == after and
                               report['input']['after_fstat'] == before['stat']})
        assert report['input']['stable_identity'], 'original adoption changed during the pass'
        report['input_bytes_read'] = reader.bytes_read
        report['whole_file_sha256'] = reader.digest.hexdigest()
        report['whole_file_sha256_verified'] = (reader.eof and reader.bytes_read == EXPECTED_FILE_BYTES and
                                                reader.digest.hexdigest() == EXPECTED_FILE_SHA256)
        report['first_65536_sha256'] = reader.prefix_digest.hexdigest()
        assert report['whole_file_sha256_verified'], 'original full-file byte count/SHA mismatch'
        assert report['first_65536_sha256'] == EXPECTED_PREFIX_SHA256, 'earlier prefix binding mismatch'
    except Exception as exc:
        report['errors'].append('original_file_binding: ' + type(exc).__name__ + ': ' + str(exc))
    if reader is not None:
        report.setdefault('input_bytes_read', reader.bytes_read)
        report.setdefault('whole_file_sha256', reader.digest.hexdigest())
    report.setdefault('whole_file_sha256_verified', False)
    if collector is not None:
        # A missing candidate is asserted only for a complete parse of the pinned file.
        report['projection'] = collector.result(parsed and report['whole_file_sha256_verified'])
    report['status'] = ('WHOLE_SHA_VERIFIED_BOUNDED_METADATA_PROJECTION' if not report['errors'] else
                        'ORIGINAL_ADOPTION_STREAM_HAS_INCOMPLETE_OR_FAILED_GATES')
    return output_projection(report)


if __name__ == '__main__':
    sys.exit(main())
