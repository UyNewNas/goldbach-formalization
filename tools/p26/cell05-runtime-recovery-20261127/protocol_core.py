"""Small, explicit byte/path and source authentication primitives for recovery v1."""
from pathlib import Path
import hashlib
import importlib.abc
import importlib.util
import json
import os
import stat
import sys


def require(value, message):
    if not value:
        raise ValueError(message)


def canonical(value, exists=True):
    p = Path(value)
    require(p.is_absolute() and '..' not in p.parts and str(p) == str(value), 'Noncanonical path: ' + str(value))
    for q in [*reversed(p.parents), p]:
        if not q.exists() and not q.is_symlink():
            require(not exists, 'Missing path: ' + str(q))
            continue
        mode = q.lstat().st_mode
        require(not stat.S_ISLNK(mode), 'Symlink path: ' + str(q))
        if q != p:
            require(stat.S_ISDIR(mode), 'Non-directory ancestor: ' + str(q))
    return p


def relative(value):
    p = Path(value)
    require(not p.is_absolute() and p.parts and '..' not in p.parts and str(p) == value, 'Unsafe relative path')
    return p


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def stat_id(path):
    s = Path(path).lstat()
    return [s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def read_bytes(path):
    p = canonical(str(path))
    before = stat_id(p)
    require(stat.S_ISREG(before[2]), 'Regular file required: ' + str(p))
    body = p.read_bytes()
    require(stat_id(p) == before, 'File changed while reading: ' + str(p))
    return body


def fp(path):
    return {'path': str(path), **pin(read_bytes(path))}


def same(a, b):
    return all(a.get(k) == b.get(k) for k in ('bytes', 'sha256'))


def read(path):
    return json.loads(read_bytes(path))


def checked(identity, path=None):
    path = str(path if path is not None else identity['path'])
    require(identity.get('path') == path, 'Identity path differs')
    body = read_bytes(path)
    require({'path': path, **pin(body)} == identity, 'File identity differs: ' + path)
    return json.loads(body)


def refs(rows):
    result = {}
    for row in rows:
        require(fp(row['path']) == row, 'Frozen input changed: ' + row['path'])
        require(result.setdefault(row['path'], row) == row, 'Conflicting input pin')
    return [result[p] for p in sorted(result)]


def write_new(path, value):
    path = canonical(str(path), False)
    canonical(str(path.parent))
    with path.open('xb') as f:
        f.write((json.dumps(value, indent=2) + '\n').encode())
        f.flush()
        os.fsync(f.fileno())
    return fp(path)


def protocol_files(here):
    """Authenticate the deliberately small, non-self-referential source manifest."""
    here = canonical(str(here))
    manifest_path = here / 'WORKFLOW_MANIFEST.json'
    manifest = read(manifest_path)
    require(manifest['schema'] == 'p26_runtime_recovery_workflow_v1', 'Unknown recovery workflow')
    rows = manifest['files']
    names = [r['relative_path'] for r in rows]
    require(len(set(names)) == len(names) and names == sorted(names), 'Duplicate/unsorted recovery source')
    require({'recovery.py', 'recovery_worker.py', 'protocol_core.py', 'ANCHORS.json'} <= set(names),
            'Incomplete recovery source manifest')
    require('WORKFLOW_MANIFEST.json' not in names, 'Self-referential recovery manifest')
    result = [fp(manifest_path)]
    for row in rows:
        path = here / relative(row['relative_path'])
        require(path.parent == here and set(row) == {'relative_path', 'bytes', 'sha256'}, 'Unexpected recovery source path')
        identity = fp(path)
        require(same(identity, row), 'Recovery source changed: ' + str(path))
        result.append(identity)
    return sorted(result, key=lambda r: r['path'])


def namespace_snapshot(root):
    root = canonical(str(root))
    require(root.is_dir(), 'Namespace root is not a directory')
    directories, files = [], []
    for folder, dirs, names in os.walk(root, followlinks=False):
        for name in dirs:
            path = canonical(str(Path(folder) / name))
            require(path.is_dir(), 'Special namespace directory')
            directories.append(path.relative_to(root).as_posix())
        for name in names:
            path = canonical(str(Path(folder) / name))
            require(stat.S_ISREG(path.lstat().st_mode), 'Special namespace file')
            files.append(path.relative_to(root).as_posix())
    return {'root': str(root), 'directories': sorted(directories), 'files': sorted(files)}


def authenticate_family(spec):
    """Authenticate all original workflow files before executing any helper."""
    stage = canonical(spec['stage'])
    here = canonical(str(stage / relative(spec['tool_relative_path'])))
    config = checked(spec['verifier'], here / spec['verifier_name'])
    rows = config['workflow_files']
    require(len({r['relative_path'] for r in rows}) == len(rows), 'Duplicate workflow path')
    sources, frozen = {}, [spec['verifier']]
    for row in rows:
        rel = relative(row['relative_path'])
        p = canonical(str(here / rel))
        require(p.is_relative_to(here), 'Workflow path escaped root')
        body = read_bytes(p)
        require(same(pin(body), row), 'Original workflow changed: ' + str(p))
        frozen.append({'path': str(p), **pin(body)})
        if p.suffix == '.py':
            require(rel.parent == Path('.'), 'Unexpected nested executable workflow source')
            require(p.stem not in sources, 'Duplicate helper name')
            sources[p.stem] = (str(p), body)
    require('receipt_checks' in sources and 'runtime_compat' in sources, 'Incomplete original helper family')
    return here, config, sources, frozen


class PinnedSourceLoader(importlib.abc.Loader):
    def __init__(self, path, body):
        self.path, self.body = path, body

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        # No SourceFileLoader/pyc cache lookup: execute these authenticated bytes.
        require(read_bytes(self.path) == self.body, 'Source changed after authentication')
        module.__file__ = self.path
        module.__cached__ = None
        exec(compile(self.body, self.path, 'exec', dont_inherit=True), module.__dict__)


class PinnedSourceFinder(importlib.abc.MetaPathFinder):
    def __init__(self, sources):
        self.sources = dict(sources)
        self.standard = sys.stdlib_module_names | {'__future__'}
        require(not set(self.sources) & set(sys.modules), 'Original helper was imported before authentication')

    def find_spec(self, fullname, path=None, target=None):
        if fullname in self.sources:
            source, body = self.sources[fullname]
            return importlib.util.spec_from_loader(fullname, PinnedSourceLoader(source, body), origin=source)
        require(fullname.split('.')[0] in self.standard, 'Unpinned executable import: ' + fullname)
        return None

    def check_loaded(self):
        for name, (path, body) in self.sources.items():
            if name in sys.modules:
                module = sys.modules[name]
                require(module.__file__ == path and isinstance(module.__loader__, PinnedSourceLoader),
                        'Mixed or cached helper import: ' + name)
                require(read_bytes(path) == body, 'Imported source changed: ' + path)


def deny_worker_mutation(event, args):
    """Workers have no legitimate filesystem mutations or process launches."""
    if event == 'open':
        _, mode, flags = args
        require(not (isinstance(mode, str) and any(c in mode for c in 'wax+')) and
                not (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)),
                'Recovery worker attempted a write')
    require(event not in {'subprocess.Popen', 'os.system', 'os.posix_spawn', 'os.exec', 'os.fork', 'os.forkpty',
                         'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.link', 'os.symlink',
                         'os.chmod', 'os.chown', 'os.utime', 'shutil.copyfile', 'shutil.copymode'},
            'Recovery worker attempted mutation/process launch: ' + event)


def check_prefix_index(context, pilot, stopped, reusable, n, pilot_name, continuation_name):
    modules = [r['module'] for r in context['targets']]
    expected = [(m, mode) for m in modules[:n] for mode in ('normal', 'kernel', 'owned')]
    records = stopped['records']
    require(stopped.get('status') == 'stopped' and 'failed_result' in stopped, 'Missing original failure index')
    require([(r['module'], r['mode']) for r in records] == expected, 'Accepted prefix coverage/order differs')
    require(stopped['newly_executed_steps'] == 3*n-2 and stopped['reused_steps'] == 3, 'Original failed-attempt counters differ')
    require(pilot.get('status') == 'stopped' and pilot.get('reason') == 'new_step_budget' and
            pilot.get('accepted_steps') == 3 and pilot.get('accepted_targets') == 1 and
            pilot.get('newly_executed_steps') == 3 and pilot.get('reused_steps') == 0 and
            pilot.get('whole_geometry_decoded') is False and pilot.get('P2_6_complete') is False,
            'Original pilot boundary differs')
    require([(r['module'], r['mode']) for r in pilot['records']] == expected[:3], 'Pilot records differ')
    objects, steps = {}, []
    for i, row in enumerate(records):
        item = reusable[row['module'], row['mode']]
        require(item is not None and row['accepted'] == item['accepted'], 'Prefix index/seal binding differs')
        require(Path(row['accepted']['path']).parent.parent.name == (pilot_name if i < 3 else continuation_name),
                'Wrong original acceptance attempt')
        require(row['disposition'] == ('reused' if i < 3 else 'executed'), 'Wrong original reuse label')
        if i < 3:
            require(pilot['records'][i]['accepted'] == row['accepted'] and
                    pilot['records'][i]['disposition'] == 'executed', 'Pilot reuse provenance changed')
        obj = item['result']['object']
        require(objects.setdefault(row['module'], obj) == obj, 'Different objects among three checks')
        steps.append(item)
    require(len(objects) == n and len(modules) == n+1 and
            all(reusable[modules[-1], mode] is None for mode in ('normal', 'kernel', 'owned')),
            'Prefix scope or failed-owner acceptance differs')
    return steps, objects
