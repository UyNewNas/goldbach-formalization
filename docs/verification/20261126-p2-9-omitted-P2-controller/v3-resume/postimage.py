import pathlib,os,sys,json,hashlib,subprocess,time,signal,datetime,traceback,shutil,tomllib,importlib.util,urllib.request,base64,re,tarfile,io
from pathlib import Path,PurePosixPath
from datetime import timezone
P=pathlib.Path
sys.dont_write_bytecode=True
OWNED_BASE_CREATED=False
FIXED_CONTRACT_SHA256='1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf'

def sha(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()

def stamp(p):
 s=P(p).stat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def save(p,x):
 p=P(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:json.dump(x,f,indent=2);f.write('\n')

def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()

def get_blob(blob):
 d=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=45))
 assert d['encoding']=='base64'
 b=base64.b64decode(d['content'])
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
 return b

def preserve(p,expected=None):
 p=P(p);s=stamp(p);d=sha(p)
 assert stamp(p)==s
 if expected is not None:assert d==expected,(str(p),'hash mismatch')
 row={'bytes':s[2],'sha256':d};protected[str(p)]=row;cache_before[str(p)]=s
 return row

AUDIT_TEMPLATE='import Lean\nopen Lean\ndef p29ResolvedImports : IO Unit := do\n  initSearchPath (← findSysroot)\n  let names : Array Name := TARGET_MODULE_NAMES\n  let env ← importModules (names.map fun n => { module := n }) {}\n  for idx in [:env.header.modules.size] do\n    let mod := env.header.modules[idx]!\n    let data := env.header.moduleData[idx]!\n    let p ← findOLean mod.module\n    let mut parts : Array System.FilePath := #[p]\n    if data.isModule then\n      parts := parts.push (OLeanLevel.server.adjustFileName p)\n      parts := parts.push (OLeanLevel.private.adjustFileName p)\n    let irSig := p.withExtension "ir.sig"\n    if ← irSig.pathExists then\n      parts := parts.push irSig\n      parts := parts.push (p.withExtension "ir")\n    let partRows ← parts.mapM fun q => do\n      let resolved ← IO.FS.realPath q\n      return Json.mkObj [\n        ("path", toJson q.toString),\n        ("resolved_path", toJson resolved.toString)]\n    IO.println ("P29_ACTUAL_IMPORT " ++ (Json.mkObj [\n      ("module", toJson mod.module.toString),\n      ("is_module", toJson data.isModule),\n      ("direct_imports", toJson (data.imports.map fun i => i.module.toString)),\n      ("parts", toJson partRows)]).compress)\n#eval p29ResolvedImports\n'

def stage(label,command,stdin=None,allow_sources=(),allow_audit=False,timeout=900):
 initial=guardlog.stat().st_size;pos=initial;pending=b'';rows=[];bad=[];started=utc();t0=time.monotonic();last=t0
 log=out/(label+'.log')
 with log.open('xb')as f:
  proc=subprocess.Popen(command,cwd=root,env=base_env,stdin=subprocess.PIPE if stdin is not None else None,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  if stdin is not None:proc.stdin.write(stdin);proc.stdin.close()
  while True:
   with guardlog.open('rb')as g:g.seek(pos);raw=g.read();pos+=len(raw)
   pending+=raw;lines=pending.split(b'\n');pending=lines.pop()
   for line in lines:
    if not line.strip():continue
    row=json.loads(line);rows.append(row)
    if row.get('tool')=='lean':
     args=row.get('input_args',[])
     if '--stdin'in args and not allow_audit:bad.append({'reason':'UNEXPECTED_STDIN_AUDIT','record':row})
     for a in args:
      if str(a).endswith('.lean'):
       q=P(a);q=q if q.is_absolute()else P(row['cwd'])/q
       if str(q.resolve())not in allow_sources and not(allow_audit and q.resolve().is_relative_to(out.resolve())):
        bad.append({'reason':'UNAUTHORIZED_SOURCE_REBUILD','record':row})
   code=proc.poll()
   if code is not None:break
   if bad or time.monotonic()-t0>timeout:
    os.killpg(proc.pid,signal.SIGTERM)
    try:proc.wait(timeout=10)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    code=96 if bad else 124;break
   if time.monotonic()-last>=30:
    print(json.dumps({'stage':label,'root':str(root),'elapsed_seconds':round(time.monotonic()-t0,1),'forbidden_source_calls':len(bad)}),flush=True);last=time.monotonic()
   time.sleep(.2)
 if bad and code==0:code=96
 rec={'stage':label,'command':command,'cwd':str(root),'started_utc':started,'finished_utc':utc(),'exit_code':code,'guard_log_start':initial,'guard_log_end':pos,'guarded_commands':rows,'forbidden_source_calls':bad,'log_path':str(log),'log_sha256':sha(log)}
 if stdin is not None:rec['stdin_sha256']=hashlib.sha256(stdin).hexdigest()
 save(out/(label+'-process.json'),rec);runs.append(rec)
 print(json.dumps({'stage':label,'exit_code':code,'forbidden_source_calls':len(bad),'log_path':str(log)}),flush=True)
 if code:print(log.read_text()[-22000:],flush=True);raise RuntimeError('Gate failed: '+label)
 return rec

def compile_audit_text(module_names):
 names='#['+', '.join(chr(96)+m for m in module_names)+']'
 return AUDIT_TEMPLATE.replace('TARGET_MODULE_NAMES',names).encode()

def named_kernel(label,module_names):
 rec=stage(label,runprefix+['lake','env','leanchecker','--verbose',*module_names])
 replayed=[l.removeprefix('replaying ')for l in (out/(label+'.log')).read_text().splitlines()if l.startswith('replaying ')]
 assert len(replayed)==len(set(replayed))==len(module_names)and set(replayed)==set(module_names)
 return rec

def full_owned(label,module_names):
 code=auditor.make_audit_code(module_names).encode();(out/(label+'.lean')).write_bytes(code)
 rec=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-Dpp.maxSteps=1000000','--stdin'],stdin=code,allow_audit=True)
 decls,inventory,axioms=auditor.read_audit((out/(label+'.log')).read_text(),module_names,rec['exit_code'])
 save(out/(label+'-DECLARATION_TYPES_AXIOMS.json'),decls)
 save(out/(label+'-INVENTORY_NAME_SET_CHECK.json'),inventory)
 return rec,decls,inventory,axioms

def actual_inputs(label,roots,production=None):
 production=production or {}
 code=compile_audit_text(roots);(out/(label+'.lean')).write_bytes(code)
 process=stage(label,runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],stdin=code,allow_audit=True)
 rows=[json.loads(line[len('P29_ACTUAL_IMPORT '):])for line in (out/(label+'.log')).read_text().splitlines()if line.startswith('P29_ACTUAL_IMPORT ')]
 assert rows and len(rows)==len({r['module']for r in rows})and set(roots)<={r['module']for r in rows}
 actual={r['module']:r for r in rows};records=[];counts={};by_facet={}
 for row in rows:
  m=row['module'];assert not m.startswith(('MathlibNt.','PrimeNumberTheoremAnd.','Architect.'))or m in qualified_research,('Unqualified research input',m)
  if m.startswith('ImbalancedChen.'):assert m in borrows or m==target,('Unregistered project module',m)
  for part in row['parts']:
   p=P(part['resolved_path']);requested=P(part['path']);st=stamp(p)
   leaf=m.rsplit('.',1)[-1]
   assert p.name.startswith(leaf+'.')
   facet=p.name[len(leaf):];assert facet in ['.olean','.olean.server','.olean.private','.ir.sig','.ir']
   expected=P(m.replace('.','/')+facet)
   if m in borrows:
    old=borrows[m];assert facet=='.olean'and p.resolve()==P(old['object']).resolve()
    digest=sha(p);assert digest==old['object_sha256']and st[2]==old['object_bytes']
    authority=old['authority'];provider={'original_object':old['original_object']}
   elif m==target:
    assert str(p)in production and production[str(p)]['sha256']==sha(p)
    digest=sha(p);authority='current_normal_output';provider={'normal_source_sha256':source_sha}
   elif (m,facet)in old_by_part:
    known=old_by_part[(m,facet)];assert str(p)==known['identity']['path']
    assert st==known['stat_snapshot']and st[2]==known['identity']['bytes']
    digest=sha(p);assert digest==known['identity']['sha256']
    authority=known['authority'];provider=known['provider']
   elif p.is_relative_to(TOOL_LIB):
    assert p.relative_to(TOOL_LIB)==expected
    digest=sha(p);authority='actual_pinned_lean_release';provider={'lean_commit':LEAN_COMMIT,'toolchain':PIN,'relative_artifact':str(expected)}
   else:
    assert p.parts[-len(expected.parts):]==expected.parts,('Module/path mismatch',m,p)
    libroot=p.parents[len(expected.parts)-1];assert libroot.parts[-4:]==('.lake','build','lib','lean')
    pkg=libroot.parents[3];name=pkg.name
    assert name in package_revisions and name not in ['goldbach','LeanArchitect'],('Unexpected package supplier',m,pkg)
    if str(pkg)not in package_bindings:
     git=lambda *args:subprocess.check_output(['git','-C',str(pkg),*args],text=True).strip()
     assert P(git('rev-parse','--show-toplevel')).resolve()==pkg and git('rev-parse','HEAD')==package_revisions[name]
     package_bindings[str(pkg)]={'name':name,'revision':package_revisions[name],'checkout':str(pkg)}
    digest=sha(p);authority='actual_pinned_mathlib_package';provider={**package_bindings[str(pkg)],'relative_artifact':str(expected)}
   assert stamp(p)==st,('Input changed during hash',p)
   if str(p)in cache_before:assert stamp(p)==cache_before[str(p)],('Previously bound input changed',p)
   else:cache_before[str(p)]=st
   records.append({'module':m,'facet':facet,'identity':{'path':str(p),'bytes':st[2],'sha256':digest},'requested_path':str(requested),'stat_snapshot':st,'authority':authority,'provider':provider})
   counts[authority]=counts.get(authority,0)+1
   assert (m,facet)not in by_facet;by_facet[(m,facet)]=digest
 for m in roots:
  if m in borrows:
   actualdeps={n for n in actual[m]['direct_imports']if n.startswith('ImbalancedChen.')}
   assert actualdeps==set(borrows[m]['direct_project_imports']),(m,actualdeps,borrows[m]['direct_project_imports'])
 for m,r in borrows.items():
  if m not in actual:continue
  for dep,h in r['producer'].get('deps',{}).items():assert by_facet[(dep,'.olean')]==h
 data={'schema':'p29_unit_tail_actual_input_parts_v1','roots':roots,'module_count':len(rows),'part_count':len(records),'counts':counts,'actual_modules':rows,'parts':records,'loading_api':'Lean.importModules; Lean.findOLean; actual module header and default private/server/IR parts','old_vs_new_standard_part_byte_equality_claim':False,'fresh_whole_import_replay_claim':False}
 save(out/(label+'-bindings.json'),data);return data

def stable():
 assert all(sha(p)==h for p,h in configs.items())
 assert sha(state_path)==state_sha
 assert all(sha(p)==h for p,h in tools_expected.items())
 assert all(P(p).stat().st_size==r['bytes']and sha(p)==r['sha256']for p,r in protected.items())
 assert all(P(p).is_file()and stamp(p)==s for p,s in cache_before.items())
 assert all(sha(r['object'])==r['object_sha256']and sha(r['source'])==r['source_sha256']for r in borrows.values())

def source_outputs():
 paths=[src,lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]
 return {str(p):{'bytes':p.stat().st_size,'sha256':sha(p)}for p in paths}

def bind_existing_qualification(data,allow_target=False):
 used=[]
 for part in data['parts']:
  if part['module']==target:
   assert allow_target
   continue
  key=(part['module'],part['facet'])
  assert key in old_by_part,('Input was not in the accepted qualification',key)
  old=old_by_part[key]
  assert part['identity']==old['identity'],('Qualified input identity differs',key,part['identity'],old['identity'])
  assert part['stat_snapshot']==old['stat_snapshot'],('Qualified input stat differs',key)
  used.append(key)
 original_modules={r['module']:r for r in old_inputs['actual_modules']}
 for row in data['actual_modules']:
  if row['module']==target:
   assert allow_target
   assert [m for m in row['direct_imports']if m!='Init']==source_imports
  else:
   old=original_modules[row['module']]
   assert row['is_module']==old['is_module'] and row['direct_imports']==old['direct_imports']
 return len(used)

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def bounded_text(path, maximum=1024 * 1024):
    with path.open('rb') as source:
        raw = source.read(maximum + 1)
    require(len(raw) <= maximum, 'resource metadata exceeds bound: ' + str(path))
    return raw.decode('utf-8')

def absolute_posix(text, label):
    value = PurePosixPath(text)
    require(text.startswith('/') and not text.startswith('//') and
            '..' not in value.parts and str(value) == text,
            'unsupported noncanonical ' + label + ': ' + text)
    return value

def bound_cgroup_v2():
    membership_text = bounded_text(Path('/proc/self/cgroup'), 65536)
    unified = [line for line in membership_text.splitlines() if line.startswith('0::')]
    require(len(unified) == 1, 'one unified cgroup2 membership is required')
    membership = absolute_posix(unified[0].split(':', 2)[2], 'cgroup membership')
    mount_text = bounded_text(Path('/proc/self/mountinfo'))
    cgroup2_rows = [line for line in mount_text.splitlines()
                    if ' - cgroup2 ' in line]
    if not cgroup2_rows:
        require(membership_text == '0::/\n',
                'unexposed fallback requires the exact observed unified root membership')
        binding = {'resource_mode': 'SERVICE_SAMPLED_RSS_CGROUPFS_UNEXPOSED',
                   'proc_self_cgroup_text': membership_text,
                   'unified_membership': str(membership),
                   'cgroup_namespace': os.readlink('/proc/self/ns/cgroup'),
                   'pid_namespace': os.readlink('/proc/self/ns/pid'),
                   'self_pid': os.getpid(),
                   'mountinfo_bytes': len(mount_text.encode()),
                   'mountinfo_sha256': hashlib.sha256(mount_text.encode()).hexdigest(),
                   'cgroup2_mountinfo_rows': [],
                   'cgroup_budget_visibility': 'UNKNOWN_CGROUPFS_NOT_EXPOSED'}
        return None, None, binding
    candidates = []
    for line in mount_text.splitlines():
        left, separator, right = line.partition(' - ')
        if not separator or right.split()[0] != 'cgroup2':
            continue
        fields = left.split()
        require(len(fields) >= 6, 'invalid cgroup2 mountinfo')
        decode = lambda value: re.sub(r'\\([0-7]{3})',
                                      lambda match: chr(int(match.group(1), 8)), value)
        root = absolute_posix(decode(fields[3]), 'cgroup2 mount root')
        mount = Path(str(absolute_posix(decode(fields[4]), 'cgroup2 mount point')))
        # A subtree-only or namespace-misaligned mount cannot expose every
        # visible ancestor; stop unless a namespace-root mount is available.
        if root != PurePosixPath('/'):
            continue
        resolved_mount = mount.resolve(strict=True)
        group = mount.joinpath(*membership.relative_to(root).parts).resolve(strict=True)
        require(group.is_relative_to(resolved_mount), 'mapped cgroup escaped its mount')
        info = group.stat()
        require(str(os.major(info.st_dev)) + ':' + str(os.minor(info.st_dev)) == fields[2],
                'mapped cgroup device does not match mountinfo')
        candidates.append({'group': group, 'mount': resolved_mount, 'line': line,
                           'root': str(root), 'device': info.st_dev, 'inode': info.st_ino})
    require(candidates, 'no supported cgroup2 namespace-root mount maps this process')
    require(len({(item['device'], item['inode']) for item in candidates}) == 1,
            'cgroup2 mounts map this process to different groups')
    candidate = sorted(candidates, key=lambda item: (len(str(item['mount'])), str(item['mount'])))[0]
    group, mount = candidate['group'], candidate['mount']
    require(bounded_text(group / 'cgroup.type', 65536).strip() == 'domain',
            'only an ordinary cgroup2 domain is supported')
    procs = bounded_text(group / 'cgroup.procs')
    require(str(os.getpid()) in procs.split(),
            'mapped cgroup.procs does not contain the actual launcher PID')
    namespace = os.readlink('/proc/self/ns/cgroup')
    mount_stat = mount.stat()
    binding = {'proc_self_cgroup_text': membership_text,
               'unified_membership': str(membership),
               'cgroup_namespace': namespace, 'selected_mountinfo_line': candidate['line'],
               'mount_root': candidate['root'], 'resolved_mount_point': str(mount),
               'resolved_process_cgroup': str(group),
               'group_device': candidate['device'], 'group_inode': candidate['inode'],
               'mount_device': mount_stat.st_dev, 'mount_inode': mount_stat.st_ino,
               'self_pid': os.getpid(), 'self_pid_present_in_mapped_cgroup_procs': True,
               'ancestor_scope': 'All visible ancestors through this verified cgroup namespace root; no claim about hidden host ancestors.'}
    return group, mount, binding

def service_observation():
    raw = globals().get('SERVICE_OBSERVATION_JSON')
    expected = globals().get('SERVICE_OBSERVATION_SHA256')
    require(isinstance(raw, str) and len(raw.encode()) <= 65536,
            'bounded external SERVICE_OBSERVATION JSON is required')
    require(isinstance(expected, str) and len(expected) == 64 and
            hashlib.sha256(raw.encode()).hexdigest() == expected,
            'SERVICE_OBSERVATION raw JSON SHA differs')
    document = json.loads(raw)
    require(document['schema'] == 'p29_timestamped_service_observation_v1' and
            document['source_tool'] == 'mcp__codex_apps__cloud_compile_private_8e1da5a7_system_info',
            'unexpected service observation schema or tool')
    limits = {'memory_mb': MCP_MEMORY_MB, 'cpu_threads': MCP_CPU_THREADS,
              'timeout_seconds': MCP_TIMEOUT_SECONDS}
    require(document['requested_MCP_limits'] == limits and
            document['submission_observation_max_age_seconds'] == 300,
            'service observation does not bind the exact request and submission window')
    before = datetime.datetime.strptime(document['clock_before']['current_time'],
                               '%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=timezone.utc)
    after = datetime.datetime.strptime(document['clock_after']['current_time'],
                              '%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=timezone.utc)
    require(0 <= (after - before).total_seconds() <= 300,
            'invalid bracketed service observation clock interval')
    response = document['system_info_raw_tool_response']
    require(not response.get('isError', False), 'system_info returned an error')
    data = response.get('structuredContent')
    if data is None:
        text_items = [item['text'] for item in response.get('content', [])
                      if item.get('type') == 'text']
        require(len(text_items) == 1, 'system_info must have one JSON text result')
        data = json.loads(text_items[0])
    require(isinstance(data, dict), 'system_info data is not an object')
    require(data['enforcement'] ==
            'CPU affinity; aggregate process-tree RSS sampled every 50 ms; PID namespace teardown' and
            data['memory_sampling_seconds'] == 0.05 and data['cgroup_writable'] is False,
            'observed service enforcement contract differs')
    require(data['memory_quota_bytes'] == 17179869184 and
            data['effective_memory_bytes'] == 17179869184 and
            data['max_job_memory_mb'] == OBSERVED_MCP_MAX_MEMORY_MB and
            data['allocated_cpu_threads'] == 4 and data['cgroup_cpu_quota_cores'] == 4,
            'observed service capacity contract differs')
    queue = data['queue']
    require(queue['concurrency'] == 1 and queue['queue_limit'] == 8 and
            isinstance(queue['queued_task_ids'], list) and
            len(queue['queued_task_ids']) < queue['queue_limit'] and
            (queue['active_task_id'] is None or
             (isinstance(queue['active_task_id'], str) and bool(queue['active_task_id']))),
            'service single-worker queue has no waiting slot or malformed observation')
    require(MCP_MEMORY_MB <= data['max_job_memory_mb'] and
            MCP_MEMORY_MB * 1024 * 1024 <= data['effective_memory_bytes'] and
            MCP_CPU_THREADS <= data['allocated_cpu_threads'],
            'request exceeds observed service capacity')
    return {'sha256': expected, 'document': document, 'observation': data,
            'clock_before': document['clock_before'],
            'clock_after': document['clock_after'],
            'runtime_seconds_after_observation': (datetime.datetime.now(timezone.utc) - after).total_seconds(),
            'freshness_scope': 'Submission-time observation only; controller and later actual get_task submitted_at must establish the 300-second window. Runtime host/affinity/disk are measured separately.'}

def resources_unexposed(binding):
    service = service_observation()
    binding = dict(binding, service_observation_sha256=service['sha256'])
    meminfo = {line.split(':', 1)[0]: line.split(':', 1)[1].strip().split()
               for line in bounded_text(Path('/proc/meminfo')).splitlines()}
    require(meminfo['MemAvailable'][1] == 'kB', 'unsupported MemAvailable unit')
    host_available = int(meminfo['MemAvailable'][0]) * 1024
    disk = os.statvfs(ROOT)
    free_disk = disk.f_bavail * disk.f_frsize
    result = {'cgroup_binding': binding,
              'resource_mode': 'SERVICE_SAMPLED_RSS_CGROUPFS_UNEXPOSED',
              'service_observation': service,
              'cgroup_memory_max_current_cache_budget': None,
              'environment_cgroup_budget_is_unknown_in_task_namespace': True,
              'service_environment_headroom_and_available_are_observations_only': True,
              'service_environment_headroom_used_as_runtime_admission_gate': False,
              'no_host_cache_or_invented_active_file_added_to_environment_budget': True,
              'host_MemAvailable_bytes': host_available,
              'host_memory_sampling_time_utc': datetime.datetime.now(timezone.utc).isoformat(),
              'free_disk_bytes': free_disk, 'required_disk_floor_bytes': DISK_FLOOR,
              'cpu_affinity_count': len(os.sched_getaffinity(0)),
              'requested_MCP_limits': {'memory_mb': MCP_MEMORY_MB, 'cpu_threads': MCP_CPU_THREADS,
                                       'timeout_seconds': MCP_TIMEOUT_SECONDS},
              'inner_Lean_audit_memory_mb': INNER_AUDIT_MEMORY_MB,
              'memory_enforcement_scope': 'Service samples aggregate process-tree RSS every 50ms and can terminate the PID namespace; this is not a per-task cgroup hard memory ceiling.',
              'passing_host_and_contract_checks_is_not_environment_capacity_or_OOM_guarantee': True,
              'no_memory_reservation_or_completion_guarantee': True,
              'actual_MCP_limits_require_later_get_task_receipt_join': True}
    current_mount_text = bounded_text(Path('/proc/self/mountinfo'))
    require(bounded_text(Path('/proc/self/cgroup'), 65536) == binding['proc_self_cgroup_text'] and
            os.readlink('/proc/self/ns/cgroup') == binding['cgroup_namespace'] and
            os.readlink('/proc/self/ns/pid') == binding['pid_namespace'] and
            hashlib.sha256(current_mount_text.encode()).hexdigest() == binding['mountinfo_sha256'] and
            not any(' - cgroup2 ' in line for line in current_mount_text.splitlines()),
            'unexposed namespace/mount binding changed during resource check')
    require(MCP_MEMORY_MB <= OBSERVED_MCP_MAX_MEMORY_MB, 'request exceeds observed MCP per-job memory maximum')
    require(INNER_AUDIT_MEMORY_MB < MCP_MEMORY_MB, 'no process-wrapper memory margin')
    require(host_available >= MCP_MEMORY_MB * 1024 * 1024,
            'insufficient actual host MemAvailable for requested process budget: ' + json.dumps(result))
    require(free_disk >= DISK_FLOOR, 'insufficient current audit disk reserve: ' + json.dumps(result))
    require(result['cpu_affinity_count'] >= MCP_CPU_THREADS, 'insufficient CPU affinity')
    return result

def resources():
    group, mount, binding = bound_cgroup_v2()
    if group is None:
        return resources_unexposed(binding)
    levels, finite_limits, adjusted_budgets, cpu_limits = [], [], [], []
    current_group = group
    while True:
        require(len(levels) < 128, 'cgroup hierarchy exceeds supported depth')
        row = {'path': str(current_group)}
        max_path = current_group / 'memory.max'
        if not max_path.exists():
            require(current_group == mount,
                    'memory controller is not exposed below the namespace-root mount')
            row['memory_limit_files'] = 'NOT_EXPOSED_AT_MOUNT_ROOT'
        else:
            maximum_text = bounded_text(max_path, 65536).strip()
            maximum = None if maximum_text == 'max' else int(maximum_text)
            current = int(bounded_text(current_group / 'memory.current', 65536).strip())
            memory_stat = {key: int(value) for key, value in
                           (line.split() for line in bounded_text(current_group / 'memory.stat').splitlines())}
            required = ('file', 'shmem', 'file_dirty', 'file_writeback', 'unevictable')
            require(all(key in memory_stat and memory_stat[key] >= 0 for key in required),
                    'required cache accounting fields are missing or negative')
            require(current >= 0 and (maximum is None or maximum > 0),
                    'invalid cgroup memory counters')
            excluded = sum(memory_stat[key] for key in required[1:])
            reclaimable = max(0, memory_stat['file'] - excluded)
            row.update({'memory_max_raw': maximum_text, 'memory_max_bytes': maximum,
                        'memory_current_bytes': current, 'memory_stat_raw': memory_stat,
                        'cache_deductions_bytes': {key: memory_stat[key] for key in required[1:]},
                        'cache_deductions_can_overlap_conservatively': True,
                        'estimated_regular_clean_evictable_file_cache_bytes': reclaimable})
            if maximum is not None:
                estimate = min(maximum, max(0, maximum - current + reclaimable))
                finite_limits.append(maximum)
                adjusted_budgets.append(estimate)
                row.update({'raw_headroom_bytes': max(0, maximum - current),
                            'reclaim_adjusted_budget_estimate_bytes': estimate})
        cpu_path = current_group / 'cpu.max'
        if cpu_path.exists():
            quota_text = bounded_text(cpu_path, 65536).strip()
            quota, period_text = quota_text.split()
            period = int(period_text)
            require(period > 0 and (quota == 'max' or int(quota) > 0), 'invalid cpu.max')
            row['cpu_max_raw'] = quota_text
            if quota != 'max':
                cpu_limits.append((int(quota), period))
        else:
            require(current_group == mount, 'cpu controller is not exposed below mount root')
            row['cpu_limit_files'] = 'NOT_EXPOSED_AT_MOUNT_ROOT'
        levels.append(row)
        if current_group == mount:
            break
        current_group = current_group.parent
        require(current_group.is_relative_to(mount), 'ancestor walk escaped cgroup2 mount')
    require(finite_limits, 'no finite visible cgroup memory maximum is exposed')
    meminfo = {line.split(':', 1)[0]: line.split(':', 1)[1].strip().split()
               for line in bounded_text(Path('/proc/meminfo')).splitlines()}
    require(meminfo['MemAvailable'][1] == 'kB', 'unsupported MemAvailable unit')
    host_available = int(meminfo['MemAvailable'][0]) * 1024
    effective_maximum = min(finite_limits)
    effective_budget = min([host_available, *adjusted_budgets])
    disk = os.statvfs(ROOT)
    free_disk = disk.f_bavail * disk.f_frsize
    result = {'cgroup_binding': binding, 'visible_cgroup_levels_leaf_to_root': levels,
              'visible_cgroup_effective_memory_max_bytes': effective_maximum,
              'host_MemAvailable_bytes': host_available,
              'reclaim_adjusted_process_budget_estimate_bytes': effective_budget,
              'reclaim_estimate_is_not_memory_reservation_or_guarantee': True,
              'resource_reads_are_live_samples_not_atomic_snapshots': True,
              'free_disk_bytes': free_disk, 'required_disk_floor_bytes': DISK_FLOOR,
              'cpu_affinity_count': len(os.sched_getaffinity(0)),
              'requested_MCP_limits': {'memory_mb': MCP_MEMORY_MB, 'cpu_threads': MCP_CPU_THREADS,
                                       'timeout_seconds': MCP_TIMEOUT_SECONDS},
              'observed_MCP_max_memory_mb': OBSERVED_MCP_MAX_MEMORY_MB,
              'inner_Lean_audit_memory_mb': INNER_AUDIT_MEMORY_MB}
    require(bounded_text(Path('/proc/self/cgroup'), 65536) == binding['proc_self_cgroup_text'] and
            os.readlink('/proc/self/ns/cgroup') == binding['cgroup_namespace'] and
            binding['selected_mountinfo_line'] in bounded_text(Path('/proc/self/mountinfo')).splitlines(),
            'cgroup membership, namespace or mount changed during resource check')
    require(MCP_MEMORY_MB <= OBSERVED_MCP_MAX_MEMORY_MB, 'request exceeds observed MCP per-job memory maximum')
    require(INNER_AUDIT_MEMORY_MB < MCP_MEMORY_MB, 'no process-wrapper memory margin')
    require(effective_maximum >= MCP_MEMORY_MB * 1024 * 1024, 'visible cgroup hard limit is below requested process budget')
    require(effective_budget >= MCP_MEMORY_MB * 1024 * 1024,
            'insufficient current host/cgroup reclaim-adjusted budget estimate: ' + json.dumps(result))
    require(free_disk >= DISK_FLOOR, 'insufficient current audit disk reserve: ' + json.dumps(result))
    require(result['cpu_affinity_count'] >= MCP_CPU_THREADS, 'insufficient CPU affinity')
    require(all(quota >= period * MCP_CPU_THREADS for quota, period in cpu_limits),
            'visible cgroup CPU quota is below requested thread allocation')
    return result

# This file is concatenated after the byte-identical fourteen reviewed helpers.
# It never invokes an old supplier source, named kernel, or owned-declaration audit.

def canonical(value):
 return json.dumps(value,sort_keys=True,separators=(',',':')).encode()

def fixed_bytes(data,rec):
 assert len(data)==rec['bytes'] and hashlib.sha256(data).hexdigest()==rec['sha256']
 if 'git_blob'in rec:assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==rec['git_blob']
 return data

def authority_file(label,rec):
 # All authority records were already captured before the original failure.
 p=previous_out/'original-authorities'/label
 assert p.is_file() and not p.is_symlink(),('Missing original cached authority',label)
 before=stamp(p);data=p.read_bytes();assert stamp(p)==before
 fixed_bytes(data,rec);cache_before[str(p)]=before
 p=out/'original-authorities'/label;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as f:f.write(data)
 preserve(p,rec['sha256'])
 return data

def capture_members(archive,wanted,destination):
 # Only the named original members are materialized. The full compressed
 # archive is authenticated, but no old actual graph is parsed or replayed.
 found={}
 with tarfile.open(fileobj=io.BytesIO(archive),mode='r:xz')as tf:
  for member in tf:
   if member.name not in wanted:continue
   assert member.name not in found and member.isfile() and not member.issym() and not member.islnk()
   pin=wanted[member.name];assert member.size==pin['bytes']
   data=tf.extractfile(member).read();fixed_bytes(data,pin)
   dest=destination/member.name;dest.parent.mkdir(parents=True,exist_ok=True)
   with dest.open('xb')as f:f.write(data)
   preserve(dest,pin['sha256']);found[member.name]=dest
 assert set(found)==set(wanted),('Missing selected original member',sorted(set(wanted)-set(found)))
 return found

def bind_original_schema1(accepted,records):
 assert accepted['schema']=='p29_two_root_original_schema1_root_semantic_acceptance_v1'
 assert accepted['status']=='PASS_EXACT_ORIGINAL_NORMAL_NAMED_KERNEL_FULL_OWNED_RECEIPTS'
 assert accepted['original_audit_job']=='7981839ec960464d913d5ee2b3a18175'
 assert accepted['new_manuscript_credit']==0
 assert accepted['external_snapshot_sha256']==contract['external_snapshot_sha256']
 summary={}
 for mod,pin in accepted['roots'].items():
  assert pin['root_accepted_for_reuse']is True and pin['owned']==contract['root_owned_counts'][mod]
  assert pin['normal_exit_code']==pin['named_kernel_exit_code']==pin['full_owned_exit_code']==0
  assert pin['normal_log_bytes']==0
  rec=records[mod]
  assert hashlib.sha256(canonical(rec)).hexdigest()==pin['normal_record_sha256']
  assert rec['exit_code']==0 and rec['source_sha256']==pin['source_sha256'] and rec['object_sha256']==pin['object_sha256']
  assert rec['closure_signature']==pin['closure_signature']
  relative=P(pin['receipt_member']).relative_to('project')
  original=P(contract['old_P2_project_root'])/relative
  data=authority_file('schema1/'+mod+'/receipt.json',{'path':str(original),'bytes':contract['schema1_receipt_sizes'][mod],'sha256':pin['receipt_sha256']})
  receipt=json.loads(data)
  assert receipt['schema']==1 and receipt['accepted']is True and receipt['module']==mod
  assert receipt['source_sha256']==pin['source_sha256'] and receipt['object_sha256']==pin['object_sha256']
  assert receipt['compile_closure_signature']==pin['closure_signature']
  assert receipt['input_sha256']==pin['input_snapshot_sha256']==hashlib.sha256(canonical(receipt['input_snapshot'])).hexdigest()
  snapshot=receipt['input_snapshot'];assert len(snapshot['project'])==pin['frozen_project_count']
  assert snapshot['external_snapshot']['snapshot_sha256']==contract['external_snapshot_sha256']
  assert receipt['replay_binding']=={k:snapshot[k]for k in ['project','toolchain','lean_binary_sha256','leanchecker_sha256','external_snapshot']}
  for module,frozen in snapshot['project'].items():
   row=records[module]
   assert frozen=={k:row[k]for k in ['source','source_sha256','object','object_sha256']}
  replay=receipt['replay'];audit=receipt['audit']
  assert replay['exit_code']==audit['exit_code']==0 and replay['inputs_unchanged']is True and audit['inputs_unchanged']is True
  assert replay['command']==[str(TC/'bin/leanchecker'),'--verbose',mod]
  assert audit['declaration_count']==pin['owned'] and audit['axiom_counts']==pin['axiom_counts']
  assert audit['command']==[str(TC/'bin/lean'),'-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000',audit['source']]
  assert receipt['artifacts'][replay['log']]==replay['log_sha256']
  assert receipt['artifacts'][audit['log']]==audit['log_sha256']
  assert receipt['artifacts'][audit['source']]==audit['source_sha256']
  for rel,digest in receipt['artifacts'].items():
   p=P(contract['old_P2_project_root'])/rel
   assert p.is_relative_to(original.parent) and p.name in ['replay.log','audit.log','Audit.lean','declarations.json','types.txt']
   authority_file('schema1/'+mod+'/'+p.name,{'path':str(p),'bytes':p.stat().st_size,'sha256':digest})
  assert set(P(p).name for p in receipt['artifacts'])=={'replay.log','audit.log','Audit.lean','declarations.json','types.txt'}
  normal_log=P(contract['old_P2_project_root'])/rec['log']
  authority_file('schema1/'+mod+'/original-normal.log',{'path':str(normal_log),'bytes':0,'sha256':hashlib.sha256(b'').hexdigest()})
  replay_lines=(out/'original-authorities/schema1'/mod/'replay.log').read_text().splitlines()
  assert [l.removeprefix('replaying ')for l in replay_lines if l.startswith('replaying ')]==[mod]
  types=out/'original-authorities/schema1'/mod/'types.txt'
  assert types.stat().st_size==pin['types_bytes'] and sha(types)==pin['types_sha256']
  summary[mod]={'root_acceptance':contract['authorities']['two_root_acceptance'],'original_schema':1,'receipt_sha256':pin['receipt_sha256'],'input_snapshot_sha256':pin['input_snapshot_sha256'],'normal_record_sha256':pin['normal_record_sha256'],'source_sha256':pin['source_sha256'],'object_sha256':pin['object_sha256'],'closure_signature':pin['closure_signature'],'owned':pin['owned'],'normal_exit_code':0,'named_kernel_exit_code':0,'full_owned_exit_code':0,'original_full_types_sha256':pin['types_sha256'],'new_normal_kernel_owned_invocations':0,'root_acceptance_reused_not_reparsed_owned_logs':True,'whole_standard_import_kernel_replay_claim':False}
 return summary

def assert_expected_current_map(data):
 # The raw external snapshot had bytes/paths, not compiled headers. This
 # guarded import is the first current header/complete-facet capture.
 seen=set();origin_counts={}
 for part in data['parts']:
  key=(part['module'],part['facet']);assert key not in seen;seen.add(key)
  assert key in expected_origins,('Previously undescribed actual input',key)
  known=expected_origins[key];identity=part['identity']
  assert identity['bytes']==known['bytes'] and identity['sha256']==known['sha256'],('Actual bytes differ from accepted origin',key)
  assert identity['path']==str(P(known['path']).resolve()),('Unselected physical input',key,identity['path'],known['path'])
  origin_counts[known['origin']]=origin_counts.get(known['origin'],0)+1
 actual_modules={row['module']:row for row in data['actual_modules']}
 assert len(actual_modules)==data['module_count']
 actual_project={m for m in actual_modules if m.startswith('ImbalancedChen.')}
 assert actual_project==set(borrows) and len(actual_project)==58
 for mod,row in borrows.items():
  direct={m for m in actual_modules[mod]['direct_imports']if m.startswith('ImbalancedChen.')}
  assert direct==set(row['direct_project_imports'])
  assert actual_modules[mod]['is_module']is False
  assert {(m,f)for m,f in seen if m==mod}=={(mod,'.olean')}
  for dep,digest in row['producer']['deps'].items():assert expected_origins[(dep,'.olean')]['sha256']==digest
 assert {p['module']for p in data['parts']}==set(actual_modules)
 save(out/'CURRENT_INPUT_ORIGIN_BINDING.json',{'schema':'p29_omitted_current_compiled_headers_and_facets_bound_to_accepted_bytes_v1','status':'PASS_CURRENT_HEADER_FACET_IMPORT_UNION','actual_bindings_sha256':sha(out/'omitted-direct-imports-bindings.json'),'module_count':data['module_count'],'part_count':data['part_count'],'project_modules':sorted(actual_project),'origin_counts':origin_counts,'approved_byte_origin_table_size':len(expected_origins),'all_current_parts_exact_accepted_bytes_and_selected_paths':True,'first_current_headers_captured_by_original_Lean_importModules_probe':True,'original_ad438_compiled_headers_claim':False,'original_qualification_files_unchanged':True,'supplier_source_kernel_owned_replays':0,'formal_credit':0})
 return len(seen)

def main():
 global contract,CONTRACT_SHA256,base,root,out,target,source_blob,source_sha,source,source_imports,src,lib,protected,cache_before,runs,borrows,old_by_part,old_inputs,qualified_research,expected_origins,configs,tools_expected,GUARD,RUNNER,OWNED,PIN,LEAN_COMMIT,TC,TOOL_LIB,base_env,state_path,state_sha,guardlog,state,runprefix,auditor,package_revisions,package_bindings,ROOT,DISK_FLOOR,MCP_MEMORY_MB,MCP_CPU_THREADS,MCP_TIMEOUT_SECONDS,OBSERVED_MCP_MAX_MEMORY_MB,INNER_AUDIT_MEMORY_MB,OWNED_BASE_CREATED,previous_out
 raw=globals()['INPUT_CONTRACT_TEXT'];CONTRACT_SHA256=FIXED_CONTRACT_SHA256
 assert isinstance(raw,str) and hashlib.sha256(raw.encode()).hexdigest()==CONTRACT_SHA256
 contract=json.loads(raw)
 assert contract['schema']=='p29_omitted_P2_concrete_single_target_contract_v1'
 assert contract['receiver_root']=='/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77'
 target=contract['target']['module'];source_blob=contract['target']['source_git_blob'];source_sha=contract['target']['source_sha256']
 assert target=='ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall' and source_blob=='ef40c77ee9b4c58a8e4761b21fafdfe867f85d8e'
 assert source_sha=='4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c'
 base=P(contract['receiver_root']);root=base/'project';previous_out=base/'verification';out=base/'verification-import-order-resume-v3'
 assert base.is_dir() and root.is_dir() and previous_out.is_dir()
 assert not out.exists(),'This exact resume already has evidence; do not repeat it.'
 previous_pins={'driver.py':'945a19ceecfd707c5fa801ca9ce4f170755c9bbe363079293198e40bacc09970','INPUT_CONTRACT.json':'1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf','FAILURE.json':'2c0e2b27ce353d0da8d4a268b11a7edc03e7e017fdd7c3c70adf40c13e74942d'}
 for name,pin in previous_pins.items():assert sha(previous_out/name)==pin
 previous_failure=json.loads((previous_out/'FAILURE.json').read_text())
 assert previous_failure['completed_stages']==[] and previous_failure['supplier_source_kernel_owned_replays']==0
 assert previous_failure['partial_target_outputs_preserved']=={str(root/(target.replace('.','/')+'.lean')):{'bytes':7887,'sha256':source_sha}}
 assert globals().get('SOURCE_TEXT') and hashlib.sha256(SOURCE_TEXT.encode()).hexdigest()==globals()['SOURCE_SHA256']
 ROOT=P('/workspace');MCP_MEMORY_MB=12800;MCP_CPU_THREADS=2;MCP_TIMEOUT_SECONDS=3600;OBSERVED_MCP_MAX_MEMORY_MB=13107;INNER_AUDIT_MEMORY_MB=12288
 assert contract['MCP_limits']=={'memory_mb':MCP_MEMORY_MB,'cpu_threads':MCP_CPU_THREADS,'timeout_seconds':MCP_TIMEOUT_SECONDS}
 capacity=contract['capacity'];assert sum(capacity['components_bytes'].values())==capacity['peak_new_output_bytes']
 DISK_FLOOR=capacity['peak_new_output_bytes']+capacity['minimum_remaining_free_bytes']
 initial_resources=resources()
 # Everything above is read-only. A resource stop never starts a retry.
 out.mkdir();OWNED_BASE_CREATED=True
 protected={};cache_before={};runs=[]
 (out/'driver.py').write_text(SOURCE_TEXT);(out/'INPUT_CONTRACT.json').write_text(raw)
 (out/'SERVICE_OBSERVATION.json').write_text(globals()['SERVICE_OBSERVATION_JSON'])
 save(out/'CAPACITY_BEFORE_NEW_WRITES.json',initial_resources)
 save(out/'ORIGINAL_PRE_LEAN_FAILURE_REUSE.json',{'schema':'p29_omitted_same_root_pre_Lean_import_order_resume_v1','original_job_id':'1dfcb781103d4426b860b7ffe3ebc8cd','original_evidence':str(previous_out),'original_file_sha256':previous_pins,'original_failure':previous_failure,'cached_original_authorities_normal_records_target_source_reused':True,'old_Lean_stages_replayed':0,'original_failed_evidence_not_modified':True})
 for name,pin in previous_pins.items():preserve(previous_out/name,pin)
 PIN='leanprover/lean4:v4.33.0-rc1';LEAN_COMMIT='62eed1db4d67327ec8120be05f1a1b0847d74561'
 TC=P('/workspace/toolchains/lean-4.33.0-rc1-linux');TOOL_LIB=(TC/'lib/lean').resolve()
 for name,pin in contract['runtime_sha256'].items():preserve(TC/'bin'/name,pin)
 references={label:authority_file(label+'.json',rec)for label,rec in contract['authorities'].items()}
 accepted=json.loads(references['two_root_acceptance'])
 projection=json.loads(references['project_projection']);selected=projection['selected_modules']
 assert projection['target']==target and projection['target_source_blob']==source_blob and len(selected)==58
 receive=json.loads(references['P2_received18'])
 assert receive['status']=='PASS_EXACT_BYTES_ONLY_NOT_MATHEMATICAL_OR_ACTUAL_IMPORT_QUALIFICATION' and len(receive['selected_objects'])==18
 binding=json.loads(references['P2_received18_path_binding'])
 assert binding['schema']=='p29_omitted18_exact_terminal_transport_binding_v1' and binding['status']=='PASS_BYTE_RECEPTION_ONLY'
 assert binding['complete_receipt']['sha256']==contract['authorities']['P2_received18']['sha256'] and binding['exact_pin_comparisons_passed']==18
 received={r['module']:r for r in binding['selected_objects']}
 assert len(received)==18 and set(received)==set(receive['selected_objects'])
 for mod,row in received.items():
  original=receive['selected_objects'][mod]
  assert row['path']==original['selected_path'] and row['stat']==original['final_stat']
  assert row['bytes']==original['bytes'] and row['sha256']==original['sha256'] and row['selection']==original['selection']
  assert row['source']==original['source_received'] if 'source'in row else 'source_received'not in original
  assert row['kind']==('foreign_project'if mod.startswith('ImbalancedChen.')else'native')
 save(out/'P2_RECEIVED18_RAW_TO_PATH_BINDING.json',{'schema':'p29_original_receipt_to_exact_current_path_view_v1','raw_receipt_sha256':contract['authorities']['P2_received18']['sha256'],'path_binding_sha256':contract['authorities']['P2_received18_path_binding']['sha256'],'all18_selected_paths_bytes_sha256_stat_source_records_identical':True,'original_receipt_rewritten':False})
 receive_root=json.loads(references['P2_received18_root_acceptance'])
 assert contract['P2_reception_receipt_sha256']==contract['authorities']['P2_received18']['sha256']=='855300937a4938f0a83fa1127476abd87263161d51a885ef4fad86a5a693838b'
 nonunit=json.loads(references['Nonunit_root_acceptance'])
 assert nonunit['status']=='ROOT_ACCEPTED_EXACT_NORMAL_KERNEL_FULL_OWNED_AND_COMPLETE_81_MEMBER_ARCHIVE' and nonunit['owned']==17
 assert nonunit['normal_exit']==nonunit['named_kernel_exit']==nonunit['full_owned_exit']==0
 assert nonunit['source_sha256']==selected[nonunit['module']]['source_sha256'] and nonunit['object_sha256']==selected[nonunit['module']]['object_sha256']
 original_P1_project_rows=json.loads(references['original_P1_profile_project_rows'])['objects']
 for label,rec in receive['authorities'].items():authority_file('received18/'+label+'.json',rec)
 normal_member='SELECTED_ORIGINAL_NORMAL_RECORDS.json';cached_normal=previous_out/'original-normal-records'/normal_member
 before=stamp(cached_normal);normal_raw=cached_normal.read_bytes();assert stamp(cached_normal)==before
 fixed_bytes(normal_raw,contract['normal_records_members'][normal_member]);cache_before[str(cached_normal)]=before
 normal_copy=out/'original-normal-records'/normal_member;normal_copy.parent.mkdir(parents=True);normal_copy.write_bytes(normal_raw)
 records=json.loads(normal_raw)
 assert len(records)==54 and set(records)=={m for m,r in selected.items()if r['origin']=='P2_saving16_original_normal_record'}
 authority_summaries=bind_original_schema1(accepted,records)
 existing_source=root/(target.replace('.','/')+'.lean')
 before=stamp(existing_source);source=fixed_bytes(existing_source.read_bytes(),{'bytes':7887,'sha256':source_sha,'git_blob':source_blob});assert stamp(existing_source)==before
 source_imports=re.findall(r'^import\s+(\S+)',source.decode(),re.M)
 assert source_imports==contract['target']['direct_imports']
 src=existing_source;cache_before[str(src)]=before
 lib=root/'.lake/build/lib/lean';assert lib.is_dir()
 borrows={}
 for mod,pin in selected.items():
  if mod in records:
   rec=records[mod]
   assert rec['exit_code']==0 and hashlib.sha256(canonical(rec)).hexdigest()==pin['record_canonical_sha256']
   assert rec['source_sha256']==pin['source_sha256'] and rec['object_sha256']==pin['object_sha256']
   assert rec['closure_signature']==pin['closure_signature'] and rec['deps']=={m:selected[m]['object_sha256']for m in pin['direct_project_imports']}
   source_path=pin['source'];object_path=pin['object'];authority='P2_original_normal_and_root_schema1_reuse'
   producer={'deps':rec['deps'],'normal_record_canonical_sha256':pin['record_canonical_sha256'],'closure_signature':pin['closure_signature'],'original_classification':pin['normal_classification']}
  else:
   current=received[mod];assert current['kind']=='foreign_project'
   assert current['sha256']==pin['object_sha256'] and current['source']['sha256']==pin['source_sha256']
   object_path=current['path'];source_path=current['source']['path'];authority='P1_P3_original_qualification_and_exact_P2_reception'
   assert stamp(object_path)==[current['stat'][i]for i in [0,1,4,5,6]]
   assert stamp(source_path)==[current['source']['stat'][i]for i in [0,1,4,5,6]]
   producer={'original_origin':pin['origin'],'P2_byte_reception_sha256':contract['P2_reception_receipt_sha256']}
  sp=preserve(source_path,pin['source_sha256']);op=preserve(object_path,pin['object_sha256'])
  actual_source_imports=re.findall(r'^import\s+(ImbalancedChen\.\S+)',P(source_path).read_text(),re.M)
  if isinstance(pin['direct_project_imports'],list):
   if mod in records:
    # The original54-record reader only promised sorted-name equality.
    assert sorted(actual_source_imports)==sorted(pin['direct_project_imports']),(mod,actual_source_imports,pin['direct_project_imports'])
   else:assert actual_source_imports==pin['direct_project_imports']
  else:
   assert mod in contract['resolved_foreign_direct_imports'] and pin['direct_project_imports']=='not_a_field_in_this_original_borrowed_row_do_not_interpret_as_empty'
   recovered=contract['resolved_foreign_direct_imports'][mod]
   assert recovered['source_sha256']==pin['source_sha256'] and recovered['object_sha256']==pin['object_sha256']
   assert actual_source_imports==recovered['direct_project_imports']
   original_row=original_P1_project_rows[mod]
   assert original_row['source_sha256']==pin['source_sha256'] and original_row['object_sha256']==pin['object_sha256']
   original_dependency_pins={m:original_P1_project_rows[m]['object_sha256']for m in actual_source_imports}
   assert recovered['dependency_byte_pins_from_original_qualified_rows']==original_dependency_pins=={m:selected[m]['object_sha256']for m in actual_source_imports}
   if mod.endswith('.P2FiniteMarkedGamma5FrozenConstants'):
    assert actual_source_imports==receive['selected_objects'][mod]['provenance']['original_borrow_record']['direct_project_imports']
   producer['original_import_recovery']=recovered
  if mod not in records:
   producer['deps']={m:selected[m]['object_sha256']for m in actual_source_imports}
   producer['deps_binding_kind']='Authenticated original source import names joined to fixed original qualified object pins; not a claim that the original borrowed row contained a producer.deps field.'
  dest=lib/(mod.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.is_symlink():assert dest.resolve(strict=True)==P(object_path).resolve(strict=True)
  else:
   assert not dest.exists();dest.symlink_to(P(object_path).resolve(strict=True))
  borrows[mod]={'source':source_path,'source_sha256':pin['source_sha256'],'source_bytes':sp['bytes'],'original_source':pin['source'],'object':str(dest),'object_sha256':pin['object_sha256'],'object_bytes':op['bytes'],'original_object':pin['object'],'reused_current_object':object_path,'direct_project_imports':actual_source_imports,'authority':authority,'producer':producer,'new_source_compilation':False}
 assert len(borrows)==58
 save(out/'BORROWED_OBJECTS.json',borrows)
 external_archive=fixed_bytes(get_blob(contract['external_derived_archive']['git_blob']),contract['external_derived_archive'])
 derived=capture_members(external_archive,contract['external_derived_members'],out/'original-external-derived')
 shape=json.loads(derived['SNAPSHOT_SHAPE.json'].read_text())
 assert shape['raw_source']['sha256']==contract['external_snapshot_sha256'] and shape['declared_module_facet_count']==55560
 assert shape['header_candidate_count']==0 and shape['context_signature_verified']is True
 native={row['module']:row for row in (json.loads(l)for l in derived['NATIVE_SOURCE_IMPORTS.jsonl'].read_text().splitlines())}
 assert len(native)==515
 expected_origins={}
 for line in derived['P2_DECLARED_FACETS.jsonl'].read_text().splitlines():
  row=json.loads(line);key=(row['module'],row['facet']);assert key not in expected_origins
  assert row['original_snapshot_sha256']==contract['external_snapshot_sha256']
  expected_origins[key]={**row['identity'],'origin':'ad438_original_accepted_snapshot'}
 assert len(expected_origins)==55560
 extra=[json.loads(l)for l in derived['P1_REQUIRED_NOT_DESCRIBED.jsonl'].read_text().splitlines()]
 assert len(extra)==19
 for row in extra:
  key=(row['module'],row['facet']);assert key not in expected_origins
  if row['module']in received:
   r=received[row['module']];assert r['kind']=='native' and row['facet']=='.olean'
   assert r['bytes']==row['P1_required']['bytes'] and r['sha256']==row['P1_required']['sha256']
   assert stamp(r['path'])==[r['stat'][i]for i in [0,1,4,5,6]]
   expected_origins[key]={'path':r['path'],'bytes':r['bytes'],'sha256':r['sha256'],'origin':'original_P1_native_qualification_exact_P2_reception'}
  else:
   assert row['module']=='Lake.Util.Casing' and row['facet']in ['.olean','.olean.private','.olean.server','.ir','.ir.sig']
   expected_origins[key]={**row['P1_required'],'origin':'original_P1_facet_current_P2_exact_preflight'}
 for mod,row in borrows.items():
  key=(mod,'.olean');assert key not in expected_origins
  expected_origins[key]={'path':str(P(row['object']).resolve()),'bytes':row['object_bytes'],'sha256':row['object_sha256'],'origin':row['authority']}
 qualified_research=set(native)|{m for m,r in received.items()if r['kind']=='native'}
 assert len(qualified_research)==529
 old_by_part={};native_links=[]
 for (mod,facet),pin in sorted(expected_origins.items()):
  if mod not in qualified_research:continue
  current=P(pin['path']);resolved=current.resolve(strict=True);st=stamp(current);assert current.is_file() and st[2]==pin['bytes'] and stamp(resolved)==st
  cache_before[str(current)]=st;cache_before[str(resolved)]=st
  # The guarded actual probe, not this metadata view, reads the used bytes.
  dest=lib/(mod.replace('.','/')+facet);assert not dest.exists() and not dest.is_symlink()
  dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(resolved)
  provider={'original_selected_path':str(current),'original_snapshot_sha256':contract['external_snapshot_sha256']}if mod in native else {'original_selected_path':str(current),'P2_byte_reception_sha256':contract['P2_reception_receipt_sha256']}
  old_by_part[(mod,facet)]={'module':mod,'facet':facet,'identity':{'path':str(resolved),'bytes':pin['bytes'],'sha256':pin['sha256']},'stat_snapshot':st,'authority':pin['origin'],'provider':provider}
  native_links.append({'module':mod,'facet':facet,'requested_path':str(dest),'selected_path':str(current),'bytes':pin['bytes'],'sha256':pin['sha256']})
 assert {m for m,f in old_by_part}==qualified_research
 save(out/'COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json',{'schema':'p29_complete_selected_native_namespace_symlink_view_v1','old_native_modules':515,'received_native_modules':14,'selected_native_modules':529,'facets':native_links,'no_old_object_or_qualification_modified':True,'actual_import_qualification_not_yet_run':True})
 # New independent configuration: no goldbach build dependency can precede
 # this complete selected namespace view. All standard package pins survive.
 for name,pin in contract['configuration'].items():
  original=P(pin['original_path']);preserve(original,pin['original_sha256'])
  data=base64.b64decode(pin['postimage_base64']);fixed_bytes(data,pin)
  (root/name).write_bytes(data)
 (root/'.lake/packages').symlink_to('/workspace/goldbach-p2/.lake/packages',target_is_directory=True)
 cfg=tomllib.loads((root/'lakefile.toml').read_text())
 assert cfg['lean_lib']==[{'name':'ImbalancedChen','roots':[target],'globs':[target]}]
 assert [r['name']for r in cfg['require']]==['mathlib']
 manifest=json.loads((root/'lake-manifest.json').read_text());assert 'goldbach'not in {p['name']for p in manifest['packages']}
 configs={str(root/n):sha(root/n)for n in contract['configuration']}
 save(out/'CONFIGURATION_ADAPTATION.json',{'configuration':contract['configuration'],'API_review_git_blob':'8eac353b96e13e83796af49956f0aebb6f09731c','complete_project_namespace_modules':58,'complete_native_namespace_modules':529,'actual_resolution_is_checked_before_normal':True})
 unit=next(a for a in receive['archives']if a['group']=='unit128')
 unit_path=P(unit['path']);unit_raw=unit_path.read_bytes();fixed_bytes(unit_raw,unit)
 unit_members=capture_members(unit_raw,contract['original_tools_members'],base)
 tools_expected={str(p):contract['original_tools_members'][member]['sha256']for member,p in unit_members.items()}
 GUARD=base/'original-tools/ci_runtime_guard.py';RUNNER=base/'original-tools/run_guarded.py';OWNED=base/'original-tools/validate_member_roots_owned.py'
 # A real fixed Git checkout is required by the original guard. The five
 # copied official scripts alone are intentionally not treated as a checkout.
 action=base/'lean-action';action.mkdir();action_commands=[]
 for argv in [['git','init',str(action)],['git','-C',str(action),'fetch','--depth=1','https://github.com/leanprover/lean-action.git',contract['action_commit']],['git','-C',str(action),'checkout','--detach','FETCH_HEAD']]:
  run=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
  action_commands.append({'command':argv,'exit_code':run.returncode,'output':run.stdout.decode(errors='replace')})
  if run.returncode:save(out/'ACTION_CHECKOUT_PROCESS.json',action_commands);raise RuntimeError('Fixed official action checkout failed')
 assert subprocess.check_output(['git','-C',str(action),'rev-parse','HEAD'],text=True).strip()==contract['action_commit']
 for name,h in contract['action_script_sha256'].items():preserve(action/'scripts'/name,h)
 save(out/'ACTION_CHECKOUT_PROCESS.json',action_commands)
 runtime_parent=base/'runtime';runtime_parent.mkdir();base_env=os.environ.copy()
 for k in ['LEAN_SYSROOT','LEAN','LEAN_AR','LEAN_CC','LAKE','LAKE_HOME','LAKE_OVERRIDE_LEAN','LEAN_PATH','LEAN_SRC_PATH','P0_CI_GUARD_STATE','P0_COMPILER_SLOT_HELD','P0_COMPILER_SLOT_FD','P0_COMPILER_SLOT_TOOL']:base_env.pop(k,None)
 base_env.update(LEAN_NUM_THREADS='2',ELAN_TOOLCHAIN=PIN,ELAN_HOME='/workspace/.elan',RUNNER_TEMP=str(runtime_parent),LEAN_ACTION_DIR=str(action),GITHUB_ENV=str(out/'runtime.env'),GITHUB_PATH=str(out/'runtime.path'))
 base_env['PATH']='/workspace/.elan/bin:'+base_env.get('PATH','')
 before_Lean_resources=resources()
 assert before_Lean_resources['cgroup_binding']==initial_resources['cgroup_binding']
 save(out/'CAPACITY_BEFORE_FIRST_LEAN.json',before_Lean_resources)
 setup_cmd=['python3',str(GUARD),'setup','--evidence',str(out/'runtime-evidence')]
 with (out/'runtime-setup.log').open('xb')as f:res=subprocess.run(setup_cmd,cwd=root,env=base_env,stdout=f,stderr=subprocess.STDOUT,timeout=240)
 save(out/'runtime-setup-process.json',{'command':setup_cmd,'cwd':str(root),'exit_code':res.returncode,'log_sha256':sha(out/'runtime-setup.log')})
 assert res.returncode==0,'Original guard setup failed; inspect runtime-setup.log'
 state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text());state_sha=sha(state_path);guardlog=P(state['log'])
 assert state['policy']=='Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2'
 assert state['action_commit']==contract['action_commit'] and len(state['action_script_sha256'])==5
 runprefix=['python3',str(RUNNER),'--state',str(state_path)]
 spec=importlib.util.spec_from_file_location('p29_original_owned_auditor',OWNED);auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
 package_revisions={r['name']:r['rev']for r in manifest['packages']};package_bindings={}
 for mapping in ['runtime_sha256','input_sha256','action_script_sha256']:
  for p,h in state[mapping].items():preserve(p,h)
 save(out/'REUSED_ORIGINAL_QUALIFICATIONS.json',{'schema':'p29_omitted_exact_original_qualification_reuse_v1','input_contract_sha256':CONTRACT_SHA256,'two_schema1_roots':authority_summaries,'Nonunit_root_acceptance':contract['authorities']['Nonunit_root_acceptance'],'P2_byte_reception':contract['authorities']['P2_received18'],'original_native_snapshot_sha256':contract['external_snapshot_sha256'],'new_source_kernel_owned_supplier_replays':0,'new_supplier_formal_credit':0,'current_actual_header_facet_union_not_yet_run':True})
 stage('runtime-initial-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe'])
 save(out/'INITIAL_RUNTIME_REPORT_PRESERVED.json',json.loads((out/'runtime-evidence/audit.json').read_text()))
 stage('pinned-lean-version',runprefix+['lake','env','lean','--version'])
 version=(out/'pinned-lean-version.log').read_text();assert 'version 4.33.0-rc1,'in version and 'commit '+LEAN_COMMIT+','in version
 stage('pinned-lean-prefix',runprefix+['lake','env','lean','--print-prefix'])
 assert (out/'pinned-lean-prefix.log').read_text().strip()==state['shadow']
 shadow=P(state['shadow']);assert (shadow/'lib').is_symlink() and (shadow/'lib/lean').resolve()==TOOL_LIB
 assert P(state['realbin']).resolve()==(TC/'bin').resolve()
 for name,copy in [('lean','lean-runtime'),('lake','lake')]:
  p=TC/'bin'/name;q=shadow/'bin'/copy;assert sha(p)==sha(q)==state['runtime_sha256'][str(p)]==state['runtime_sha256'][str(q)]
 before=actual_inputs('omitted-direct-imports',source_imports)
 bound_before=assert_expected_current_map(before)
 old_inputs=before;old_by_part={(p['module'],p['facet']):p for p in before['parts']}
 assert bind_existing_qualification(before)==bound_before
 before_part_identities={k:p['identity']for k,p in old_by_part.items()}
 stable()
 normal_cmd=runprefix+['lake','env','lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(lib/(target.replace('.','/')+'.olean')),'-i',str(lib/(target.replace('.','/')+'.ilean')),str(src)]
 normal=stage('normal-build',normal_cmd,allow_sources={str(src.resolve())},timeout=900)
 produced=source_outputs();save(out/'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json',produced)
 after=actual_inputs('consumer-actual-imports',[target],produced)
 bound_after=bind_existing_qualification(after,allow_target=True);assert bound_after==bound_before
 after_old={(p['module'],p['facet']):p['identity']for p in after['parts']if p['module']!=target}
 assert after_old==before_part_identities
 assert {(p['module'],p['facet'])for p in after['parts']if p['module']==target}=={(target,'.olean')}
 assert {r['module']for r in after['actual_modules']}=={r['module']for r in before['actual_modules']}|{target}
 save(out/'BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json',{'schema':'p29_omitted_exact_old_module_facet_identity_preservation_v1','old_part_count':bound_before,'pre_normal_graph_sha256':sha(out/'omitted-direct-imports-bindings.json'),'post_normal_graph_sha256':sha(out/'consumer-actual-imports-bindings.json'),'every_old_module_facet_path_bytes_sha256_identical':True,'only_added_part':[target,'.olean'],'old_source_kernel_owned_replays':0})
 kernel=named_kernel('named-kernel',[target]);owned,decls,inventory,axioms=full_owned('full-owned',[target])
 stage('runtime-final-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe','--require-source'])
 stable();assert source_outputs()==produced and sha(src)==source_sha
 save(out/'SOURCE_AND_OUTPUTS_AFTER.json',produced)
 commands=[json.loads(l)for l in guardlog.read_text().splitlines()if l]
 lean_sources=[str(P(r['cwd'])/a)if not P(a).is_absolute()else a for r in commands if r.get('tool')=='lean'for a in r.get('input_args',[])if a.endswith('.lean')]
 assert lean_sources==[str(src)],lean_sources
 assert not (lib/(target.replace('.','/')+'.trace')).exists() and not (lib/(target.replace('.','/')+'.setup.json')).exists()
 result={'schema':'p29_omitted_prime_wall_P2_normal_named_kernel_full_owned_v1','result':'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED','module':target,'source_git_blob':source_blob,'source_sha256':source_sha,'source_bytes':len(source),'normal':normal,'normal_warningAsError':True,'kernel':kernel,'owned':owned,'owned_count':len(decls),'inventory':inventory,'observed_axioms':axioms,'full_owned_types_and_original_parser':True,'separate_raw_AST_universe_serializer_claim':False,'actual_input_modules':after['module_count'],'actual_input_parts':after['part_count'],'actual_input_bindings_sha256':sha(out/'consumer-actual-imports-bindings.json'),'pre_normal_import_bindings_sha256':sha(out/'omitted-direct-imports-bindings.json'),'existing_accepted_byte_parts_used':bound_after,'input_contract_sha256':CONTRACT_SHA256,'borrowed_module_count':58,'actual_project_modules_including_target':59,'selected_native_namespace_modules':529,'actual_native_modules_used':len(set(r['module']for r in after['actual_modules'])&qualified_research),'original_guard_runner_validator_unchanged':tools_expected,'normal_source_invocations':lean_sources,'borrowed_source_recompilations':0,'borrowed_new_kernel_replays':0,'borrowed_new_owned_replays':0,'full_P2_9_complete':False,'whole_standard_import_kernel_replay_claim':False,'scope':'Original manuscript OmittedPrimeWall only; all original quantifiers, ordered tuples and omitted-coordinate reserve remain unchanged.'}
 save(out/'VALIDATION_RESULTS.json',result)
 print(json.dumps({k:result[k]for k in ['result','module','owned_count','observed_axioms','actual_input_modules','actual_input_parts']}),flush=True)
 members={}
 for p in out.rglob('*'):
  if p.is_file():assert not p.is_symlink();members['verification/'+str(p.relative_to(out))]=p
 for p in [src,root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json',lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]:
  assert p.is_file()and not p.is_symlink();members['project/'+str(p.relative_to(root))]=p
 for p in (base/'original-tools').iterdir():members['original-tools/'+p.name]=p
 for name in previous_pins:members['original-first-attempt/'+name]=previous_out/name
 for name in contract['action_script_sha256']:members['original-action-scripts/'+name]=action/'scripts'/name
 manifest={'schema':'p29_omitted_complete_original_single_target_evidence_v1','files':{k:{'bytes':p.stat().st_size,'sha256':sha(p)}for k,p in members.items()},'excludes':['FILE_MANIFEST.json'],'borrowed_old_objects_not_duplicated':True,'all_source_kernel_owned_supplier_replays':0}
 save(base/'FILE_MANIFEST.json',manifest);members['FILE_MANIFEST.json']=base/'FILE_MANIFEST.json'
 archive=base/'qualified-omitted-prime-wall.tar.xz'
 with tarfile.open(archive,'w:xz',preset=6)as tf:
  for name,p in sorted(members.items()):tf.add(p,arcname=name,recursive=False)
 meta={'path':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'members':len(members),'manifest_sha256':sha(base/'FILE_MANIFEST.json'),'new_module':target,'new_owned_count':len(decls),'borrowed_supplier_replays':0}
 save(base/'ARCHIVE_TRANSPORT.json',meta);print('P29_ARCHIVE '+json.dumps(meta),flush=True)

try:
 main()
except Exception as error:
 partial={}
 if 'lib'in globals():
  for p in [src,lib/(target.replace('.','/')+'.olean'),lib/(target.replace('.','/')+'.ilean')]:
   if p.is_file():partial[str(p)]={'bytes':p.stat().st_size,'sha256':sha(p)}
 failure={'schema':'p29_omitted_P2_original_single_attempt_failure_v1','error':str(error),'traceback':traceback.format_exc(),'completed_stages':[r['stage']for r in globals().get('runs',[])],'partial_target_outputs_preserved':partial,'no_automatic_retry':True,'supplier_source_kernel_owned_replays':0}
 if globals().get('OWNED_BASE_CREATED',False) and 'out'in globals() and out.is_dir() and not (out/'FAILURE.json').exists():save(out/'FAILURE.json',failure)
 print('P29_FAILURE '+json.dumps(failure),flush=True)
 raise
