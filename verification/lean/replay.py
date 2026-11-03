"""Replay only the packaged selected graph. No git or network operations.
Usage: python -B replay.py --mathlib PATH --lean-root PATH --work-dir EMPTY_PATH [--wait-for-other-lean]
The work directory must be outside this source package. --resume reuses only
successful source/object hash-matched receipts from this runner.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,struct,subprocess,sys,time
import psutil
A=argparse.ArgumentParser();A.add_argument('--mathlib',required=True);A.add_argument('--lean-root',required=True);A.add_argument('--work-dir',required=True);A.add_argument('--resume',action='store_true');A.add_argument('--wait-for-other-lean',action='store_true');a=A.parse_args()
P=Path(__file__).resolve().parent;W=Path(a.work_dir).resolve();M=Path(a.mathlib).resolve();LR=Path(a.lean_root).resolve()
assert not W.is_relative_to(P) and W!=P
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest().upper()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
pins=read(P/'dependency-pins.json');manifest=P/'MANIFEST.sha256';manifest_hash=sha(manifest)
def guard_sources():
 assert sha(manifest)==manifest_hash
 for line in manifest.read_text().splitlines():
  h,rel=line.split('  ',1);assert sha(P/rel)==h,rel
 for n,k in [('lakefile.lean','lakefileSHA256'),('lake-manifest.json','manifestSHA256'),('lean-toolchain','toolchainSHA256')]:assert sha(M/n)==pins['mathlib'][k],n
if not a.resume:assert not W.exists() or not any(W.iterdir()),'Use an empty scratch directory'
W.mkdir(parents=True,exist_ok=True)
for d in ['build','vendor-build','runtime-build','bin','logs','tmp']:(W/d).mkdir(exist_ok=True)
guard_sources()
env=os.environ.copy();env.update(LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1',LEAN_SYSROOT=str(LR),TEMP=str(W/'tmp'),TMP=str(W/'tmp'))
env['PATH']=str(LR/'bin')+os.pathsep+env['PATH'];paths=[W/'build',W/'vendor-build',W/'runtime-build',M/'.lake/build/lib/lean']
paths += [p/'.lake/build/lib/lean' for p in (M/'.lake/packages').iterdir() if p.is_dir()]
env['LEAN_PATH']=os.pathsep.join(map(str,paths))
lean=LR/'bin/lean.exe';leanc=LR/'bin/leanc.exe'
ver=subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout
assert 'version 4.30.0,' in ver and 'd024af099ca4bf2c86f649261ebf59565dc8c622' in ver,ver
core=[lean,LR/'lib/lean/Init.olean',LR/'lib/lean/Init/Prelude.olean',LR/'lib/lean/Lean/Replay.olean']+list((LR/'bin').glob('libleanshared*.dll'))
core_hash={str(p):sha(p) for p in core}
receipts=read(W/'receipts.json') if a.resume and (W/'receipts.json').exists() else []
old={x['stage']:x for x in receipts};records=[];started=time.monotonic();peak_all=0
selfp=psutil.Process();exclude={os.getpid()}|{p.pid for p in selfp.parents()}
def external():
 hits=[]
 if not a.wait_for_other_lean:return hits
 for p in psutil.process_iter(['pid','name','cmdline']):
  if p.pid in exclude:continue
  n=(p.info['name'] or '').lower();cmd=' '.join(p.info['cmdline'] or [])
  if n in ('lean.exe','lake.exe','leanchecker430.exe','leanexport430.exe','nanoda-stack128.exe'):
   hits.append({'pid':p.pid,'name':n,'command':cmd})
 return hits

def idle():
 while True:
  hits=external()
  if not hits:return
  (W/'waiting.json').write_text(json.dumps({'waiting_for_external_build':hits,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2))
  print('WAIT external Lean build:',[h['pid'] for h in hits],flush=True);time.sleep(5)

def terminate_tree(p):
 try:children=psutil.Process(p.pid).children(recursive=True)
 except psutil.NoSuchProcess:children=[]
 for q in children[::-1]:
  try:q.kill()
  except psutil.NoSuchProcess:pass
 p.kill();p.wait()

def run(stage,args,cwd,output=None,source=None,obj=None):
 global peak_all
 if source and obj and a.resume:
  r=old.get(stage)
  if r and r['exitCode']==0 and r.get('sourceSHA256')==sha(source) and Path(obj).exists() and r.get('objectSHA256')==sha(obj):records.append(r);print('REUSE',stage,flush=True);return
 idle()
 for p,h in core_hash.items():assert sha(p)==h,p
 start=time.monotonic();peak=0;path=W/'logs'/(stage.replace('/','_')+'.log')
 print('START',stage,flush=True)
 with path.open('wb') as log:
  out=Path(output).open('wb') if output else log
  try:
   p=subprocess.Popen(list(map(str,args)),cwd=cwd,env=env,stdin=subprocess.DEVNULL,stdout=out,stderr=log)
   while p.poll() is None:
    try:
     tree=[psutil.Process(p.pid)]+psutil.Process(p.pid).children(recursive=True);ids={q.pid for q in tree};rss=sum(q.memory_info().rss for q in tree if q.is_running());peak=max(peak,rss);peak_all=max(peak_all,rss)
     if rss>10*1024**3:terminate_tree(p);raise RuntimeError('10 GB subprocess-tree cap exceeded')
     # Stop our own stage if an external build starts despite the pre-stage guard.
     overlap=[h for h in external() if h['pid'] not in ids]
     if overlap:
      terminate_tree(p);(W/'external-overlap-stop.json').write_text(json.dumps(overlap,indent=2));raise RuntimeError('Stopped own stage because an external Lean build started; resume after it exits')
    except psutil.NoSuchProcess:pass
    time.sleep(.5)
  finally:
   if output:out.close()
 r={'stage':stage,'exitCode':p.returncode,'seconds':round(time.monotonic()-start,3),'peakTreeRSSBytes':peak,'finishedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'threads':1,'memoryLimitMB':6144,'command':list(map(str,args))}
 if source:r['sourceSHA256']=sha(source)
 if obj and p.returncode==0:r['objectSHA256']=sha(obj)
 if output:r.update(outputSHA256=sha(output),outputBytes=Path(output).stat().st_size)
 records.append(r);(W/'receipts.json').write_text(json.dumps(records,indent=2));(W/'status.json').write_text(json.dumps({'lastStage':stage,'exit':p.returncode,'elapsedSeconds':round(time.monotonic()-started,3),'peakTreeRSSBytes':peak_all,'packageManifestSHA256':manifest_hash},indent=2))
 print('DONE',stage,p.returncode,r['seconds'],peak,flush=True)
 if p.returncode:raise RuntimeError('Stage failed: '+stage+'; see '+str(path))
 for p,h in core_hash.items():assert sha(p)==h,p

def compile_one(stage,src,obj,cwd,vendor=False,runtime=False):
 obj.parent.mkdir(parents=True,exist_ok=True)
 args=[lean,'-j1','-M6144','-DmaxRecDepth=100000','-DmaxSynthPendingDepth=10000']
 if vendor:args+=['-Dbackward.isDefEq.respectTransparency=false','-Dlinter.unusedSimpArgs=false','-DsynthInstance.maxHeartbeats=200000','-DmaxHeartbeats=2000000']
 args+=['-o',obj]
 if runtime:args+=['-c',obj.with_suffix('.c')]
 args+=[str(src.relative_to(cwd))]
 run(stage,args,cwd,source=src,obj=obj)

try:
 # Fresh scratch copy of every packaged source: no source-tree or historical oleans used.
 for folder in ['src','vendor','runtime']:
  dst=W/folder
  if not dst.exists():shutil.copytree(P/folder,dst)
 selected=read(P/'selected-sources.json');vend=read(P/'vendor-modules.json')
 for m in vend:
  rel=m.replace('.','/');compile_one('vendor/'+m,W/'vendor/PhyslibQuantumInfo'/(rel+'.lean'),W/'vendor-build'/(rel+'.olean'),W/'vendor/PhyslibQuantumInfo',vendor=True)
 done=set();order=[]
 def visit(m):
  if m in done:return
  for dep in re.findall(r'^import\s+([\w.]+)',(W/'src'/(m+'.lean')).read_text(encoding='utf-8-sig'),re.M):
   if dep in selected:visit(dep)
  done.add(m);order.append(m)
 for m in selected:visit(m)
 for m in order:
  src=W/'src'/(m+'.lean');assert sha(src)==selected[m],m;compile_one('owned/'+m,src,W/'build'/(m+'.olean'),W/'src')
 runtime=['LeanExport/Json','LeanExport/Basic','LeanExport/Parse','LeanExport','LeanChecker430']
 for m in runtime:compile_one('runtime/'+m,W/'runtime'/(m+'.lean'),W/'runtime-build'/(m+'.olean'),W/'runtime',runtime=True)
 for name,mods in [('leanexport430',runtime[:4]),('leanchecker430',[runtime[0],runtime[2],runtime[4]])]:
  raw=W/'bin'/(name+'.raw.exe');run('link/'+name,[leanc,'-O2','-o',raw]+[W/'runtime-build'/(m+'.c') for m in mods],W)
  data=bytearray(raw.read_bytes());pe=struct.unpack_from('<I',data,0x3c)[0];assert data[pe:pe+4]==b'PE\0\0';field=pe+24+72;before=bytes(data);struct.pack_into('<Q',data,field,134217728);assert data[:field]==before[:field] and data[field+8:]==before[field+8:];(W/'bin'/(name+'.exe')).write_bytes(data)
 shutil.copy2(P/'runtime/nanoda-stack128.exe',W/'bin/nanoda-stack128.exe')
 roots=['ScheduleLaw.Blueprint.'+n for n in ['finite_factory_of_small_residue_coding','source_factory_circuits','cyclic_cache_protocol','finite_conserving_phase','corrected_joint_tangent','pointwise_physical_compiler','work_law_for_schedules']]
 primitives=['Quot','Quot.mk','Quot.lift','Quot.ind','propext','Classical.choice','Quot.sound','Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam']
 export=W/'proofs.ndjson';run('export430',[W/'bin/leanexport430.exe','Round28Audit','--']+roots+primitives,W,output=export);h=sha(export)
 meta=json.loads(export.open(encoding='utf-8').readline());assert meta['meta']['lean']['version']=='4.30.0' and meta['meta']['format']['version']=='3.1.0'
 run('leanchecker430',[W/'bin/leanchecker430.exe',export],W);assert sha(export)==h
 cfg=W/'nanoda.json';cfg.write_text(json.dumps({'use_stdin':False,'export_file_path':str(export),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'num_threads':1,'nat_extension':True,'string_extension':True},indent=2))
 run('nanoda430',[W/'bin/nanoda-stack128.exe',cfg],W);assert sha(export)==h;guard_sources()
 gate={'certified':True,'freshOwnedModules':len(order),'freshVendorModules':len(vend),'exportSHA256':h,'exportBytes':export.stat().st_size,'packageManifestSHA256':manifest_hash,'wallSeconds':round(time.monotonic()-started,3),'peakTreeRSSBytes':peak_all,'kernels':['Lean 4.30 Environment.replay','Rust nanoda'],'permittedAxioms':['propext','Classical.choice','Quot.sound'],'coreRuntimeHashes':core_hash,'records':records}
 (W/'clean-replay.json').write_text(json.dumps(gate,indent=2));print('CLEAN REPLAY CERTIFIED',h,flush=True)
except BaseException as e:
 (W/'stopped.json').write_text(json.dumps({'error':str(e),'lastCompleted':records[-1]['stage'] if records else None,'wallSeconds':round(time.monotonic()-started,3),'peakTreeRSSBytes':peak_all,'packageManifestSHA256':manifest_hash},indent=2));raise
