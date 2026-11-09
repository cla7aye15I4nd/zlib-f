#!/usr/bin/env python3
"""One reviewed scoped case; never changes public Goal.deflate coverage.

The approval reference is an explicit trusted-invoker input. No candidate lock,
self-captured type, missing record, source-only failure, or resource failure is
accepted as a scoped admission. Run only after the normal source build/audit.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

AUDITOR = Path(__file__).resolve().parents[2]
PROOF = 'Zlib.Deflate.Engine.Proofs.generic_default_public_contract'
FUNCTION = 'Zlib.Deflate.deflate'
RECEIPT = 'Zlib.Deflate.Engine.Proofs.public_deflate_source'
MATCHER = 'Zlib.Deflate.deflate.match_1'
CASE = 'null-output-guard'
SOURCE = Path('ZlibF/Zlib/deflate.c.lean')
CUT = Path('ZlibF/Proof/deflate.c.engine.public-source.lean')
OP = Path('ZlibF/Proof/deflate.c.engine.public-entry-refusal-source.lean')
TOOL = Path('tests/proofmut/ScopedDefaultAdmission.lean')
REVIEW = Path('tests/proofmut/reviews/deflate-default-null-output.json')
OP_SPAN = (10, 37)  # Reviewed actual theorem declaration, exclusive upper bound.
OLD = 'if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||'
NEW = 'if false || (z.avail_in != 0 && z.next_in == .null) ||'
RESOURCE = ('maximum recursion depth', 'maximum number of heartbeats',
            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory')

class Rejected(Exception): pass

def sha(data): return hashlib.sha256(data).hexdigest()
def digest(value):
    return sha(json.dumps(value, ensure_ascii=True, separators=(',', ':'), sort_keys=True).encode())
def command(argv, cwd, env=None, expected=0, log=None):
    result = subprocess.run(argv, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
    if log: log.write_text(result.stdout)
    if result.returncode != expected or any(word in result.stdout.lower() for word in RESOURCE):
        raise Rejected(f'command rejected or inconclusive ({result.returncode}): {argv}\n{result.stdout}')
    return result

def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root)
def resolve(root, ref): return git(root, 'rev-parse', '--verify', ref+'^{commit}').decode().strip()
def approved(root, commit, path): return git(root, 'show', f'{commit}:{path}')
def names(data):
    result=[line.strip() for line in data.decode().splitlines() if line.strip() and not line.lstrip().startswith('#')]
    if len(set(result)) != len(result): raise Rejected('duplicate registry entries')
    return result

def statement(data, proof):
    rows=[line for line in data.decode().splitlines() if line.startswith('statement '+proof+' ')]
    if len(rows)!=1: raise Rejected('FAIL CLOSED: approved scoped statement record is absent or duplicated')
    match=re.fullmatch(r'statement (\S+) ([0-9a-f]{64}) :: .+', rows[0])
    if not match: raise Rejected('malformed approved statement record')
    return match.group(2)

def preflight(root, approval_ref, semantic_ref):
    # Explicit immutable externally approved commits, never candidate HEAD or a moving branch.
    if not re.fullmatch(r'[0-9a-f]{40}',approval_ref) or not re.fullmatch(r'[0-9a-f]{40}',semantic_ref):
        raise Rejected('explicit full approved/semantic commit SHAs are required')
    approval=resolve(AUDITOR, approval_ref)
    semantic=resolve(AUDITOR, semantic_ref)
    registry=approved(AUDITOR,approval,'tests/audit/theorems.txt')
    if PROOF not in names(registry): raise Rejected('approved scoped theorem is not registered')
    locked_type=statement(approved(AUDITOR,approval,'tests/audit/statements.lock'),PROOF)
    # Registration extensions can be reviewed before merge. A semantic change
    # still needs the independently approved semantic baseline, as elsewhere.
    for path in ('tests/audit/policy.lock','tests/audit/trusted.lock'):
        if approved(AUDITOR,approval,path)!=approved(AUDITOR,semantic,path):
            raise Rejected('scope approval changes semantic baseline; explicit semantic approval is required')
        if (root/path).read_bytes()!=approved(AUDITOR,approval,path):
            raise Rejected('current semantic/policy lock differs from approved snapshot')
    if PROOF not in names((root/'tests/audit/theorems.txt').read_bytes()): raise Rejected('current registry missing scoped root')
    if statement((root/'tests/audit/statements.lock').read_bytes(),PROOF)!=locked_type:
        raise Rejected('current scoped statement differs from independently approved record')
    if (root/OP).read_bytes()!=approved(AUDITOR,approval,OP):
        raise Rejected('operational theorem statement/proof differs from approved source')
    policy=json.loads(approved(AUDITOR,approval,'tests/audit/policy.lock'))
    for path,value in policy['files'].items():
        file=root/path
        if file.is_symlink() or not file.is_file() or sha(file.read_bytes())!=value:
            raise Rejected('approved protected source mismatch: '+path)
    # Execute only the independently approved auditor's standard parser/tool.
    for path in (TOOL,Path(__file__).relative_to(AUDITOR),Path('scripts/mutation_spans.py'),
                 Path('tests/audit/DeclarationSpan.lean'),Path('lean-toolchain'),Path('lakefile.toml')):
        if (AUDITOR/path).read_bytes()!=approved(AUDITOR,approval,path):
            raise Rejected('invoking admission/parser code differs from approved commit: '+str(path))
    pin=git(root,'ls-files','-s','zlib').decode().split()
    if len(pin)<2 or pin[0]!='160000' or pin[1]!=policy['zlib']:
        raise Rejected('target upstream gitlink differs from approved policy')
    if resolve(root/'zlib','HEAD')!=policy['zlib'] or git(root/'zlib','status','--porcelain').strip():
        raise Rejected('actual upstream checkout is not clean and at approved pin')
    review=json.loads(approved(AUDITOR,approval,REVIEW))
    required={'case':CASE,'proof':PROOF,'scope':'default-basic-requests',
              'verdict':'review-complete','review_role':'independent'}
    if any(review.get(k)!=v for k,v in required.items()): raise Rejected('independent allowed-input review is not approved')
    for path in (REVIEW,Path(review['evidence'])):
        if str(path) not in policy['files']: raise Rejected('behaviour review is not protected by approved source policy')
    if sha(approved(AUDITOR,approval,Path(review['evidence'])))!=review['evidence_sha256']:
        raise Rejected('independent behaviour evidence hash differs')
    if review['upstream_pin']!=policy['zlib']: raise Rejected('behaviour review upstream pin differs')
    patches={str(p.relative_to(root)):sha(p.read_bytes()) for p in (root/'patches').glob('*.patch')}
    if patches!=review['patches']: raise Rejected('behaviour review effective patch set differs')
    if sha(approved(AUDITOR,approval,Path(review['domain_witness'])))!=review['domain_witness_sha256']:
        raise Rejected('reviewed actual-domain witness differs')
    if str(Path(review['domain_witness'])) not in policy['files']:
        raise Rejected('domain witness is not protected by approved policy')
    if sha((root/SOURCE).read_bytes())!=review['original_source_sha256']:
        raise Rejected('behaviour review concerns a different original source')
    head=resolve(root,'HEAD')
    if git(root,'status','--porcelain','--untracked-files=normal').strip():
        raise Rejected('source context must be clean and committed before snapshot')
    return approval,semantic,head,registry,locked_type,review

def fingerprint(directory):
    return {str(p.relative_to(directory)):sha(p.read_bytes()) for p in directory.rglob('*') if p.is_file()}

def mutate(text, source):
    first='def deflate (strm : ZStreamPtr)' if source else 'theorem public_deflate_source ('
    end='/-- `int ZEXPORT deflateParams(' if source else '\nend Zlib.Deflate.Engine.Proofs'
    before,body=text.split(first,1); body,after=body.split(end,1)
    if body.count(OLD)!=1: raise Rejected('ambiguous/null output guard not inside selected program cut')
    return before+first+body.replace(OLD,NEW)+end+after

def check_inventory(sides):
    old,new=({r['name']:r for r in side} for side in sides)
    if old.keys()!=new.keys(): raise Rejected('source-owned declaration inventory changed')
    for name,a in old.items():
        b=new[name]
        if a['unsafe'] or a['partial'] or b['unsafe'] or b['partial']: raise Rejected('unsafe/partial source-owned declaration')
        if name==FUNCTION:
            if a['type']!=b['type'] or a['body']==b['body']: raise Rejected('actual function signature/body mutation mismatch')
        elif name==RECEIPT:
            if a['type']==b['type']: raise Rejected('derived source cut was not synchronized')
        elif name==MATCHER:
            if a['type'][0]!=b['type'][0] or a['typeAlpha']!=b['typeAlpha'] or a['bodyAlpha']!=b['bodyAlpha']:
                raise Rejected('compiler matcher changed beyond binder names/mdata')
            if a['semantic'][2:]!=b['semantic'][2:]: raise Rejected('matcher definition metadata changed')
        elif a!=b:
            raise Rejected('another source-owned declaration changed: '+name)


def run(args):
    root=args.root.resolve(); approval,semantic,head,registry,locked_type,review=preflight(
        root,args.approved_commit,args.semantic_baseline)
    if args.preflight_only:
        print('SCOPED PREFLIGHT ONLY; no proof acceptance claimed');return
    # A normal fresh build/audit must precede admission. Actual model/type records
    # below are checked again against independently approved locks, not just caches.
    spec=importlib.util.spec_from_file_location('approved_mutation_spans',AUDITOR/'scripts/mutation_spans.py')
    spans=importlib.util.module_from_spec(spec);spec.loader.exec_module(spans)
    env=dict(os.environ)
    for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT'): env.pop(key,None)
    env['ELAN_TOOLCHAIN']=(AUDITOR/'lean-toolchain').read_text().strip()
    env['LEAN_NUM_THREADS']='2'
    lean=subprocess.check_output(['elan','which','lean'],cwd=AUDITOR,env=env,text=True).strip()
    env['PATH']=str(Path(lean).resolve().parent)+os.pathsep+env.get('PATH','')
    version=subprocess.check_output([lean,'--version'],cwd=AUDITOR,env=env,text=True).strip()
    pinned=env['ELAN_TOOLCHAIN'].rsplit(':v',1)[-1]
    if 'version '+pinned not in version: raise Rejected('invoking compiler differs from approved toolchain')
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    with tempfile.TemporaryDirectory(prefix='scoped-default-admission-') as directory:
        work=Path(directory); command(['git','archive','--format=tar','--output='+str(work/'source.tar'),head,
            'ZlibF','ZlibF.lean','lakefile.toml','lean-toolchain',str(REVIEW.parent)],root)
        command(['tar','-xf',str(work/'source.tar')],work)
        original=root/'.lake/build/lib/lean';before=fingerprint(original)
        shutil.copytree(original,work/'original-lib')
        if fingerprint(original)!=before or fingerprint(work/'original-lib')!=before:
            raise Rejected('source build cache changed during frozen copy; no retry')
        (output/'frozen-context.json').write_text(json.dumps({'head':head,'approved':approval,'semantic':semantic,
            'cache':before},sort_keys=True)+'\n')
        (work/'registry.txt').write_bytes(registry)
        pin=work/'type.json'; report=work/'report.json'
        def tool(mode, variant=None, expected=0):
            result=command([lean,'--run',str(AUDITOR/TOOL),mode,str(work/'original-lib'),
                str(variant or work/'original-lib'),str(work/'registry.txt'),str(pin),str(report)],
                work,env,expected,output/(mode+'.log'))
            data=json.loads(report.read_text());(output/(mode+'.json')).write_text(json.dumps(data,sort_keys=True)+'\n')
            return result,data
        _,metadata=tool('inspect')
        if digest(metadata['type'])!=locked_type: raise Rejected('actual complete root type differs from approved statement lock')
        trusted={}
        for line in approved(AUDITOR,approval,'tests/audit/trusted.lock').decode().splitlines():
            tag,name,t,v=line.split();trusted[name]=(t,v)
        for record in metadata['semantic']:
            if trusted.get(record['name'])!=(digest(record['type']),digest(record['value'])):
                raise Rejected('actual root semantic dependency differs from approved lock: '+record['name'])
        pin.write_text(json.dumps(metadata['type'],ensure_ascii=True,separators=(',',':'),sort_keys=True)+'\n')
        tool('baseline')
        def compile_source(path, library, target, label, expected=0):
            target.parent.mkdir(parents=True,exist_ok=True)
            local=dict(env,LEAN_PATH=str(library))
            return command([lean,'-o',str(target),str(path)],work,local,expected,output/(label+'.log'))
        opbytes=(work/OP).read_bytes()
        positive_overlay=work/'positive-op-lib'
        for source in (work/'original-lib').rglob('*'):
            if not source.is_file(): continue
            relative=str(source.relative_to(work/'original-lib'))
            stem='ZlibF/Proof/deflate.c.engine.public-entry-refusal-source.olean'
            if relative==stem or relative.startswith(stem+'.'): continue
            target=positive_overlay/relative;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(source)
        compile_source(OP,work/'original-lib',positive_overlay/'ZlibF/Proof/deflate.c.engine.public-entry-refusal-source.olean','operational-positive')
        tool('operation-seed',positive_overlay)
        compile_source(Path(review['domain_witness']),work/'original-lib',work/'domain-witness.olean','actual-domain-witness')
        original_c=work/'original-C.lean';original_c.write_bytes((work/SOURCE).read_bytes())
        (work/SOURCE).write_text(mutate((work/SOURCE).read_text(),True))
        (work/CUT).write_text(mutate((work/CUT).read_text(),False))
        guard=spans.check(original_c,work/SOURCE,'deflate')
        (output/'parsed-body.json').write_text(json.dumps(guard,sort_keys=True)+'\n')
        if sha((work/SOURCE).read_bytes())!=review['mutant_source_sha256']:
            raise Rejected('same-case mutant does not match independent behaviour review')
        overlay=work/'variant-lib'
        overrides=('ZlibF/Zlib/deflate.c.olean','ZlibF/Proof/deflate.c.engine.public-source.olean')
        for source in (work/'original-lib').rglob('*'):
            if not source.is_file():continue
            rel=str(source.relative_to(work/'original-lib'))
            if any(rel==p or rel.startswith(p+'.') for p in overrides):continue
            target=overlay/rel;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(source)
        compile_source(SOURCE,overlay,overlay/overrides[0],'mutant-c')
        compile_source(CUT,overlay,overlay/overrides[1],'synchronized-cut')
        _,inventory=tool('inventory',overlay);check_inventory(inventory)
        result,data=tool('exact-mutant',overlay,2)
        if data.get('status')!='exact-scoped-proof-rejected' or not result.stdout.startswith('EXACT_SCOPED_PROOF_REJECTED'):
            raise Rejected('exact scoped original proof did not reject')
        tool('source-gate',overlay)
        if (work/OP).read_bytes()!=opbytes: raise Rejected('operational source was modified')
        negative=compile_source(OP,overlay,work/'negative-op.olean','operational-negative',1)
        errors=re.findall(r'^([^\n]+\.lean):(\d+):(\d+): error: (.*)$',negative.stdout,re.M)
        lower,upper=OP_SPAN
        if len(errors)!=1 or errors[0][0]!=str(OP) or not lower<=int(errors[0][1])<upper or errors[0][3]!='unsolved goals':
            raise Rejected('not the existing real execution-goal failure; source/rw errors do not count')
        if resolve(root,'HEAD')!=head or git(root,'status','--porcelain','--untracked-files=normal').strip():
            raise Rejected('source context changed during admission')
        (output/'result.json').write_text(json.dumps({'scope':'default-basic-requests','case':CASE,'proof':PROOF,
            'head':head,'approved':approval,'semantic':semantic,'type_sha256':locked_type,
            'original_c_sha256':review['original_source_sha256'],'mutant_c_sha256':review['mutant_source_sha256'],
            'source_signature_body_guard':True,'exact_root_baseline':0,'exact_root_negative':2,
            'synchronized_gate':0,'operational_positive':0,'operational_negative':1,
            'execution_error':errors[0],'independent_behavior_review':str(REVIEW),'actual_domain_witness':0,
            'full_Goal_deflate_coverage':False},sort_keys=True)+'\n')
    print('SCOPED ADMISSION PASSED: default-basic-requests / null-output-guard; not Goal.deflate')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--approved-commit',required=True,help='externally reviewed immutable scope/type/behaviour approval; never candidate HEAD by default')
    parser.add_argument('--semantic-baseline',required=True,help='same approved semantic baseline used by the invoking verification gate')
    parser.add_argument('--output',type=Path,default=Path('.lake/scoped-default-admission'))
    parser.add_argument('--preflight-only',action='store_true')
    args=parser.parse_args()
    try:run(args)
    except (Rejected,ValueError,KeyError,OSError,subprocess.SubprocessError) as error:
        print('SCOPED ADMISSION REJECTED: '+str(error),file=__import__('sys').stderr);return 1
    return 0
if __name__=='__main__':raise SystemExit(main())
