"""Finite pinned raw binder-field accounting; never alpha-normalizes expressions."""
import argparse
import copy
import json
from functools import lru_cache
from pathlib import Path
import comparator as c


def pin(path):
    return dict(path=str(Path(path).resolve()), sha256=c.file_hash(path))


def check_pin(p):
    c.require(p.get('path') and p.get('sha256'), 'unpinned binder accounting input')
    c.require(c.file_hash(p['path']) == p['sha256'], 'stale binder input: ' + p['path'])
    return p


def pinned(p):
    check_pin(p)
    return c.read(p['path'])


def split(node):
    c.require(isinstance(node, list) and node, 'invalid raw Expr node')
    k = node[0]
    sizes = {'bvar':2,'fvar':2,'mvar':2,'sort':2,'const':3,'lit':2,'app':3,
             'lam':5,'forallE':5,'letE':6,'mdata':3,'proj':4}
    c.require(k in sizes and len(node) == sizes[k], 'unknown/incomplete Expr constructor')
    if k == 'app': return [k], node[1:3]
    if k in {'lam','forallE'}: return [k,node[1],node[4]],node[2:4]
    if k == 'letE': return [k,node[1],node[5]],node[2:5]
    if k == 'mdata': return node[:2],node[2:3]
    if k == 'proj': return node[:3],node[3:4]
    return node,[]


class RawDag:
    def __init__(self, doc):
        self.nodes, self.hashes = doc['nodes'], []
        self.records = {}
        for i,node in enumerate(self.nodes):
            payload,children=split(node)
            c.require(all(isinstance(j,int) and 0<=j<i for j in children),'non-topological raw DAG')
            self.hashes.append(c.node_hash(payload,[self.hashes[j] for j in children]))
        for r in doc['declarations']:
            n=r['kernel_name']
            c.require(n not in self.records,'duplicate raw DAG owner')
            self.records[n]=r
        self.storage_object=doc.get('actual_storage_object')

    def root(self,n,slot):
        i=self.records[n][slot+'_DAG_root']
        c.require(i is None or isinstance(i,int) and 0<=i<len(self.nodes),'invalid declaration DAG root')
        return i

    def digest(self,n,slot):
        i=self.root(n,slot)
        return None if i is None else self.hashes[i]


@lru_cache(maxsize=4)
def _cached_dag(path,sha):
    # Called only after rechecking bytes against this exact immutable pin.
    return RawDag(c.read(path))


def load_dag(p):
    check_pin(p)
    return _cached_dag(p['path'],p['sha256'])

def binder_delta(a,b,left,right):
    if left is None or right is None:
        c.require(left is right,'missing raw expression')
        return []
    work=[(left,right)];seen=set();delta=[]
    while work:
        i,j=work.pop()
        if (i,j) in seen:continue
        seen.add((i,j))
        if a.hashes[i]==b.hashes[j]:continue
        x,xc=split(a.nodes[i]);y,yc=split(b.nodes[j])
        c.require(x[0]==y[0] and len(xc)==len(yc),'changed Expr constructor/child structure')
        if x!=y:
            c.require(x[0] in {'lam','forallE','letE'} and x[2:]==y[2:] and x[1]!=y[1],
                      'non-binder-name raw scalar changed')
            c.require(all(isinstance(v,str) and '_hyg' in v and v.startswith('Lean.Name.mkNum') for v in [x[1],y[1]]),
                      'binder labels are not compiler-hygienic raw Names')
            delta.append(dict(before_node=i,after_node=j,constructor=x[0],field='binder_name',before_raw=x[1],after_raw=y[1]))
        work.extend(zip(xc,yc))
    return sorted(delta,key=lambda r:(r['before_node'],r['after_node']))


def audit(inputs, protected_roots):
    auth=pinned(inputs['authorization'])
    c.require(auth.get('status','').startswith('AUTHORIZED_') and auth.get('exact_scope') and auth.get('audit_seal'),
              'no explicit finite binder route authorization')
    # Immutable audit inputs, rather than mutable original golfer artifacts.
    seal=pinned(auth['audit_seal'])
    for r in seal['owned_artifacts']:check_pin(r)
    for r in seal['sealed_input_copies']:check_pin(dict(path=r['sealed_copy'],sha256=r['sha256']))
    sealed={Path(r['sealed_copy']).name:r['sha256'] for r in seal['sealed_input_copies']}
    c.require(inputs['before_dag']['sha256'] in {sealed.get('ACCEPTED_NATIVE_DAG.json'),sealed.get('ORIGINAL_NATIVE_DAG.json'),sealed.get('BASELINE_NATIVE_DAG.json')} and
              inputs['after_dag']['sha256']==sealed.get('CANDIDATE_NATIVE_DAG.json'),'raw DAG not bound to authorized sealed exact payloads')
    parentage_pins={r['sha256'] for r in seal['owned_artifacts']}
    if 'supplement_seal' in inputs:
        supplement=pinned(inputs['supplement_seal'])
        c.require(supplement['status']=='SEALED_VERIFIED_BOUNDED_GOLF_HANDOFF_NOT_FINAL_RELEASE_ACCEPTANCE' and
                  supplement['source_sha256']==auth['source_after_sha256'],'supplement handoff/source binding')
        route_pins=supplement['external_authorization_pins']
        c.require(any(r.get('sha256')==inputs['authorization']['sha256'] for r in route_pins),'handoff lacks exact authorization binding')
        for r in supplement['owned_artifacts']:check_pin(r)
        parentage_pins.update(r['sha256'] for r in supplement['owned_artifacts'])
    c.require(inputs['lineage']['sha256'] in parentage_pins,'unsealed parentage input')
    scope=pinned(auth['exact_scope'])
    c.require(auth['exact_scope']['sha256']==seal['scope_sha256'],'scope/audit seal disagreement')
    names=auth.get('allowed_generated_binder_names',[r['name'] for r in scope['generated_artifacts']])
    c.require(len(names)==len(set(names)),'duplicate finite binder names')
    c.require(set(names)=={r['name'] for r in scope['generated_artifacts']},'extra/missing helper scope')
    parent=auth['parent_theorem_proof_change_separate']
    c.require(parent==scope['parent_proof_change']['name'],'parent scope disagreement')
    c.require(not set(names).intersection(protected_roots+[parent]),'protected/source-authored type in binder roster')
    lineage=pinned(inputs['lineage'])
    a,b=load_dag(inputs['before_dag']),load_dag(inputs['after_dag'])
    c.require(set(a.records)==set(b.records),'raw native declaration inventory differs')
    diagnostic_extension_deltas=[]
    if lineage.get('status')=='PASS_BOUNDED_SINGLE_SOURCE_THEOREM_GENERATED_NATIVE_FAMILY':
        commands=lineage['source_parser_declaration_commands']
        c.require(len(commands)==1 and len(lineage['native_origins'])==lineage['actual_native_owned_names'],
                  'ambiguous source command ownership')
        c.require('Exactly one source-authored theorem' in lineage['source_parser_declared_kind'],'source-authored roster ambiguous')
        for r in lineage['compile_receipt_pin_replay']:
            label=r['label'];sha=auth['source_before_sha256'] if label=='original' else auth['source_after_sha256']
            c.require(r['returncode']==0 and r['source_sha256_verified'] and r['object_sha256_verified'] and r['source_sha256']==sha,
                      'source/object/compiler provenance mismatch')
        family={r['name'] for r in lineage['native_origins']}
        c.require(family==set(a.records),'parentage/native family mismatch')
        matcher_rows={r['name']:r for r in lineage['native_matcher_records']}
        source_authored=[parent]
    elif lineage.get('status')=='PASS_PARSER_COMMAND_AND_NATIVE_MATCHER_LINEAGE':
        c.require('supplement_seal' in inputs,'unsealed extended parser/native lineage')
        c.require(lineage['before_source_sha256']==auth['source_before_sha256'] and lineage['after_source_sha256']==auth['source_after_sha256'],
                  'lineage source binding')
        c.require(lineage['all_nonparent_parser_command_bytes_identical'] and lineage['all_edit_spans_within_owned_theorem_parser_command'] and
                  lineage['only_changed_parser_command']['owned_source_theorem'] and
                  lineage['only_changed_parser_command']['declared_short_name_raw']=='`'+parent.rsplit('.',1)[-1],
                  'ambiguous or additional source command changes')
        c.require(lineage['all_235_module_origins_match'] and lineage['all_native_lineage_fields_equal_except_parent_end_range'] and
                  lineage['splitter_value_head_is_registered_matcher'] and lineage['no_owned_family_instance_registrations'] and
                  lineage['other_native_extension_entry_counts_identical'],
                  'native matcher/extension lineage drift')
        diagnostic_extension_deltas=lineage['native_extension_entry_count_deltas']
        c.require(lineage['native_extension_entry_roster_identical'] or diagnostic_extension_deltas and all(r['extension']=='Lean.Linter.lintLogExt' for r in diagnostic_extension_deltas),'non-diagnostic extension roster drift')
        c.require(lineage['native_declarations']==len(a.records),'native lineage census mismatch')
        family=set(lineage['native_family'])
        matcher_rows={}
        for key in ['registered_matcher','private_splitter']:
            left,right=lineage[key]['before'],lineage[key]['after']
            c.require(left==right,'matcher or splitter registration drift')
            matcher_rows[left['name']]=left
        # Source-authored names are obtained from the sealed parser input, rather
        # than classifying helpers by Name spelling or absent source ranges.
        native_inputs=[r for r in supplement['owned_artifacts'] if Path(r['path']).name=='BASELINE_NATIVE_LINEAGE.json']
        c.require(len(native_inputs)==1,'missing sealed parser source roster')
        parser=pinned(native_inputs[0])
        shorts={r['declared_short_name_raw'] for r in parser['parsed_source_commands'] if r['declared_short_name_raw'] is not None}
        c.require(not any(a.records[n]['kernel_name_raw'] in shorts or '`'+n.rsplit('.',1)[-1] in shorts for n in names),
                  'source-authored declaration in finite helper roster')
        source_authored=[parent]
    else:
        raise ValueError('missing supported sealed compiler/parser parentage')
    c.require(scope['before_source_sha256']==auth['source_before_sha256'] and scope['after_source_sha256']==auth['source_after_sha256'],
              'source authorization drift')
    c.require(parent in family and family<=set(a.records) and set(names)<=family,'helper outside exact compiler family')
    for n in names:
        if a.records[n]['kind']=='definition':
            c.require(n in matcher_rows and (matcher_rows[n]['matcher_info'] is not None or matcher_rows[n]['value_head_constant'] in family),
                      'nonproof matcher/splitter lacks compiler lineage')
    records={}
    for n in names:
        c.require(a.records[n]['kind']==b.records[n]['kind'] and a.records[n]['kernel_name_raw']==b.records[n]['kernel_name_raw'] and
                  a.records[n]['ordered_universes_raw']==b.records[n]['ordered_universes_raw'],'raw constant/native universe drift')
        row=dict(name=n,kind=a.records[n]['kind'],status='PERMITTED_COMPILER_GENERATED_BINDER_RENUMBERING',
                 strict_type_equal=a.digest(n,'type')==b.digest(n,'type'),strict_value_equal=a.digest(n,'value')==b.digest(n,'value'),
                 before_type_hash=a.digest(n,'type'),after_type_hash=b.digest(n,'type'),before_value_hash=a.digest(n,'value'),after_value_hash=b.digest(n,'value'))
        row['raw_type_binder_deltas']=binder_delta(a,b,a.root(n,'type'),b.root(n,'type'))
        row['raw_value_binder_deltas']=binder_delta(a,b,a.root(n,'value'),b.root(n,'value'))
        if row['kind']=='definition' and matcher_rows[n]['matcher_info'] is None:
            c.require(row['strict_value_equal'],'native splitter computational/value payload must remain literally exact')
        c.require(row['raw_type_binder_deltas'],'listed helper has no observed type binder change')
        records[n]=row
    result=dict(status='PASS_FINITE_RAW_BINDER_AUDIT_NOT_FINAL_ADMISSION',records=records,
                exact_family=sorted(family),source_authored_roster=source_authored,protected_roster=protected_roots,
                inputs=inputs,authorization_sha256=inputs['authorization']['sha256'],
                source_before_sha256=auth['source_before_sha256'],source_after_sha256=auth['source_after_sha256'],
                normal_strict_mode='FAIL_RETAINED',final_after_consumers_pending=True)
    if diagnostic_extension_deltas:result['diagnostic_extension_entry_count_deltas']=diagnostic_extension_deltas
    return result


def admit_group(policy,before,after,before_path,after_path):
    expected=pinned(policy['raw_audit'])
    actual=audit(expected['inputs'],before['roots'])
    c.require(actual==expected,'raw accounting audit drift or extra fields')
    receipt=pinned(policy['source_consumer_receipt'])
    c.require(receipt.get('status')=='PASS' and receipt.get('outside_consumers')==[],'source/extension outside-family consumer')
    c.require(receipt.get('before_snapshot_sha256')==c.file_hash(before_path) and receipt.get('after_snapshot_sha256')==c.file_hash(after_path),
              'source consumer census is not bound to full final snapshots')
    c.require(set(receipt.get('exact_names',[]))==set(actual['records']) and
              set(receipt.get('exact_family',[]))==set(actual['exact_family']),'source consumer scope mismatch')
    c.require(receipt.get('source_before_sha256')==actual['source_before_sha256'] and receipt.get('source_after_sha256')==actual['source_after_sha256'],
              'source consumer source-pin mismatch')
    c.require(receipt.get('checked_source_spellings') is True and receipt.get('checked_applicable_extensions') is True,
              'incomplete source/extension consumer audit')
    names=set(actual['records']);family=set(actual['exact_family'])
    for label,doc in [('before',before),('after',after)]:
        for n,r in doc['records'].items():
            c.require(not names.intersection(r['dependencies']) or n in family,'outside-family native consumer in '+label+': '+n)
        for n,row in actual['records'].items():
            c.require(n in doc['records'],'missing finite helper')
            r=doc['records'][n]
            c.require(r['type_hash']==row[label+'_type_hash'] and r['value_hash']==row[label+'_value_hash'] and r['kind']==row['kind'],
                      'full snapshot differs from pinned finite raw payload: '+n)
    for n in names:
        x,y=before['records'][n],after['records'][n]
        sx,sy=c.semantic_record(x),c.semantic_record(y)
        sx.pop('type_hash');sy.pop('type_hash')
        c.require(sx==sy and x['dependencies']==y['dependencies'] and x['axioms']==y['axioms'],'additional finite-helper field drift: '+n)
    return actual['records'],dict(raw_audit=policy['raw_audit'],source_consumer_receipt=policy['source_consumer_receipt'],
                                full_native_consumer_census='PASS_BOTH_COMPLETE_SNAPSHOTS')


def admit(policy_path,before,after,before_path,after_path):
    policy=c.read(policy_path)
    groups=policy.get('groups',[policy])
    c.require(isinstance(groups,list) and groups,'empty finite binder scope')
    records={};pins=[]
    for group in groups:
        rows,proof=admit_group(group,before,after,before_path,after_path)
        c.require(not records.keys() & rows.keys(),'overlapping finite helper groups')
        records.update(rows);pins.append(proof)
    return records,dict(groups=pins)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--authorization',required=True);p.add_argument('--before-dag',required=True);p.add_argument('--after-dag',required=True)
    p.add_argument('--lineage',required=True);p.add_argument('--roots',required=True);p.add_argument('--out',required=True)
    p.add_argument('--supplement-seal',help='bounded frozen handoff seal for extended native/parser lineage')
    a=p.parse_args()
    try:
        inputs={k:pin(getattr(a,k)) for k in ['authorization','before_dag','after_dag','lineage']}
        if a.supplement_seal:inputs['supplement_seal']=pin(a.supplement_seal)
        result=audit(inputs,c.read(a.roots));c.write(a.out,result)
        print(json.dumps(dict(status=result['status'],helpers=len(result['records']),out=a.out)))
    except (ValueError,KeyError,OSError,IndexError) as e:
        print(json.dumps(dict(status='FAIL',error=str(e))))
        return 1
    return 0

if __name__=='__main__':raise SystemExit(main())
