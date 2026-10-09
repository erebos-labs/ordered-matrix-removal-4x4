"""Independent, standard-library audit of the PDF's Sections 3--7.

No supplied research code or certificates are imported. Run from task root:
python3 evidence/audit_checker.py --max-depth 5 --output evidence/checks.json
"""
import argparse
import hashlib
import itertools
import json
import math
import time
from pathlib import Path
from fractions import Fraction

H = ((0,1,1,0),(1,0,0,1),(1,0,1,0),(0,1,1,1))

def build(h, reverse=False):
    m = 2**h
    modes = []
    for i in range(1,h+1):
        modes += [(i,'V+',None),(i,'V-',None),(i,'W+',0),(i,'W+',1)]
        modes += [(i,'W-',d) for d in ((1,0) if reverse else (0,1))]
    anchors = [('A',)+t+(g,) for t in modes for g in (1,2)]
    def tree(i,p,axis):
        if i == h:
            return [('T',i,p,'L')]
        opening,closing = ('-','+') if axis == 'R' else ('+','-')
        return [('T',i,p,opening)] + tree(i+1,2*p,axis) + tree(i+1,2*p+1,axis) + [('T',i,p,closing)]
    rows = anchors + tree(0,0,'R') + [('D',)]
    cols = anchors + [('D',)] + tree(0,0,'C')
    def role(x,t,axis):
        i,k,d = t
        if x[0] == 'D':
            return (2 if k.startswith('W') else 0) if axis == 'R' else (1 if k.startswith('V') else 0)
        if x[0] != 'T':
            return 0
        _,j,p,s = x
        signed = lambda sign: s == sign or s == 'L'
        if axis == 'R':
            if k == 'V+':
                return 1 if j==i and signed('+') else 2 if j==i-1 and signed('+') else 0
            if k == 'V-':
                return 1 if j==i-1 and signed('-') else 2 if j==i and signed('-') else 0
            return 1 if j==i and signed(k[-1]) and p%2==d else 0
        if k.startswith('V'):
            return 2 if j==i-1 and signed(k[-1]) else 0
        if k == 'W+':
            return 1 if j==i-1 and signed('+') else 2 if j==i and signed('+') and p%2==d else 0
        return 1 if j==i and signed('-') and p%2==d else 2 if j==i-1 and signed('-') else 0
    def entry(r,c):
        if r[0]=='A' and c[0]=='A':
            return int(r[1:4]==c[1:4] and r[4]!=c[4])
        if r[0]=='A':
            return int(role(c,r[1:4],'C')==r[4])
        if c[0]=='A':
            return int(role(r,c[1:4],'R')==c[4])
        if r[0]=='D' or c[0]=='D':
            return 1
        _,i,p,s = r
        _,j,q,u = c
        if i==h:
            return int((j==h and p<=q) or (j==h-1 and ((u=='+' and p//2<=q) or (u=='-' and p//2<q))))
        if s!=u:
            return 0
        if j==i:
            return int(p<=q if s=='+' else p<q)
        if j==i-1:
            return int(p//2<=q if s=='+' else p//2<q)
        return 0
    weights = lambda x: m if x[0] in ('A','D') else 2**(h-x[1])
    A = [[entry(r,c) for c in cols] for r in rows]
    rw,cw = list(map(weights,rows)),list(map(weights,cols))
    if sum(rw)!=(14*h+2)*m or sum(cw)!=sum(rw):
        raise ValueError('host size')
    return rows,cols,A,rw,cw

def exhaustive(rows,cols,A,rw,cw):
    """All column quadruples, bit intersections, then all increasing row chains."""
    n=len(rows); full=(1<<n)-1
    masks=[sum(A[r][c]<<r for r in range(n)) for c in range(n)]
    pairs={}
    for a,b in itertools.combinations(range(n),2):
        x,y=masks[a],masks[b]
        pairs[a,b]=((full^x)&y,x&(full^y),x&y)
    found={}
    for a,b,c,d in itertools.combinations(range(n),4):
        ab01,ab10,_=pairs[a,b]
        cd01,cd10,cd11=pairs[c,d]
        s0,s1,s2,s3=ab01&cd10,ab10&cd01,ab10&cd10,ab01&cd11
        if not (s0 and s1 and s2 and s3):
            continue
        while s0:
            bit0=s0&-s0; s0-=bit0; r0=bit0.bit_length()-1
            t1=s1&~((bit0<<1)-1)
            while t1:
                bit1=t1&-t1; t1-=bit1; r1=bit1.bit_length()-1
                t2=s2&~((bit1<<1)-1)
                while t2:
                    bit2=t2&-t2; t2-=bit2; r2=bit2.bit_length()-1
                    t3=s3&~((bit2<<1)-1)
                    while t3:
                        bit3=t3&-t3; t3-=bit3; r3=bit3.bit_length()-1
                        rr=(r0,r1,r2,r3); cc=(a,b,c,d)
                        if tuple(tuple(A[r][v] for v in cc) for r in rr)!=H:
                            raise ValueError('bitset enumeration error')
                        found[rr+cc]=math.prod(rw[r] for r in rr)*math.prod(cw[v] for v in cc)
    return found

def families(h,rows,cols,rw,cw):
    """Generate symbolic families separately from entry evaluation/search."""
    ri={x:i for i,x in enumerate(rows)}; ci={x:i for i,x in enumerate(cols)}
    out={}; counts=[0,0,0]
    def add(rs,cs,f):
        rr=tuple(ri[x] for x in rs); cc=tuple(ci[x] for x in cs)
        if tuple(sorted(rr))!=rr or tuple(sorted(cc))!=cc:
            raise ValueError('family order')
        key=rr+cc
        if key in out:
            raise ValueError('overlapping families')
        out[key]=math.prod(rw[x] for x in rr)*math.prod(cw[x] for x in cc)
        counts[f]+=out[key]
    an=lambda k,d,g: ('A',h,k,d,g)
    M=2**(h-1)
    for p in range(2*M):
        b,d=divmod(p,2)
        add([an('W-',d,1),an('W-',d,2),('T',h,p,'L'),('D',)],
            [an('W-',d,1),an('W-',d,2),('T',h,p,'L'),('T',h-1,b,'-')],0)
    for a,b in itertools.combinations(range(M),2):
        for d in (0,1):
            first=[an('V+',None,2),an('W+',0,1),an('W+',1,1)]
            if h>=2 and a%2==b%2:
                first += [('A',h-1,'W+',a%2,2)]
            for r in first:
                add([r,an('W-',d,2),('T',h,2*b+d,'L'),('D',)],
                    [an('W-',d,1),('T',h-1,a,'+'),('T',h-1,b,'+'),('T',h-1,b,'-')],1)
    for p in range(2*M):
        b,d=divmod(p,2)
        for q0 in range(p):
            for q1 in range(p,2*b+2):
                if q0%2!=q1%2:
                    continue
                e=q0%2
                first=[an('W+',e,2)]
                if e<=d:
                    first += [an('W-',e,1)]
                for r in first:
                    add([r,an('W-',d,2),('T',h,p,'L'),('D',)],
                        [an('W-',d,1),('T',h,q0,'L'),('T',h,q1,'L'),('T',h-1,b,'-')],2)
    return out,counts

def structural(h,rows,cols,A):
    def cls(x):
        return x[:2]+(x[3],) if x[0]=='T' else x
    nr=[i for i,x in enumerate(rows) if x[0]!='A']
    nc=[j for j,x in enumerate(cols) if x[0]!='A']
    for axis,positions,opposite,mat in [('R',rows,nc,A),('C',cols,nr,list(map(list,zip(*A))))]:
        groups={}
        for i,x in enumerate(positions):
            if x[0]=='T': groups.setdefault(cls(x),[]).append(i)
        for ids in groups.values():
            traces=[{j for j in opposite if mat[i][j]} for i in ids]
            for a,b in itertools.combinations(traces,2):
                if not (a<=b or b<=a): raise ValueError('nesting')
            ac=[j for j,x in enumerate(cols if axis=='R' else rows) if x[0]=='A']
            if len({tuple(mat[i][j] for j in ac) for i in ids})>2:
                raise ValueError('anchor signatures')
    crown_tests=0
    for cc in itertools.combinations(nc,3):
        candidates={v:[] for v in (3,5,6)}
        for r in nr:
            v=sum(A[r][c]<<j for j,c in enumerate(cc))
            if v in candidates: candidates[v].append(r)
        crown_tests+=1
        if all(candidates.values()): raise ValueError('nonanchor crown')
    return {'nested_both_axes':True,'at_most_two_signatures':True,'crown_column_triples':crown_tests}

def local_arithmetic():
    residue_checks=0
    for p,q in itertools.product(range(128),repeat=2):
        if p%2==q%2 and p//2<=q//2 and not p<=q: raise ValueError('residue')
        if p<q and q//2<=p//2 and not (p%2==0 and q==p+1): raise ValueError('siblings')
        residue_checks+=1
    # A state is the two same-level signed diagonal bits. Each transition has
    # two cross-level bits. Avoid all four P bodies in a mode frame.
    transitions=[]
    for old in itertools.product((0,1),repeat=2):
        new=set()
        for a,b,u,v in itertools.product((0,1),repeat=4):
            bodies=(((1,a),(1,old[0])),((1,old[1]),(1,b)),((a,u),(1,1)),((v,b),(1,1)))
            if all(B!=((1,0),(1,1)) for B in bodies): new.add((u,v))
        transitions.append({'old':old,'allowed_next':sorted(new)})
        if old==(1,0) and new!={(1,0)}: raise ValueError('propagation')
    sampling=[]
    for h in range(1,9):
        m=2**h
        for i in range(h+1):
            prob=Fraction(1,2**i)*Fraction(1,2**(h-i))*Fraction(1,m)
            if prob!=Fraction(1,m*m): raise ValueError('protected probability')
        sampling.append({'h':h,'protected_cell_probability':str(Fraction(1,m*m))})
    return {'integer_pairs_checked':residue_checks,'boolean_transition_table':transitions,'sampling':sampling}

def extra_checks():
    # A second tree-order description via exact dyadic endpoints.
    order_checks=[]
    for h in range(1,9):
        rows,cols,A,rw,cw=build(h)
        for axis,positions in [('R',rows),('C',cols)]:
            variables=[x for x in positions if x[0]=='T']
            def key(x):
                _,i,p,s=x
                if s=='L': return (Fraction(2*p+1,2**(i+1)),0)
                opening=(s=='-' if axis=='R' else s=='+')
                return (Fraction(p if opening else p+1,2**i),i if opening else -i)
            if variables!=sorted(variables,key=key): raise ValueError('dyadic order')
        order_checks.append(h)
    rows,cols,A,rw,cw=build(1)
    er=[r for r,w in zip(rows,rw) for _ in range(w)]
    ec=[c for c,w in zip(cols,cw) for _ in range(w)]
    ri=[i for i,w in enumerate(rw) for _ in range(w)]
    ci=[i for i,w in enumerate(cw) for _ in range(w)]
    EA=[[A[r][c] for c in ci] for r in ri]
    full=exhaustive(er,ec,EA,[1]*len(er),[1]*len(ec))
    if len(full)!=128: raise ValueError('expanded depth one')
    rows,cols,A,rw,cw=build(2)
    old=exhaustive(rows,cols,A,rw,cw)
    changes=[]
    for r,x in enumerate(rows):
        if x[0]=='T' and x[1]==2:
            c=cols.index(('T',1,x[2]//2,'-'))
            if A[r][c]!=0: raise ValueError('sparse zero value')
            A[r][c]=1; changes.append((r,c))
    after=exhaustive(rows,cols,A,rw,cw)
    if set(after)&set(old): raise ValueError('original copy survived sparse flip')
    if not after: raise ValueError('new copies expected')
    key=min(after)
    return {'dyadic_order_depths':order_checks,'expanded_depth_one':{'n':32,'column_quadruples':math.comb(32,4),'copies':len(full)},'sparse_zero_flip_depth_two':{'actual_edits':sum(rw[r]*cw[c] for r,c in changes),'distance_lower_bound':16,'original_block_copies':len(old),'surviving_original_block_copies':len(set(after)&set(old)),'new_block_copies':len(after),'new_expanded_copies':sum(after.values()),'witness_rows':[rows[x] for x in key[:4]],'witness_columns':[cols[x] for x in key[4:]]}}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--max-depth',type=int,default=5); ap.add_argument('--output',default='evidence/checks.json'); args=ap.parse_args()
    result={'pattern':H,'method':'independent column-quadruple bitset exhaustion; exact integer weights','depths':[],'local_checks':local_arithmetic(),'extra_checks':extra_checks()}
    for h in range(1,args.max_depth+1):
        start=time.monotonic(); rows,cols,A,rw,cw=build(h)
        s=structural(h,rows,cols,A); found=exhaustive(rows,cols,A,rw,cw); predicted,counts=families(h,rows,cols,rw,cw)
        if found!=predicted: raise ValueError(('family mismatch',h,len(found),len(predicted)))
        for key in found:
            r=rows[key[2]]; c=cols[key[7]]
            if not (r[0]=='T' and r[1]==h and c==('T',h-1,r[2]//2,'-')): raise ValueError('localization')
            if rows[key[3]]!=('D',): raise ValueError('dummy fourth row')
        m=2**h; expected=128 if h==1 else (41*m**6-74*m**5)//4
        if sum(found.values())!=expected: raise ValueError('count')
        records=[{'rows':[rows[x] for x in key[:4]],'columns':[cols[x] for x in key[4:]],'weight':weight} for key,weight in sorted(found.items())]
        path=Path(f'evidence/copies_h{h}.json'); path.write_text(json.dumps(records,indent=2)+'\n')
        item={'h':h,'n':sum(rw),'block_order':len(rows),'column_quadruples':math.comb(len(cols),4),'block_copies':len(found),'expanded_copies':sum(found.values()),'family_expanded_counts':counts,'all_localized':True,'family_sets_equal':True,'structure':s,'seconds':round(time.monotonic()-start,3),'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        result['depths'].append(item); print(json.dumps(item),flush=True)
    # Exact changed-order negative control, including expanded multiplicity.
    rows,cols,A,rw,cw=build(3,reverse=True)
    rs=[('A',2,'W-',1,1),('A',2,'W-',0,2),('T',2,2,'-'),('D',)]
    cs=[('A',2,'W-',0,1),('T',2,1,'-'),('T',2,3,'-'),('T',1,1,'-')]
    rr=[rows.index(x) for x in rs]; cc=[cols.index(x) for x in cs]
    if rr!=sorted(rr) or cc!=sorted(cc) or tuple(tuple(A[r][c] for c in cc) for r in rr)!=H: raise ValueError('negative control')
    result['reversed_parity_control']={'h':3,'rows':rs,'columns':cs,'weight':math.prod(rw[r] for r in rr)*math.prod(cw[c] for c in cc),'nonterminal':True}
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__': main()
