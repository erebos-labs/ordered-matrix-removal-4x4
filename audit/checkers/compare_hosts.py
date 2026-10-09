"""Independent interval-order reconstruction from report.tex; no supplied host code imported."""
from fractions import Fraction
from pathlib import Path
import json,hashlib,itertools
BASE=Path(__file__).resolve().parents[1]

def axes(h,col):
 m=2**h
 anchors=[('A',l,k,g,a) for l in range(1,h+1) for k in range(6) for g in range(2) for a in range(m)]
 nodes=[]
 for i in range(h):
  for p in range(2**i):
   for sig in (False,True):
    opening=sig==col
    key=(Fraction(p if opening else p+1,2**i),1 if opening else 0,i if opening else -i)
    for a in range(2**(h-i)):nodes.append((key,a,('T',i,int(sig),p,a)))
 for p in range(m):nodes.append(((Fraction(2*p+1,2*m),1,h),0,('T',h,1,p,0)))
 var=[x[2] for x in sorted(nodes)]
 dummy=[('D',a) for a in range(m)]
 return anchors+(dummy+var if col else var+dummy)

def role(h,l,k,g,x,col):
 if x[0]=='A':return False
 if x[0]=='D':return (k in (0,1) and g==0) if col else (k in (2,3,4,5) and g==1)
 _,i,s,p,a=x
 plus=s==1 or i==h;minus=s==0 or i==h
 if not col:
  tests=[((g==0 and i==l) or (g==1 and i+1==l)) and plus,
         ((g==0 and i+1==l) or (g==1 and i==l)) and minus,
         g==0 and i==l and plus and p%2==k-2,
         g==0 and i==l and minus and p%2==k-4]
 else:
  tests=[g==1 and i+1==l and plus,g==1 and i+1==l and minus,
         plus and ((g==0 and i+1==l) or (g==1 and i==l and p%2==k-2)),
         minus and ((g==0 and i==l and p%2==k-4) or (g==1 and i+1==l))]
 return tests[0 if k==0 else 1 if k==1 else 2 if k<4 else 3]

def entry(h,r,c):
 if r[0]==c[0]=='A':return int(r[1:3]==c[1:3] and r[3]!=c[3])
 if r[0]=='A':return int(role(h,*r[1:4],c,True))
 if c[0]=='A':return int(role(h,*c[1:4],r,False))
 if r[0]=='D' or c[0]=='D':return 1
 _,i,s,p,_=r;_,j,t,q,_=c
 if i==j:
  if (s or i==h) and (t or j==h):return int(p<=q)
  if i<h and s==t==0:return int(p<q)
 if i==j+1:
  if (s or i==h) and t==1:return int(p//2<=q)
  if (not s or i==h) and t==0:return int(p//2<q)
 return 0

def text(tags):return [''.join(map(str,(entry(h,r,c) for c in cc))) for r in rr]
results=[]
for h in (1,2,3):
 rr,cc=axes(h,False),axes(h,True);n=(14*h+2)*2**h
 assert len(rr)==len(cc)==n and len(set(rr))==len(set(cc))==n
 for name,tags in [('r',rr),('c',cc)]:
  expected=[','.join(map(str,t)) for t in tags]
  actual=(BASE/f'evidence/lean-axis-{name}-h{h}.txt').read_text().splitlines();assert actual==expected,(h,name)
 expected='\n'.join(text((rr,cc)))+'\n';actual=(BASE/f'evidence/lean-host-h{h}.txt').read_text();assert actual==expected,h
 results.append({'h':h,'n':n,'cells':n*n,'axes':2*n,'matrix_sha256':hashlib.sha256(actual.encode()).hexdigest(),'passed':True})
# Supplement: reproduce exact finite all-bit copy counts in the independently built h1 host.
h=1;rr,cc=axes(h,False),axes(h,True);H=['0110','1001','1010','0111'];N=len(rr)
rowbits=[sum(entry(h,r,c)<<j for j,c in enumerate(cc)) for r in rr];allbits=(1<<N)-1;count=0
for ris in itertools.combinations(range(N),4):
 masks=[]
 for j in range(4):
  mask=allbits
  for i in range(4):mask&=rowbits[ris[i]] if H[i][j]=='1' else ~rowbits[ris[i]]
  masks.append(mask)
 dp=[int(bool(masks[0] & (1<<j))) for j in range(N)]
 for stage in range(1,4):
  acc=0;new=[]
  for j in range(N):new.append(acc if masks[stage]&(1<<j) else 0);acc+=dp[j]
  dp=new
 count+=sum(dp)
assert count==128,count
out={'method':'independent rational interval order and literal report entry/role tables','coverage':'finite h=1,2,3; not an all-depth proof','results':results,'h1_exhaustive_ordinary_copy_count':count}
(BASE/'evidence/independent-host-comparison.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
