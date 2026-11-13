# Linear programme over length-class histograms bounding header + excess (see ../README.md).
# Usage: python3 header_lp.py <lit_bufsize> <Delta> choice|nochoice   (needs ./lpsolve built from lpsolve.c)
import sys, subprocess
def optcode(f):
    # optimal 7-limited code lengths for (fractional) weights f over 19 symbols, all symbols present
    w=[max(1e-6,v) for v in f]
    sc=[int(v*1000)+1 for v in w]
    items=sorted([(sc[i],i) for i in range(19)])
    leaves=[(wt,(i,)) for wt,i in items]
    pk=leaves[:]
    for _ in range(6):
        pk.sort(key=lambda x:x[0])
        merged=[(pk[j][0]+pk[j+1][0],pk[j][1]+pk[j+1][1]) for j in range(0,len(pk)-1,2)]
        pk=sorted(leaves+merged,key=lambda x:x[0])
    sel=pk[:2*19-2]; ln=[0]*19
    for wt,ids in sel:
        for i in ids: ln[i]+=1
    return ln
class hlp: pass
hlp.optcode=staticmethod(optcode)
F=[0,1]
for i in range(40): F.append(F[-1]+F[-2])
L=int(sys.argv[1]); W=L+2; DELTA=float(sys.argv[2]); USECHOICE=sys.argv[3]=='choice'
M=max(x for x in range(1,16) if F[x+2]<=W)
fmax=[0]+[(W-F[x])//F[x+1] for x in range(1,M+1)]
Acls=[(0,9)]+[(e,4) for e in range(1,6)]                 # (extra, #codes) length classes
Dcls=[(4,10)]+[(e,2) for e in range(5,14)]               # dist: e<=4 grouped (10 codes)
V={}
def var(name):
    if name not in V: V[name]=len(V)
    return V[name]
for x in range(1,M+1):
    var(('cL',x)); var(('FL',x))
    for a,_ in Acls: var(('cA',a,x)); var(('FA',a,x))
    for g,_ in Dcls: var(('cD',g,x)); var(('FD',g,x))
for r in ('a1','a2','a3','a11','t'): var(r)
NV=len(V)
def lp(table):
    rows=[]
    def add(coef,b): rows.append((coef,b))
    add({V[('cL',x)]:2.0**-x for x in range(1,M+1)} | {V[('cA',a,x)]:2.0**-x for a,_ in Acls for x in range(1,M+1)},1.0)
    add({V[('cD',g,x)]:2.0**-x for g,_ in Dcls for x in range(1,M+1)},1.0)
    add({V[('cL',x)]:1 for x in range(1,M+1)},256)
    for a,n in Acls: add({V[('cA',a,x)]:1 for x in range(1,M+1)},n)
    for g,n in Dcls: add({V[('cD',g,x)]:1 for x in range(1,M+1)},n)
    pairs=[(('cL',x),('FL',x)) for x in range(1,M+1)]+[(('cA',a,x),('FA',a,x)) for a,_ in Acls for x in range(1,M+1)]+[(('cD',g,x),('FD',g,x)) for g,_ in Dcls for x in range(1,M+1)]
    for c,f in pairs:
        x=c[-1]
        add({V[c]:1,V[f]:-1},0); add({V[f]:1,V[c]:-fmax[x]},0)
    add({V[('FL',x)]:1 for x in range(1,M+1)} | {V[('FA',a,x)]:1 for a,_ in Acls for x in range(1,M+1)},L-1)
    bal={V[('FA',a,x)]:1 for a,_ in Acls for x in range(1,M+1)}; bal.update({V[('FD',g,x)]:-1 for g,_ in Dcls for x in range(1,M+1)})
    add(bal,0); add({k:-v for k,v in bal.items()},0)
    cs=[c for c,f in pairs]
    r={V[c]:-1 for c in cs}; r.update({V['a1']:1,V['a2']:1,V['a3']:1,V['a11']:1}); add(r,1)
    r={V[c]:1 for c in cs}; r.update({V['a1']:1,V['a2']:2,V['a3']:3,V['a11']:11}); add(r,316)
    for k in table:
        rep=(k[16]+2)/3.0
        r={V['t']:1}
        for c in cs: r[V[c]]=-max(k[c[-1]],rep)
        r[V['a1']]=-k[0]; r[V['a2']]=-2*k[0]; r[V['a3']]=-(k[17]+3); r[V['a11']]=-(k[18]+7)
        add(r,71+2*(k[18]+7+2*k[0])+7+DELTA)
    if USECHOICE:
        r={V['t']:1}
        for x in range(1,M+1):
            r[V[('FL',x)]]=-(9-x)
            for a,_ in Acls: r[V[('FA',a,x)]]=-(8-x)
            for g,_ in Dcls: r[V[('FD',g,x)]]=-(5-x)
        add(r,11)
    obj={V['t']:1}
    for x in range(1,M+1):
        for a,_ in Acls: obj[V[('FA',a,x)]]=max(0,x+a-9)
        for g,_ in Dcls: obj[V[('FD',g,x)]]=max(0,x+g-15)
    s=[f"{len(rows)} {NV}"]
    for coef,b in rows:
        row=['0']*NV
        for k,v in coef.items(): row[k]=repr(v)
        s.append(' '.join(row)+' '+repr(b))
    row=['0']*NV
    for k,v in obj.items(): row[k]=repr(v)
    s.append(' '.join(row))
    try:
        out=subprocess.run(['./lpsolve'],input='\n'.join(s),capture_output=True,text=True,timeout=20).stdout.split('\n')
    except subprocess.TimeoutExpired:
        out=['timeout','','']
    return float(out[0]), list(map(float,out[1].split())), list(map(float,out[2].split()))
table=[[4,5,5,5,5,5,5,4,4,4,4,4,5,5,5,5,5,4,4]]
for it in range(200):
    val,x,du=lp(table)
    f=[0.0]*19
    for (k,*rest),i in V.items():
        if k in ('cL','cA','cD'): f[rest[-1]]+=x[i]
    f[0]=x[V['a1']]+2*x[V['a2']]; f[17]=x[V['a3']]; f[18]=x[V['a11']]; f[16]=0.3
    kk=hlp.optcode(f)
    if kk in table: break
    table.append(kk)
E=val-x[V['t']]
print(L,'choice' if USECHOICE else 'nochoice','Delta',DELTA,'bound',round(val,1),'budget',8*L-25,'margin',round(8*L-25-val,1),'t',round(x[V['t']],1),'E',round(E,1),'refs',len(table))
nd=[round(d,3) for d in du]
nk=len(table); kd=nd[-nk-(1 if USECHOICE else 0):]
print('nonzero duals',sum(1 for d in nd if abs(d)>1e-6),'of',len(nd),'kappa rows with weight',sum(1 for d in kd if abs(d)>1e-6), [d for d in kd if abs(d)>1e-6])
for k,d in zip(table,kd[:nk]):
    if abs(d)>1e-6: print(' kappa',k,'weight',d)
