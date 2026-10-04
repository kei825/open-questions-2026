#!/usr/bin/env python3
# Structured CNF: C4-free k-regular graph on N vertices (valid when N <= 1+(k+1)+(k+1)(k-1)-2*floor((k+1)/2) - 1),
# vertex 0 has m0 matched pairs in N(0). Prints CNF and the twin classes (for lex-leader) on stderr.
import sys, itertools
N=int(sys.argv[1]); k=int(sys.argv[2]); m0=int(sys.argv[3])
var={}
for i in range(N):
    for j in range(i+1,N): var[(i,j)]=len(var)+1
nv=len(var)
def e(a,b): return var[(a,b)] if a<b else var[(b,a)]
cl=[]
for u in range(1,N): cl.append([e(0,u)] if u<=k else [-e(0,u)])
mate={}
for p in range(m0): mate[2*p+1]=2*p+2; mate[2*p+2]=2*p+1
blocks={}; nxt=k+1
for i in range(1,k+1):
    sz=k-2 if i in mate else k-1
    blocks[i]=range(nxt,nxt+sz); nxt+=sz
rest=range(nxt,N)
assert nxt<=N, 'too few vertices'
for i in range(1,k+1):
    for j in range(i+1,k+1): cl.append([e(i,j)] if mate.get(i)==j else [-e(i,j)])
    for u in range(k+1,N): cl.append([e(i,u)] if u in blocks[i] else [-e(i,u)])
for q in itertools.combinations(range(N),4):
    a,b,c,d=q
    for x,y,z,w in ((a,b,c,d),(a,b,d,c),(a,c,b,d)):
        cl.append([-e(x,y),-e(y,z),-e(z,w),-e(w,x)])
def atmost(lits,m):
    global nv
    if m<0: cl.append([]); return
    if m==0:
        for x in lits: cl.append([-x])
        return
    if m>=len(lits): return
    s=[[0]*m for _ in lits]
    for i in range(len(lits)):
        for j in range(m): nv+=1; s[i][j]=nv
    for i,x in enumerate(lits):
        cl.append([-x,s[i][0]])
        if i>0:
            for j in range(m): cl.append([-s[i-1][j],s[i][j]])
            for j in range(1,m): cl.append([-x,-s[i-1][j-1],s[i][j]])
            cl.append([-x,-s[i-1][m-1]])
for v in range(k+1,N):
    L=[e(v,u) for u in range(N) if u!=v]
    atmost(L,k); atmost([-l for l in L],len(L)-k)
print('p cnf %d %d'%(nv,len(cl)))
for c in cl: print(' '.join(map(str,c)),0)
cls=[f'{b.start}-{b.stop}' for b in blocks.values()]+([f'{rest.start}-{rest.stop}'] if len(rest)>1 else [])
sys.stderr.write(','.join(cls)+'\n')
