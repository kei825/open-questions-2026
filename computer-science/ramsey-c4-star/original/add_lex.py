# Append lex-leader constraints for vertex transpositions (x y) within given twin classes to a graph CNF on N vertices.
import sys, itertools
cnf, N, classes_spec = sys.argv[1], int(sys.argv[2]), sys.argv[3]
classes=[list(range(int(a),int(b))) for a,b in (c.split('-') for c in classes_spec.split(','))]
lines=open(cnf).read().split('\n')
hdr=lines[0].split(); nv=int(hdr[2]); body=[l for l in lines[1:] if l.strip()]
var={}; k=0
for i in range(N):
    for j in range(i+1,N): k+=1; var[(i,j)]=k
pairs=sorted(var)
new=[]
def lexleq(xs,ys):
    global nv
    prev=None
    for x,y in zip(xs,ys):
        if x==y: continue
        new.append(([-x,y] if prev is None else [-prev,-x,y]))
        nv+=1; e=nv
        if prev is None: new.append([x,y,e]); new.append([-x,-y,e])
        else: new.append([-prev,x,y,e]); new.append([-prev,-x,-y,e])
        prev=e
for cls in classes:
    for a,b in zip(cls, cls[1:]):   # adjacent transpositions within class
        sig=list(range(N)); sig[a],sig[b]=sig[b],sig[a]
        xs=[var[p] for p in pairs]
        ys=[var[tuple(sorted((sig[p[0]],sig[p[1]])))] for p in pairs]
        lexleq(xs,ys)
print('p cnf %d %d'%(nv,len(body)+len(new)))
print('\n'.join(body))
for c in new: print(' '.join(map(str,c)),0)
