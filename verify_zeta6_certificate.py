"""Check the static zeta-six certificate using only rational arithmetic and Arb."""
from bisect import bisect_right
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Q
from functools import lru_cache
from math import comb
from pathlib import Path
import json
import sys

from flint import arb, ctx, fmpq, fmpq_mat

def A(x):
    q=Q(x)
    return arb(fmpq(q.numerator,q.denominator))

def at(line,x):
    return line[0]+line[1]*x


def order(lines,low,high,l,r):
    """Certify clipping and all relative orders by affine endpoint signs."""
    def ends(line):
        a,b=line
        return (a*l.denominator+b*l.numerator,a*r.denominator+b*r.numerator)

    L,R=ends(low),ends(high)
    active=[]
    for a in set(lines)|{low,high}:
        u,v=ends(a)
        for x,y in (L,R):
            assert (u-x)*(v-y)>=0,('unlisted clipping wall',a,l,r)
        if L[0]<=u<=R[0] and L[1]<=v<=R[1]:
            active.append((u,v,a))
    active.sort()
    assert all(a[1]<=b[1] for a,b in zip(active,active[1:])),('unlisted crossing',l,r)
    return [line for u,v,line in active]

def int_aff(u,l,r):
    return (r-l)*at(u,(l+r)/2)

def cap_int(H,u,l,r):
    a,b=at(u,l),at(u,r)
    if max(a,b)<=H:
        return (a+b)*(r-l)/2
    if min(a,b)>=H:
        return H*(r-l)
    return H*(r-l)-(H-min(a,b))**2/(2*abs(u[1]))

@lru_cache(None)
def slots(m,top,aliases,zeros,right,left):
    val=[max(0,max(r-top+(m-e-r if aliases else min(zeros,m-e-r))
                 +(e+4)*int(right!=left if e%2==0 else right>0)
                 for e in range(1,m-r+1))) for r in range(m)]
    return tuple(max(val[r:]) for r in range(m))


def blocks(U,L,Z,D):
    C=2*U+L
    return ([(2*(U+d),2*(U+L-d),1) for d in D]+
            [(0,2*z,-1) for z in Z]+[(2*(C-z),2*C,-1) for z in Z])


def raw_fold(data,C,S,Z,lines,l,r):
    x=(l+r)/2
    raw=order(lines,(C,0),(Z,0),l,r)
    normal=0
    for a,b,t in data:
        k=(b-a)//x
        assert k*r<=b-a<=(k+1)*l
        normal+=t*k
    R=[]
    for a,b in zip(raw,raw[1:]):
        u=(at(a,x)+at(b,x))/2
        p=sum((hi-u)//x-(lo-u)//x for lo,hi,t in data if t==1)
        z=sum((hi-u)//x-(lo-u)//x for lo,hi,t in data if t==-1)
        m=sum(lo<u<hi for lo,hi,t in data if t==1)
        w=slots(m,normal+z-p+m,p-m,z,(u-S)//x,(2*C-u-S)//x) if m else ()
        R.append((a,b,w))
    K=(Z-C)//l+2
    walls={(s*2*(a-C),s*2*(b-k)) for a,b in raw for s in [-1,1] for k in range(K+1)}
    fold=order(walls,(0,0),(0,1),l,r)
    widths=defaultdict(lambda:[0,0])
    values=[at(a,x) for a in raw]
    for a,b in zip(fold,fold[1:]):
        u=(at(a,x)+at(b,x))/4
        profile=[]
        for k in range(K+1):
            for s in (-1,1):
                y=C+k*x+s*u
                if C<y<Z:
                    profile.extend(j for j in R[bisect_right(values,y)-1][2] if j>0)
        label=tuple(sorted(profile,reverse=True))
        if label:
            for j in (0,1):
                widths[label][j]+=b[j]-a[j]
    return R,widths


def high(data,H,N,S,C,Z,cut,table):
    start=cut*N
    J=2*C//start+3
    lines={(e,j) for a,b,_ in data for e in (a,b) for j in range(-J,J+1)}
    lines|={(S,j) for j in range(1,J+1)}|{(2*C-S,-j) for j in range(1,J+1)}
    total=Q(0);edge=start
    for tile in table:
        l,r=N*Q(tile[0]),N*Q(tile[1])
        assert l==edge and l<r
        edge=r
        mid=(l+r)/2
        K=2*H//mid
        assert K*r<=2*H<=(K+1)*l
        raw,fold=raw_fold(data,C,S,Z,lines,l,r)
        assert r<=2*H or l>=2*H
        point=l
        for aa,bb,label in tile[2]:
            a,b=N*Q(aa),N*Q(bb)
            assert point==a and a<b<=r
            point=b
            caps=defaultdict(lambda:[Q(0),Q(0)])
            if label=='unfolded':
                period=0
                samples=((w,tuple(y-2*i if l>=2*H else y for i,y in enumerate(v)),1)
                         for w,v in (((hi[0]-lo[0],hi[1]-lo[1]),t) for lo,hi,t in raw))
            else:
                q=int(label.removeprefix('joint').removeprefix('fold'))
                assert 0<=q<=K
                period=int_aff((2*H*(K-q),-sum(range(q+1,K+1))),a,b)
                if label.startswith('joint'):
                    samples=((w,tuple(B-2*max(j-q,0) for j,B in enumerate(v)),2) for v,w in fold.items())
                else:
                    assert label.startswith('fold')
                    samples=()
                    for v,w in fold.items():
                        for j in range(1,v[0]+1):
                            for t in (0,1):
                                caps[j][t]+=Q(w[t],2)*((v[0]-j)//2+q+1)
            for width,costs,den in samples:
                for cost in costs:
                    for j in range(1,cost+1):
                        for t in (0,1):
                            caps[j][t]+=Q(width[t],den)
            total+=period+sum((cap_int(H,u,a,b) for u in caps.values()),Q(0))
        assert point==r
    assert edge==Z-S
    return total/(N*H)


def periodic(data,C,N,H,cut,table):
    shifted=[(a-C,b-C,w) for a,b,w in data]
    ends={x for a,b,t in shifted for x in (a,b)}
    lines={(-j,a) for a in ends for j in range(min(0,a)-1,max(0,a)+1)}
    edge=Q(0);Fa=Ga=Q(0);out=arb(0);stop=45
    first=1/(cut*N);K=int(2*H)
    assert K==2*H
    for row in table:
        l,r=map(Q,row[:2])
        assert l==edge and l<r
        edge=r;t=(l+r)/2
        W=order(lines,(0,0),(1,0),l,r)
        normal=sum(e*((b-a)*t//1) for a,b,e in shifted)
        assert all((k:=(b-a)*t//1)<=(b-a)*l and (b-a)*r<=k+1 for a,b,e in shifted)
        F=[0,0];G=[0,0]
        for a,b in zip(W,W[1:]):
            n,d=t.numerator,t.denominator
            w=(a[0]+b[0])*d+(a[1]+b[1])*n
            B=max(0,4-normal+sum(s*(((2*h*n-w)//(2*d))-((2*j*n-w)//(2*d))) for j,h,s in shifted))
            for i in (0,1):
                F[i]+=(b[i]-a[i])*B
                G[i]+=(b[i]-a[i])*sum(k//2 for k in range(B))
        assert F==list(map(int,row[2:4])),('periodic profile',l,r,F,row[2:4])
        j=(K*t)//1
        u=int(row[7])
        assert j<=K*l and K*r<=j+1 and 0<=u<=K*first
        a,b=F;c,d=G
        c,d,e=c+(1-u)*a+u*(u-1)-j*(2*u-a),d+(1-u)*b+K*(2*u-a)+j*b,-K*b
        assert (c,d,e)==tuple(map(int,row[4:7]))
        Fa+=int_aff(F,l,r);Ga+=int_aff(G,l,r)
        for k in range(first//1,stop):
            x,y=max(first,k+l),k+r
            if x<y:
                d1=1/x-1/y
                d2=(1/x**2-1/y**2)/2
                L=A(y/x).log()
                out+=A((a-b*k)*d1)+b*L
                out+=(A((c-d*k+e*k*k)*d2+(d-2*e*k)*d1)+e*L)/A(2*H)
    assert edge==1
    return (out+A(Fa/(stop-1)+(Fa+Ga)/(4*H*(stop-1)**2)))/N


def analytic(data,C,N,theta,phase):
    c=Q(phase['c'])
    assert 0<c<min(a for a,b,w in data if w==1)/Q(N)
    assert 11+5*theta<24
    delta=C/Q(N)-c
    W=Counter();constant=arb(0);slope=arb(-2)
    for a,b,t in data:
        z=Q(b-a,N)
        constant+=t*A(z)*A(z).log()
        for q,g in ((Q(a,N)-c,t),(Q(b,N)-c,-t)):
            if q:
                s=1 if q>0 else -1
                W[abs(q)]+=g*s
                slope+=g*s*arb(1)/2
    W=[(A(z),e) for z,e in W.items() if e]
    L=slope*arb.pi();D0=4*A(delta)**2
    @lru_cache(maxsize=8192)
    def scalar(lo,hi):
        a,b=arb(lo),arb(hi)
        x=(a+b)/2;length=(b-a)/2;I=x+arb(0,length)
        v=constant+L*x;der=L
        for z,w in W:
            v+=w*(z/2*(z*z+x*x).log()-x*(x/z).atan())
            der-=w*(I/z).atan()
        return a,b,x,length,I,v,der

    sum_caps=Q(0);edge=Q(0)
    for u in phase['bins']:
        l,r=Q(u['a']),Q(u['b'])
        assert edge==l<r;edge=r
        atoms=[(Q(a),Q(b)) for a,b in u['atoms']]
        assert sum(w for a,w in atoms)==1 and all(0<=a<=Q(7,5) and w>0 for a,w in atoms)
        for t,name in [(l,'lo_cap'),(r,'hi_cap')]:
            stack=[(i/16,(i+1)/16) for i in range(64)]
            cap=A(u[name]);sum_caps+=Q(u[name])*(r-l)/2
            roots=[(A(a),A(t*w/2)) for a,w in atoms if t]
            while stack:
                lo,hi=stack.pop()
                a,b,x,length,I,v,der=scalar(lo,hi)
                coarse=v+abs(der).upper()*length;refined=v;smooth=True
                for j,w in roots:
                    d=I*I-j*j
                    if smooth and not d.contains(0):
                        refined+=w*(2*abs(x*x-j*j).log()+((x+j)**2+D0).log()+((x-j)**2+D0).log())
                        der+=w*(4*I/d+2*(I+j)/((I+j)**2+D0)+2*(I-j)/((I-j)**2+D0))
                    else:
                        smooth=False
                    mx=max(abs(a*a-j*j).upper(),abs(b*b-j*j).upper())
                    coarse+=w*(2*mx.log()+((b+j)**2+D0).log()+
                               (max(abs(a-j).upper(),abs(b-j).upper())**2+D0).log())
                if coarse<cap or smooth and refined+abs(der).upper()*length<cap:
                    continue
                assert hi-lo>2**-28,(l,r,t,lo,hi)
                mid=(lo+hi)/2;stack.extend(((lo,mid),(mid,hi)))
    assert edge==theta
    return A(sum_caps/theta)+A(theta)*(3-2*(2*A(theta)).log())


def gate(U,L,Z,D,theta,w):
    T,J,A0,B=w['T'],w['J'],w['A'],w['B']
    S=min(Z)
    assert 0<T and J>=1 and J*T==L*theta and S+T<=U and S+2*T<=L and 2*J*T<=L
    assert A0==U+L-S-T and 2*A0>U+L-S and B>2*(J-1)
    m=Counter(d for d in D if d<T)
    zeros=Counter(max(0,S+T-z) for z in Z if z>S)
    assert m-zeros==Counter({0:B-4}) and not zeros-m
    for q in range(zeros[0],sum(zeros.values())+1):
        order=B-4+q
        M=[[comb(B-1-i-j,order-1-i-j) if i+j<order else 0 for j in range(J)] for i in range(J)]
        assert M==w['blocks'][str(q)]
        assert fmpq_mat(M).det()


def ball_check(function,args):
    ctx.prec=144
    return str(function(*args))

def main(path):
    if not __debug__:
        raise RuntimeError('Run without Python optimization to enable certificate checks.')
    ctx.prec=144
    d=json.loads(Path(path).read_text(encoding='utf-8'))
    U,L=d['U'],d['L'];Z,D=d['zeros'],d['offsets'];N=2*L;C=2*U+L
    theta,cut=Q(d['theta']),Q(d['cut']);H=N*theta
    assert len(Z)==5 and len(D)==14 and 0<min(Z)<=max(Z)<=U and 0<=min(D)<=max(D)<L/2
    assert 0<Q(d['phase']['c'])<Q(min(Z),L) and 0<theta and 2*sum(Z)<=11*L
    assert U+L-min(Z)>=max(L,max(Z),2*theta*L)
    assert sum(L-2*x for x in D)-2*sum(Z)>4*theta*L
    data=blocks(U,L,Z,D)
    gate(U,L,Z,D,theta,d['gate'])
    with ProcessPoolExecutor(max_workers=3) as pool:
        real=pool.submit(ball_check,analytic,(data,C,N,theta,d['phase']))
        medium=pool.submit(high,data,H,N,2*min(Z),C,2*(U+L),cut,d['high'])
        small=pool.submit(ball_check,periodic,(data,C,N,H,cut,d['periodic']))
        C0=arb(small.result())
        print('Periodic small-prime integral checked.',flush=True)
        C1=medium.result()
        print('Middle/high-prime walls and integral checked.',flush=True)
        R=arb(real.result())
        print('R <=',R,flush=True)
    total=R+A(C1)+C0
    print('C <=',A(C1)+C0,'net <=',total)
    assert total<A(Q(d['target']))<0
    print('PASS: analytic, arithmetic, walls, and confluent gate.')

if __name__=='__main__':
    main(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('zeta6_certificate.json'))
