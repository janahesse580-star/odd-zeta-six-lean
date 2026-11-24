"""Independent rational geometry and objective-envelope audit for S=14."""
from bisect import bisect_right
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import argparse
import csv
import sys

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0,str(HERE))
import zeta7_s14_replay as reference

NAME='confluent40-34-4-3-5-1-1'
BASE=reference.Shape(NAME,40,34,(30,30,30,32,33),tuple(map(F,[0]*5+[1,2,4,5,6,7,8,9,10])))
THETA=F(3,10)
CUT=F(9,200)


def value(line,x):
    a,b=line
    return a+b*x


def root(a,b):
    if a[1]!=b[1]:
        return F(b[0]-a[0],a[1]-b[1])
    return None


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def as_pair(k,v):
    return int(v.get((k,0),0)),int(v.get((k,1),0))


@lru_cache(None)
def cost_vector(order,top,pole_neighbors,zero_neighbors,right,left):
    assert pole_neighbors>=0 and zero_neighbors>=0 and right>=left>=0
    result=[]
    for r in range(order):
        options=[0]
        for ell in range(1,order-r+1):
            d=order-r-ell
            loss=d if pole_neighbors else min(d,zero_neighbors)
            singular=(right!=left if ell%2==0 else right>0)
            options.append(r-top+loss+(ell+4)*singular)
        result.append(max(options))
    return tuple(max(result[j:]) for j in range(order))


class Arrangement:
    def __init__(self,shape,theta,lower):
        self.sh=shape
        self.N=2*shape.length
        self.H=self.N*theta
        self.S=2*shape.start
        self.C=shape.left+shape.right
        self.Z=2*shape.right
        self.cap=len(shape.offsets)+4
        poles=[(2*shape.left+int(2*d),2*shape.right-int(2*d),1) for d in shape.offsets]
        zeros=[(0,2*z,-1) for z in shape.zeros]+[(2*(self.C-z),2*self.C,-1) for z in shape.zeros]
        self.blocks=poles+zeros
        self.limit=2*self.C//lower+3
        const={a for a,b,w in self.blocks}|{b for a,b,w in self.blocks}
        lines={(a,j) for a in const for j in range(-self.limit,self.limit+1)}
        lines.update((self.S,j) for j in range(1,self.limit+1))
        lines.update((2*self.C-self.S,-j) for j in range(1,self.limit+1))
        self.lines=lines|{(self.C,0),(self.Z,0)}

    def raw_order(self,x):
        n,d=x.numerator,x.denominator
        return sorted(self.lines,key=lambda u:(u[0]*d+u[1]*n,u))

    def assert_order(self,order,l,r,what):
        for a,b in zip(order,order[1:]):
            if value(a,l)>value(b,l) or value(a,r)>value(b,r):
                raise ValueError((what,str(l/self.N),str(r/self.N),a,b,str(root(a,b)/self.N)))

    def raw(self,x):
        n,d=x.numerator,x.denominator
        at=lambda line: line[0]*d+line[1]*n
        order=self.raw_order(x)
        active=order[order.index((self.C,0)):order.index((self.Z,0))+1]
        normal=sum(t*((b-a)*d//n) for a,b,t in self.blocks)
        profile=[]
        for a,b in zip(active,active[1:]):
            s,t=at(a),at(b)
            if s==t:
                assert a==b,(a,b,x)
                continue
            uv=s+t
            inside=pc=zc=0
            for a0,b0,sgn in self.blocks:
                total=(2*b0*d-uv)//(2*n)-(2*a0*d-uv)//(2*n)
                if sgn==1:
                    pc+=total
                    inside+=2*a0*d<uv<2*b0*d
                else:
                    zc+=total
            right=(uv-2*self.S*d)//(2*n)
            left=((4*self.C-2*self.S)*d-uv)//(2*n)
            top=normal+zc-pc+inside
            costs=cost_vector(inside,top,pc-inside,zc,right,left) if inside else ()
            if inside:
                assert costs==reference.jet_slot_costs(inside,top,pc-inside,zc,right,left)
            profile.append((a,b,costs))
        return order,normal,profile

    def images(self,raw,x):
        span=(self.Z-self.C)//x+2
        return {(sign*2*(a-self.C),sign*2*(j-k)) for low,high,_ in raw
                for a,j in (low,high) for k in range(span+1) for sign in (-1,1)}|{(0,0),(0,1)}

    def folded(self,raw,x,slab=None):
        n,d=x.numerator,x.denominator
        evaluate=lambda a:a[0]*d+a[1]*n
        lines=self.images(raw,slab[0] if slab else x)
        if slab:
            l,r=slab
            for a in lines:
                for side in ((0,0),(0,1)):
                    w=root(a,side)
                    if w is not None and l<w<r:
                        raise ValueError(('fold entry/exit',l/self.N,r/self.N,a,side,w/self.N))
        relevant=sorted((a for a in lines if 0<=evaluate(a)<=n),key=lambda a:(evaluate(a),a))
        if slab:
            self.assert_order(relevant,*slab,'folded collision')
        boundaries=[evaluate(a) for a,b,costs in raw]
        joint=Counter(); baseline=Counter(); trace=[]
        for a,b in zip(relevant,relevant[1:]):
            aa,bb=evaluate(a),evaluate(b)
            if aa==bb:
                assert a==b,(a,b,x)
                continue
            target=aa+bb
            costs=[]
            for k in range((self.Z-self.C)//x+2):
                for sign in (-1,1):
                    pos=4*self.C*d+4*k*n+sign*target
                    if 4*self.C*d<pos<4*self.Z*d:
                        j=bisect_right(boundaries,pos//4)-1
                        costs.extend(v for v in raw[j][-1] if v>0)
            costs=tuple(sorted(costs,reverse=True))
            trace.append((a,b,costs))
            if costs:
                for j in (0,1):
                    joint[(costs,j)]+=b[j]-a[j]
                    baseline[(costs[0],j)]+=b[j]-a[j]
        old_segments=[(a,b,tuple(v for v in q if v)) for a,b,q in raw if any(q)]
        old_base, old_joint=reference.folded_regions(old_segments,x,self.C)
        assert {k:v for k,v in old_base.items() if v}=={k:v for k,v in baseline.items() if v}
        assert {k:v for k,v in old_joint.items() if v}=={k:v for k,v in joint.items() if v}
        return trace,baseline,joint

    def candidates(self,raw,base,joint,x):
        H=self.H
        margin=(2*H)//x
        raw_limits=[(0,0)]*(self.cap+1)
        for a,b,c in raw:
            for r,u in enumerate(c):
                value=u-2*r if x>2*H else u
                for j in range(1,value+1):
                    raw_limits[j]=add(raw_limits[j],(b[0]-a[0],b[1]-a[1]))
        out=[('unfolded',(0,0),raw_limits[1:])]
        for q in range(margin+1):
            penalty=(2*H*(margin-q),-sum(range(q+1,margin+1)))
            folded_limits=[(0,0)]*(self.cap+1)
            for score in {k for k,_ in base}:
                for j in range(1,score+1):
                    count=(score-j)//2+q+1
                    folded_limits[j]=add(folded_limits[j],(count*base[(score,0)],count*base[(score,1)]))
            out.append((f'fold{q}',penalty,[(F(a,2),F(b,2)) for a,b in folded_limits[1:]]))
            limits=[(0,0)]*(self.cap+1)
            for profile in {k for k,_ in joint}:
                widths=as_pair(profile,joint)
                for j,B in enumerate(profile):
                    u=B-2*max(0,j-q)
                    if u<=0:
                        break
                    for m in range(1,u+1):
                        limits[m]=add(limits[m],widths)
            out.append((f'joint{q}',penalty,[(F(a,2),F(b,2)) for a,b in limits[1:]]))
        return out


def integrate(line,l,r):
    return (r-l)*value(line,(l+r)/2)


def arrangement_envelope(candidates,cap,l,r):
    inside={l,r}
    for _,_,lines in candidates:
        for line in lines:
            x=root(line,(cap,0))
            if x is not None and l<x<r:
                inside.add(x)
    fixed=sorted(inside)
    result=[]
    for a,b in zip(fixed,fixed[1:]):
        mid=(a+b)/2
        pieces={}
        for name,penalty,lines in candidates:
            line=penalty
            for u in lines:
                line=add(line,u if value(u,mid)<=cap else (cap,0))
            pieces[line]=name
        # The lower envelope of affine lines is concave. Check all
        # crossings inside this saturation subinterval exactly.
        splits={a,b}
        for u,v in combinations(pieces,2):
            x=root(u,v)
            if x is not None and a<x<b:
                splits.add(x)
        splits=sorted(splits)
        for p,q in zip(splits,splits[1:]):
            u=min(pieces,key=lambda f:(value(f,(p+q)/2),f))
            if result and result[-1][2]==u:
                result[-1]=(result[-1][0],q,u,result[-1][3])
            else:
                result.append((p,q,u,pieces[u]))
    return result


def compare(path,shape,theta,output):
    with Path(path).open(newline='',encoding='utf-8-sig') as f:
        tiles=list(csv.DictReader(f))
    lower=F(tiles[0]['p_low_u'])*2*shape.length
    ar=Arrangement(shape,theta,lower)
    report=[]; envelope=[]; old=new=F(0); endpoints=set(); geometry_count=0
    for index,r in enumerate(tiles):
        l,h=F(r['p_low_u'])*ar.N,F(r['p_high_u'])*ar.N
        endpoints.update((l,h))
        sig=None
        for j,x in enumerate((l+(h-l)/5,(l+h)/2,h-(h-l)/5)):
            order,normal,raw=ar.raw(x)
            trace,base,joint=ar.folded(raw,x,(l,h) if j==1 else None)
            current=(normal,raw,trace,base,joint,(2*ar.H)//x)
            if sig is not None and current!=sig:
                raise ValueError(('three-point topology differs',index,l/ar.N,h/ar.N,j))
            sig=current
            if j==1:
                ar.assert_order(order,l,h,'raw incidence')
                for a,b,t in ar.blocks:
                    assert (b-a)//((l+h)/2)>=0
                    numerator=b-a
                    k=numerator//((l+h)/2)
                    if k and l<F(numerator,k)<h or l<F(numerator,k+1)<h:
                        raise ValueError(('factorial wall',index,l,h,numerator,k))
                k=(2*ar.H)//((l+h)/2)
                if k and l<2*ar.H/k<h or l<2*ar.H/(k+1)<h:
                    raise ValueError(('q admissibility wall',index,l,h,k))
        _,raw,trace,base,joint,_=sig
        candidates=ar.candidates(raw,base,joint,(l+h)/2)
        prior=min(integrate(p,l,h)+sum((reference.linear_cap(ar.H,*a,l,h) for a in lines),F(0))
                  for _,p,lines in candidates)/(ar.N*ar.H)
        assert prior==F(r['joint_selected']),(index,prior,r['joint_selected'])
        selected=arrangement_envelope(candidates,ar.H,l,h)
        improved=sum((integrate(line,a,b) for a,b,line,_ in selected),F(0))/(ar.N*ar.H)
        assert improved<=prior
        old+=prior;new+=improved
        geometry_count+=1
        report.append((index,str(l/ar.N),str(h/ar.N),len(raw),len(trace),len(joint),len(selected),str(prior),str(improved)))
        envelope.extend((index,str(a/ar.N),str(b/ar.N),str(line[0]),str(line[1]),name) for a,b,line,name in selected)
        if index%100==0:
            print('audit tile',index,'passing',flush=True)
    output.mkdir(exist_ok=True,parents=True)
    for filename,header,rows in [('wall-audit.csv',('tile','x_lo','x_hi','raw_segments','folded_segments','fold_profiles','objective_pieces','old_integral','envelope_integral'),report),('objective-envelope.csv',('tile','x_lo','x_hi','a_scaled','b_scaled','winning_branch'),envelope)]:
        reference.csv_write(output/filename,header,rows)
    print('AUDIT',geometry_count,len(endpoints),len(envelope),'old',float(old),'new',float(new),'gain',float(old-new),flush=True)
    return ar,report,envelope,old,new

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--tiles',type=Path,help='Original high-prime CSV; regenerate if omitted.')
    parser.add_argument('--out',type=Path,default=Path('wall-replay'))
    parser.add_argument('--winner',action='store_true',help='Audit the L=50 profile.')
    args=parser.parse_args()
    shape=BASE
    if args.winner:
        shape=reference.Shape('local50-45-209',50,45,(40,40,40,41,43),
                              tuple(map(F,[0,0,0,0,0,2,4,5,5,6,8,9,9,11])))
    args.out.mkdir(exist_ok=True,parents=True)
    source=args.tiles
    if source is None:
        source=args.out/'source.csv'
        *_,tiles=reference.arithmetic_certificate(shape,THETA,xmin=CUT)
        header=('profile','theta_u','p_low_u','p_high_u','unfolded','q_zero',
                'strict_selected','split_selected','joint_selected')
        reference.csv_write(source,header,tiles)
    compare(source,shape,THETA,args.out)
