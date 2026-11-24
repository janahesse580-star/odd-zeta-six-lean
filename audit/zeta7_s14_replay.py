"""Reproducible S=14 large-dimension determinant experiment."""
import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import chain
from math import comb, factorial, gcd, lcm, prod
from pathlib import Path
import csv
import sys

from flint import arb, arb_mat, ctx, fmpq, fmpq_mat, fmpz, fmpz_mat, fmpz_mpoly_ctx, nmod_mat



@dataclass(frozen=True)
class Shape:
    name: str
    length: int
    left: int
    zeros: tuple
    offsets: tuple

    @property
    def right(self):
        return self.left+self.length

    @property
    def center(self):
        return Q(self.left+self.right,2)

    @property
    def start(self):
        return min(self.zeros)

    @property
    def gap(self):
        return len(self.offsets)*self.length-2*(sum(self.offsets)+sum(self.zeros))

    @property
    def orders(self):
        return tuple(range(7,len(self.offsets)+5,2))

    def theta_ok(self,theta):
        return self.gap>4*theta*self.length


CORE=Shape('core25',25,21,(17,18,19,20,21),tuple(Q(b,2) for b in range(14)))
ORIGINAL=Shape('liu7',52,53,(48,49,50,51,52),tuple(map(Q,range(16))))
DROP6=Shape('drop6',52,53,(48,49,50,51,52),tuple(map(Q,range(14))))


def floor(q):
    return q.numerator//q.denominator


def qstr(x):
    return fmpq(x.numerator,x.denominator)


@lru_cache(None)
def factorial_z(n):
    return fmpz(factorial(n))


def inventories(sh,n):
    left,right,s=sh.left*n,sh.right*n,sh.start*n
    doubled_center=left+right+2
    zero_lengths=[z*n for z in sh.zeros]
    left_zeros=Counter(chain.from_iterable(range(1,z+1) for z in zero_lengths))
    zeros=left_zeros+Counter({doubled_center-k:m for k,m in left_zeros.items()})
    # Use x=2t+left+right+2 as the odd factor with either parity of the center.
    # The local jet routine uses a monic (t+center); include the factor 2 below.
    shifts=[floor(d*n) for d in sh.offsets]
    poles=Counter(chain.from_iterable(range(left+d+1,right-d+2) for d in shifts))
    scale=fmpq(2*prod(factorial_z(right-left-2*d) for d in shifts),prod(factorial_z(z)**2 for z in zero_lengths))
    if doubled_center%2==0:
        zeros[doubled_center//2]=1
    assert all(k not in poles for k in left_zeros)
    return doubled_center,s,zeros,poles,scale


def integer_basis(h,half_center):
    if not half_center:
        return even_basis(h)
    # On the half lattice use binom(x+i-1/2,2i). Its leading coefficient
    # and denominator retain the same asymptotic scaling as Liu's basis.
    table=[[fmpq(1) if i==j==0 else fmpq(0) for j in range(h)] for i in range(h)]
    p=[fmpq(1)]
    for i in range(1,h):
        square=fmpq((2*i-1)**2,4)
        p=[a-square*b for a,b in zip([fmpq(0),*p],[*p,fmpq(0)])]
        table[i][:i+1]=[a/factorial_z(2*i) for a in p]
    return fmpq_mat(table)


def exact_shape(sh,n,h,blocks_only=False):
    two_c,s,zeros,poles,kappa=inventories(sh,n)
    assert 1+2*sum(sh.zeros)*n+4*(h-1)<=sum(poles.values())-2,(sh,n,h)
    max_diff=two_c
    D=fmpz(lcm(*range(1,max_diff+1)))
    scales={k:D//k for k in range(-max_diff,max_diff+1) if k}
    max_order=len(sh.offsets)
    multipliers=[fmpq(1,D**r) for r in range(max_order)]
    keys=(0,*sh.orders)
    moments={q:[fmpq(0) for _ in range(2*h-1)] for q in (5,*keys)}
    blocks={}
    top=sh.right*n-s
    H={q:harmonic(q,top) for q in range(5,max_order+5)}
    for k in sorted(poles):
        if 2*k<two_c:
            continue
        local=local_jet(k,zeros,poles,kappa,scales)
        m=len(local)
        x=fmpq(two_c-2*k,2)
        jet=[v*multipliers[j] for j,v in enumerate(local)]
        if two_c%2:
            jet=[x*a+(jet[j-1] if j else 0) for j,a in enumerate(jet)]
        other=two_c-k
        C={e: -H[e+4][k-s-1]+((-1)**e*H[e+4][other-s-1] if other!=k else 0)
           for e in range(1,m+1)}
        W={q:[fmpq(0) for _ in range(m)] for q in (5,*keys)}
        for e in range(1,m+1):
            for r in range(m-e+1):
                a=jet[m-e-r]*comb(e+3,4)
                if not a:
                    continue
                W[0][r] += a*C[e]
                if e%2:
                    W[e+4][r]+=a*(1 if other==k else 2)
        # Every site uses powers of the same integer or half-integer x.
        blocks[k]=(x,tuple(jet),W)
        if blocks_only:
            continue
        powers=[x**i for i in range(4*h-3)]
        for q, coefficients in W.items():
            for r,a in enumerate(coefficients):
                if not a:
                    continue
                for j in range((r+1)//2,2*h-1):
                    if x or 2*j==r:
                        moments[q][j]+=a*comb(2*j,r)*powers[2*j-r]
    if blocks_only:
        return blocks
    assert not any(moments.pop(5)),(sh,n,h)
    basis=integer_basis(h,two_c%2)
    transpose=basis.transpose()
    matrices={q:basis*fmpq_mat([[m[i+j] for j in range(h)] for i in range(h)])*transpose for q,m in moments.items()}
    return matrices,blocks


def leading(matrices,h):
    return {q:fmpq_mat([[A[i,j] for j in range(h)] for i in range(h)]) for q,A in matrices.items()}


def p_content_bounds(matrices,top):
    h=matrices[0].nrows()
    coefficients=list(matrices.values())
    row_denominators=[lcm(*(A[i,j].denominator for A in coefficients for j in range(h))) for i in range(h)]
    N=[[int((A[i,j]*row_denominators[i]).numerator) for A in coefficients for j in range(h)] for i in range(h)]
    width=len(N[0])
    assignments=[[1]+[0]*(len(coefficients)-1),[1]*len(coefficients),list(range(1,len(coefficients)+1)),
                 [1]+[(-1)**i*(1+i*i) for i in range(1,len(coefficients))]]
    numerator_matrices=[fmpz_mat([[row[q*h+j] for j in range(h)] for row in N]) for q in range(len(coefficients))]
    sample=[sum((w*M for w,M in zip(row,numerator_matrices)),fmpz_mat(h,h)).det() for row in assignments]
    spec=fmpq(gcd(*sample),prod(row_denominators))
    assert spec
    vrows=[]
    for p in all_primes(max(top,2*h)):
        max_cost=sum(valuation(fmpq(d),p) for d in row_denominators)
        if not max_cost:
            continue
        v_spec=valuation(spec,p)
        # The modulus tracks precision through p divisions. Retain positive
        # content savings when all specializations permit them.
        max_saving=max_cost+max(0,v_spec)
        precision=min(12,max_saving+1)
        while True:
            saving,rank=joint_pivots(N,p,precision,max_saving)
            if saving>=max_saving or rank==h:
                break
            precision=min(max_saving+1,precision*2)
        lo=min(saving,max_saving)-max_cost
        assert lo<=v_spec
        vrows.append((p,-max_cost,lo,v_spec))
    return vrows,spec


def joint_pivots(N,p,precision,target):
    modulus=p**precision
    data=[[x%modulus for x in row] for row in N]
    h,width=len(data),len(data[0])
    rank=saving=0
    while rank<h and saving<target and modulus>1:
        pivot=next(((i,j) for i in range(rank,h) for j in range(rank,width) if data[i][j]%p),None)
        if pivot is None:
            saving+=h-rank
            modulus//=p
            for row in data[rank:]:
                row[rank:]=[x//p for x in row[rank:]]
            continue
        i,j=pivot
        data[rank],data[i]=data[i],data[rank]
        for row in data[rank:]:
            row[rank],row[j]=row[j],row[rank]
        inverse=pow(data[rank][rank],-1,modulus)
        normalized=[x*inverse%modulus for x in data[rank][rank:]]
        for row in data[rank+1:]:
            v=row[rank]
            if v:
                row[rank:]=[(a-v*b)%modulus for a,b in zip(row[rank:],normalized)]
        rank+=1
    return saving,rank


@lru_cache(None)
def all_primes(top):
    return tuple(p for p in range(2,top+1) if fmpz(p).is_prime())


def gate_matrix(sh,n,matrix,p):
    h=matrix[0].nrows()
    if not fmpz(p).is_prime():
        return ('composite','','','','')
    minimum=min(valuation(A[i,j],p) for A in matrix.values() for i in range(h) for j in range(h))
    weight=max(0,-minimum)
    factor=p**weight
    leading_blocks=[nmod_mat([[reduction(factor*A[i,j],p) for j in range(h)] for i in range(h)],p) for A in matrix.values()]
    return ('prime',weight,leading_blocks[0].rank(),str(leading_blocks[0].det()),max(M.rank() for M in leading_blocks[1:]))


def finite_case(sh,n,dimensions,out):
    out.mkdir(exist_ok=True,parents=True)
    matrices,blocks=exact_shape(sh,n,max(dimensions))
    print('matrix built',sh.name,n,max(dimensions),flush=True)
    summaries=[]; primes=[]
    for h in dimensions:
        A=leading(matrices,h)
        real,bits=arb_det(A,1)
        norm=sh.length*n*h
        real/=norm
        vals,sample=p_content_bounds(A,(sh.left+sh.right)*n+2)
        low=-abs(arb(sample)).log()/norm
        high=-sum((v*arb(p).log() for p,_,v,_ in vals),arb(0))/norm
        exact=''
        if h<=4:
            c,_=rational_content(A)
            er=-arb(c).log()/norm
            assert er.overlaps(low) or er>low
            assert er.overlaps(high) or er<high
            real_low,real_high=real+er,real+er
            exact=str(c)
        else:
            real_low,real_high=real+low,real+high
        groups=[sum(((v-e)*arb(p).log() for p,e,v,_ in vals if f(p)),arb(0))/norm
                for f in (lambda p:p<=2*h,lambda p:2*h<p<=sh.length*n/2,lambda p:p>max(2*h,sh.length*n/2))]
        pg=(sh.right-sh.start)*n+1-h
        gate=gate_matrix(sh,n,A,pg)
        confirmed='negative' if real_high<0 else 'positive' if real_low>0 else 'unresolved'
        summ=(sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(str(d) for d in sh.offsets),n,h,str(Q(h,n*sh.length)),
              str(real),str(low),str(high),str(real_low),str(real_high),confirmed,str(exact),*map(str,groups),bits,pg,*gate)
        summaries.append(summ)
        primes.extend((sh.name,n,h,p,entry,vl,vu) for p,entry,vl,vu in vals)
        print(sh.name,n,h, 'P',float(real_low),float(real_high),confirmed,'gate',pg,gate,flush=True)
    csv_write(out/f'{sh.name}-{n}-summary.csv',('profile','L0','U0','zeros','offsets','n','h','theta_u','R_per_nhL0','C_full_lower','C_upper','primitive_lower','primitive_upper','sign','symbolic_content_if_h_le_4','gain_p_le_2h','gain_2h_lt_p_le_half_L','gain_large','arb_bits','proposed_gate_p','p_status','p_entry_exponent','p_constant_rank','p_constant_det','p_nonconstant_max_rank'),summaries)
    csv_write(out/f'{sh.name}-{n}-primes.csv',('profile','n','h','p','entry_v_lower','joint_lattice_v_lower','specialization_v_upper'),primes)
    return summaries


def run_core(out):
    for n in (1,2,3,4):
        cols=sorted({floor(Q(a,25)*CORE.length*n) for a in (3,4,5,6) if 4<=a*n<=20})
        finite_case(CORE,n,cols,out)


def run_controls(out):
    for sh,n,hs in ((ORIGINAL,1,(4,6)),(ORIGINAL,2,(8,12)),(DROP6,6,(9,12,15))):
        finite_case(sh,n,hs,out)



# Normalized screening. The grid scores guide experiments, while the final
# arithmetic and phase certificates use rational pieces and Arb intervals.
def phase_inventory(sh,c):
    W=Counter(); N=Counter(); pi_term=Q(-2)
    segments=[(Q(0),Q(a),1) for a in sh.zeros]
    segments += [(Q(sh.left+sh.right-a),Q(sh.left+sh.right),1) for a in sh.zeros]
    segments += [(sh.left+d,sh.right-d,-1) for d in sh.offsets]
    for a,b,m in segments:
        N[(b-a)/sh.length]-=m
        for u,sgn in ((a,-m),(b,m)):
            d=u/sh.length-c
            if d:
                polarity=1 if d>0 else -1
                W[abs(d)]+=sgn*polarity
                pi_term+=Q(sgn*polarity,2)
    return W,N,pi_term


def phase_values(inventory,ys):
    import numpy as np
    from math import log,pi
    W,N,pi_term=inventory
    return (sum(m*float(l)*log(float(l)) for l,m in N.items())+float(pi_term)*pi*ys+
            sum(m*(float(d)/2*np.log(float(d)**2+ys*ys)-ys*np.arctan(ys/float(d))) for d,m in W.items() if m))


def pair_values(ys,roots,delta):
    import numpy as np
    return sum(2*np.log(np.maximum(abs(ys*ys-a*a),1e-40))+
               np.log((ys+a)**2+4*delta*delta)+np.log((ys-a)**2+4*delta*delta) for a in roots)


def phase_grid(sh,theta_list):
    import numpy as np
    from math import log
    ys=np.linspace(0,2.50,501)
    thetas=np.array([float(t) for t in theta_list])
    best=[(float('inf'),None) for t in theta_list]
    kgrid=(Q(1,25),Q(2,25),Q(3,25),Q(4,25),Q(1,5),Q(6,25))
    for c in kgrid:
        delta=float(sh.center/sh.length-c)
        F=phase_values(phase_inventory(sh,c),ys)
        peak=ys[np.argmax(F)]
        comps=((.03,.09,.17,.29),(.11,.23,.34,.43),(.26,.36,.46,.56),(.38,.48,.58,.68),
               (.48,.60,.75,.92),tuple(max(.02,peak+gap) for gap in (-.09,-.02,.045,.12)),
               tuple(max(.02,peak+gap) for gap in (-.035,.015,.075,.155)))
        P=np.asarray([pair_values(ys,roots,delta)/8 for roots in comps])
        t=thetas[:,None]*(np.arange(9)/8)[None,:]
        M=np.max(F[None,None,None,:]+t[:,:,None,None]*P[None,None,:,:],axis=3)
        M=np.min((M[:,1:,:]+M[:,:-1,:])/2,axis=2).mean(axis=1)
        scores=M+thetas*(3-2*np.log(2*thetas))
        for i,v in enumerate(scores):
            if v<best[i][0]:
                best[i]=float(v),c
    return best


def pole_grid(sh,theta_list,nprime=149,nspace=156,cut=.055):
    import numpy as np
    bound=len(sh.offsets)+4
    s=sh.start/sh.length
    r=sh.right/sh.length
    center=float(sh.center/sh.length)
    tail=r-s
    x=cut+(np.arange(nprime)+.5)*(tail-cut)/nprime
    norm=np.zeros((nprime,1,1),dtype=int)
    X=x[:,None,None]
    folds=(np.arange(nspace)+.5)/nspace
    nodes=(np.arange(nspace)+.5)/(2*nspace)
    representatives=x[:,None]/2*folds[None,:]
    indices=np.arange(0,int(.5/cut)+2)
    q_grid=np.concatenate((indices[None,None,:]*X+representatives[:,:,None],indices[None,None,:]*X-representatives[:,:,None]),axis=2)
    valid=(q_grid>0)&(q_grid<.5)
    q1=np.broadcast_to(nodes[None,:,None],(nprime,nspace,1))
    D=np.concatenate((q1,q_grid),axis=2)+center
    score=np.zeros(D.shape,dtype=int)
    order=np.zeros(D.shape,dtype=int)
    edges=[(float((sh.left+d)/sh.length),float((sh.right-d)/sh.length),1) for d in sh.offsets]
    edges += [(0.0,a/sh.length,-1) for a in sh.zeros]
    edges += [((sh.left+sh.right-a)/sh.length,(sh.left+sh.right)/sh.length,-1) for a in sh.zeros]
    for a,b,t in edges:
        norm+=t*np.floor((b-a)/X+1e-10).astype(int)
        lo=np.floor((a-D)/X).astype(int)
        hi=np.floor((b-D)/X).astype(int)
        score+=t*(hi-lo)
        if t==1:
            order+=(a<D)&(D<b)
    B=score-norm+np.where(D-s>=X,4,-1)
    coeff=B[:,:,0]
    count=order[:,:,0]
    folded=np.max(np.where(valid,B[:,:,1:],-100),axis=2)
    all_levels=np.arange(1,bound+1)
    theta_results=[]
    for t in theta_list:
        theta=float(t)
        unfolded=np.zeros(nprime)
        for j in all_levels:
            cap=np.minimum(count,np.where(x[:,None]>2*theta, np.maximum(0,(coeff-j)//2+1), np.where(coeff>=j,bound,0)))
            unfolded+=np.minimum(theta,.5*cap.mean(axis=1))
        strict=unfolded.copy(); split=unfolded.copy()
        for q in range(0,1+int(2*theta/cut)):
            cost=np.zeros(nprime)
            for j in all_levels:
                cap=np.where(folded>=j,q+1+np.maximum(0,(folded-j)//2),0)
                cost+=np.minimum(theta,x/2*cap.mean(axis=1))
            cost+=sum(2*np.maximum(0,theta-j*x/2) for j in range(q+1,2+int(2*theta/cut)))
            if not q:
                strict=np.minimum(strict,cost)
            split=np.minimum(split,cost)
        theta_results.append(tuple(bound*cut+(tail-cut)*cost.mean()/theta for cost in (strict,split)))
    return theta_results


def gate_recipes():
    for L,T,U,S,Z in ((20,4,17,11,(12,13,14,16)),(20,4,18,11,(12,13,15,17)),
                        (25,5,22,14,(16,17,18,20)),(25,5,22,14,(15,17,19,21)),
                        (25,6,22,12,(14,15,16,20)),(25,6,24,12,(14,16,18,23)),
                        (30,6,26,17,(19,20,21,25)),(30,7,27,15,(17,19,20,26)),
                        (40,9,35,22,(24,26,27,33)),(40,10,36,20,(22,24,26,34))):
        attached=[S+T-z for z in Z if S<z<S+T]
        q0=sum(z>=S+T for z in Z)
        for m0 in (3,5,7,9):
            if m0<q0+1 or m0+len(attached)>14:
                continue
            remaining=14-m0-len(attached)
            for drift in (0,1):
                d=tuple(sorted(map(Q,[0]*m0+attached+[T+drift*i for i in range(remaining)])))
                sh=Shape(f'gate{L}-{T}-{U}-{m0}-{drift}-{Z[0]}',L,U,(S,*Z),d)
                theta=Q(T,L)
                if max(d)<Q(45,100)*L and sh.theta_ok(theta):
                    yield sh,theta


def seed_shapes():
    import numpy as np
    rng=np.random.default_rng(514221)
    check=[Q(x,100) for x in (10,12,14,16,18,20,22,24,26,28,30)]
    yield ORIGINAL,[Q(2,52),Q(4,52),Q(6,52)]
    yield DROP6,[Q(2,52),Q(5,104),Q(12,100),Q(16,100),Q(20,100),Q(24,100),Q(28,100)]
    yield CORE,check
    for sh,theta in gate_recipes():
        yield sh,[theta]
    for i in range(170):
        L=int(rng.choice([20,25,25,30,30,40,50]))
        U=max(round(.55*L),min(round(1.05*L),round(float(rng.normal(.85,.105))*L)))
        max_zero=max(round(.5*L),U-int(rng.choice([0,0,0,1,1,2])))
        spread=int(rng.choice([1,1,2,2,3,4,5,6]))
        if i%3:
            extra=sorted(rng.integers(0,spread+1,4),reverse=True)
        else:
            extra=[int(round(1.5*spread)),spread,round(spread*.65),round(spread*.35)]
        zeros=tuple(int(max(round(.5*L),max_zero-d)) for d in extra)+(max_zero,)
        step=float(rng.choice([.011,.014,.017,.02,.023,.026,.029,.032]))
        curvature=float(rng.choice([.58,.75,1,1,1.20,1.45]))
        head=int(rng.choice([0,0,0,2,3,4]))
        offsets=tuple(Q(round(2*L*step*13*((max(0,j-head)/(13-head))**curvature)),2) for j in range(14))
        sh=Shape(f'grid{i:03d}',L,U,zeros,offsets)
        if max(offsets)>=Q(45,100)*L:
            continue
        ts=[t for t in check if sh.theta_ok(t)]
        if ts:
            yield sh,ts


def screening(out):
    import numpy as np
    out.mkdir(exist_ok=True,parents=True)
    all_rows=[]
    seen=set()
    for index,(sh,ts) in enumerate(seed_shapes()):
        key=(sh.length,sh.left,sh.zeros,sh.offsets,tuple(ts))
        if key in seen:
            continue
        seen.add(key)
        phase=phase_grid(sh,ts)
        costs=pole_grid(sh,ts)
        for t,(R,c),(Cs,Cb) in zip(ts,phase,costs):
            all_rows.append((sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(map(str,sh.offsets)),str(t),str(c),float(sh.gap/sh.length),R,Cs,Cb,Cs+R,Cb+R))
        if index%15==0:
            print('screen',index,sh.name,flush=True)
            write_screen(out,all_rows)
    write_screen(out,all_rows)


def write_screen(out,rows):
    csv_write(out/'s14-screen.csv',('profile','L0','U0','zeros','offsets','theta_u','contour_c_u','degree_gap_u','real_grid','C_strict_grid','C_split_grid','net_strict_grid','net_split_grid'),sorted(rows,key=lambda q:q[-1]))


def parse_shape(r):
    import ast
    return Shape(r['profile'],int(r['L0']),int(r['U0']),tuple(ast.literal_eval(__import__('re').sub(r'np\.int64\(([-\d]+)\)',r'\1',r['zeros']))),tuple(Q(x) for x in r['offsets'].split(';')))


def table(path):
    with Path(path).open(newline='',encoding='utf-8-sig') as f:
        return list(csv.DictReader(f))


def shortlist(screen, category, limit):
    all_rows=table(screen)
    out=[]; visited=set()
    for r in all_rows:
        name=r['profile']
        if name in visited or category=='gate' and not name.startswith('gate'):
            continue
        if category=='grid' and not name.startswith('grid'):
            continue
        if int(r['L0'])>40:
            continue
        out.append(r);visited.add(name)
        if len(out)>=limit:
            break
    return out




def gate_parameters(sh,theta):
    T=theta*sh.length
    if T.denominator!=1 or any(d.denominator!=1 for d in sh.offsets):
        return None
    T=int(T)
    S=sh.start
    if sh.left<S+T or S+2*T>sh.length or 2*T>=sh.length:
        return None
    left_counts=Counter(max(0,S+T-z) for z in sh.zeros if z>S)
    dose=Counter(int(d) for d in sh.offsets if d<T)
    if any(dose[d]!=left_counts[d] for d in (set(left_counts)|set(dose))-{0}):
        return None
    excess=dose[0]-left_counts[0]
    if excess<1:
        return None
    return T,sh.right-S-T,excess+4


def gate_witness(sh,n,theta):
    info=gate_parameters(sh,theta)
    assert info,(sh,theta)
    T,A,B=info
    h=T*n;p=A*n+1
    if not fmpz(p).is_prime():
        return None
    matrices,blocks=exact_shape(sh,n,h)
    rows,constant=gate_from_matrix(sh,n,theta,matrices,blocks)
    del matrices
    return rows,constant


def gate_from_matrix(sh,n,theta,matrices,blocks):
    T,A,B=gate_parameters(sh,theta)
    h=T*n;p=A*n+1
    assert p>max(sh.length*n,16,2*h)
    X=integer_basis(h,((sh.right+sh.left)*n)%2)
    weights=[]; nodes=[]
    for k in range(sh.right*n+2-h,sh.right*n+2):
        x,jet,_=blocks[k]
        m=len(jet)
        q=sum((k-p)<=n*z for z in sh.zeros)
        assert m+4-q==B and 0<=q<=4
        U=jet[0]/fmpz(-p)**q
        unit=reduction(U,p)
        assert unit and valuation(jet[0],p)==q
        w=(-1)**(q+1)*comb(m+3-q,m-1)*unit%p
        assert w
        weights.append(w);nodes.append(reduction(x,p))
    V=nmod_mat([[sum(reduction(X[i,j],p)*pow(x,2*j,p) for j in range(i+1))%p for x in nodes] for i in range(h)],p)
    VW=nmod_mat([[int(V[i,j])*weights[j]%p for j in range(h)] for i in range(h)],p)
    gram=VW*V.transpose()
    evaluated=nmod_mat([[reduction(p**B*matrices[0][i,j],p) for j in range(h)] for i in range(h)],p)
    assert evaluated==gram and evaluated.rank()==h
    assert all(not reduction(p**B*M[i,j],p) for j in range(h) for i in range(h) for w,M in matrices.items() if w)
    return [(k,x,w) for k,x,w in zip(range(sh.right*n+2-h,sh.right*n+2),nodes,weights)],int(evaluated.det())


def proposed_gates(screen_path,out):
    out.mkdir(exist_ok=True,parents=True)
    chosen=[]
    for r in shortlist(screen_path,'gate',8):
        sh=parse_shape(r);t=Q(r['theta_u']);g=gate_parameters(sh,t)
        assert g
        chosen.append((sh,t,g))
    rows=[]; nodes=[]
    for sh,theta,(T,A,B) in chosen:
        primes=[n for n in range(1,16) if fmpz(A*n+1).is_prime() and 16<A*n+1 and T*n<=27]
        for n in primes[:2]:
            result,constant=gate_witness(sh,n,theta)
            rows.append((sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(map(str,sh.offsets)),str(theta),n,T*n,A*n+1,B,constant))
            nodes.extend((sh.name,n,T*n,A*n+1,k,x,w) for k,x,w in result)
            print('gate certified',sh.name,n,T*n,A*n+1,B,constant,flush=True)
    csv_write(out/'large-gates.csv',('profile','L0','U0','zeros','offsets','theta','n','h','p','entry_p_exponent','det_mod_p'),rows)
    csv_write(out/'gate-weights.csv',('profile','n','h','p','pole_k','node_mod_p','weight_mod_p'),nodes)


def certify_phase_sup(inventory,delta,roots,t,tol=Q(1,1000),weights=None):
    import numpy as np
    from math import ceil
    W,N,pi_term=inventory
    dlist=[(arb(qstr(d)),m) for d,m in W.items() if m]
    const=sum(m*arb(qstr(l))*arb(qstr(l)).log() for l,m in N.items())
    linear=arb(qstr(pi_term))*arb.pi()
    exact_delta=delta
    if weights is None:
        weights=(Q(1,len(roots)),)*len(roots)
    assert len(weights)==len(roots) and sum(weights)==1
    delta=arb(qstr(delta)); amp=arb(qstr(t/2))
    root_arb=[(arb(qstr(q)),arb(qstr(w))) for q,w in zip(roots,weights)]
    end=4
    assert all(q<=Q(7,5) for q in roots)
    assert 11+5*t<6*end
    grid=np.linspace(0,end,12001)
    estimate=phase_values(inventory,grid)
    if t:
        estimate+=float(t)/2*sum(float(w)*pair_values(grid,(float(a),),float(delta)) for a,w in zip(roots,weights))
    guessed=float(estimate.max())
    cap=arb(qstr(Q(ceil((guessed+float(tol))*10**6),10**6)))
    stack=[(i/16,(i+1)/16) for i in range(16*end)]
    passes=0
    while stack:
        lo,hi=stack.pop()
        a,b=arb(lo),arb(hi)
        mid=(a+b)/2
        width=(b-a)/2
        interval=mid+arb(0,width)
        value=const+linear*mid
        derivative=linear
        for d,w in dlist:
            value+=w*(d/2*(d*d+mid*mid).log()-mid*(mid/d).atan())
            derivative-=w*(interval/d).atan()
        ceiling=value+abs(derivative).upper()*width
        if t:
            logs=arb(0)
            for root,w in root_arb:
                gap=max(abs(a*a-root*root).upper(),abs(b*b-root*root).upper())
                plus=(b+root)**2+4*delta**2
                minus=max(abs(a-root).upper(),abs(b-root).upper())**2+4*delta**2
                logs+=w*(2*gap.log()+plus.log()+minus.log())
            ceiling+=amp*logs
        passes+=1
        if ceiling<cap:
            continue
        if hi-lo<2**-27:
            assert tol<Q(1,30)
            return certify_phase_sup(inventory,exact_delta,roots,t,2*tol,weights)
        middle=(lo+hi)/2
        stack.extend(((lo,middle),(middle,hi)))
    return cap,passes


def adapt_roots(inventory,delta,theta):
    import numpy as np
    from scipy.optimize import minimize
    xs=np.linspace(0,2.3,2301)
    F=phase_values(inventory,xs)
    peak=xs[np.argmax(F)]
    choices=(tuple(max(.015,peak+a) for a in (-.08,-.02,.05,.15)),(.04,.15,.25,.38),(.16,.28,.39,.56),(.32,.45,.60,.74))
    def val(roots):
        return max(F+float(theta)/8*pair_values(xs,roots,float(delta)))
    init=min(choices,key=val)
    fit=minimize(val,init,method='Nelder-Mead',bounds=[(.005,1.25)]*4,
                 options={'maxiter':440,'xatol':.00025,'fatol':.00004})
    return tuple(Q(round(a*10000),10000) for a in sorted(fit.x))


def phase_certificate(sh,theta,contour):
    ctx.prec=104
    data=phase_inventory(sh,contour)
    delta=sh.center/sh.length-contour
    parts=[]
    integral=arb(0)
    for i in range(8):
        x=theta*i/8;y=theta*(i+1)/8
        roots=adapt_roots(data,delta,(x+y)/2)
        a,na=certify_phase_sup(data,delta,roots,x)
        b,nb=certify_phase_sup(data,delta,roots,y)
        integral+=arb(qstr(y-x))*(a+b)/2
        parts.append((sh.name,str(theta),str(contour),str(x),str(y),';'.join(map(str,roots)),str(a),str(b),na+nb))
    t=arb(qstr(theta))
    return integral/t+t*(3-2*(2*t).log()),parts


def rank_cases(screen_path,out):
    selected=shortlist(screen_path,'grid',5)+shortlist(screen_path,'gate',3)
    for r in selected:
        sh=parse_shape(r)
        q=Q(r['theta_u'])
        for n in (1,2,3,4):
            if gate_parameters(sh,q):
                sizes=[floor(q*sh.length*n)]
            else:
                sizes=sorted({floor(q*sh.length*n),floor(max(Q(14,100),q-Q(4,100))*sh.length*n)})
            sizes=[h for h in sizes if 4<=h<=38]
            if sizes:
                finite_case(sh,n,sizes,out)




def linear_cap(cap,a,b,l,r):
    u,v=a+b*l,a+b*r
    if u<=cap and v<=cap:
        return (u+v)*(r-l)/2
    if u>=cap and v>=cap:
        return cap*(r-l)
    cross=(cap-a)/b
    if u<cap:
        return (u+cap)*(cross-l)/2+cap*(r-cross)
    return cap*(cross-l)+(v+cap)*(r-cross)/2


def folded_regions(segments,mid,center):
    from collections import defaultdict
    numerator,denominator=mid.numerator,mid.denominator
    change=defaultdict(Counter)
    def evaluate(p):
        return p[0]*denominator+p[1]*numerator
    for a,b,profile in segments:
        left=2*(a[0]-center),2*a[1]
        right=2*(b[0]-center),2*b[1]
        i0=evaluate(left)//(2*numerator)
        i1=evaluate(right)//(2*numerator)
        for j in range(i0-1,i1+2):
            zlow=(left[0],left[1]-2*j)
            zhigh=(right[0],right[1]-2*j)
            for lo,hi in ((zlow,zhigh),((-zhigh[0],-zhigh[1]),(-zlow[0],-zlow[1]))):
                lo=max(lo,(0,0),key=evaluate)
                hi=min(hi,(0,1),key=evaluate)
                if evaluate(lo)<evaluate(hi):
                    change[lo][profile]+=1
                    change[hi][profile]-=1
    length=Counter()
    joint=Counter()
    ordered=sorted(change,key=evaluate)
    tracker=Counter()
    for a,b in zip(ordered,ordered[1:]):
        tracker.update(change[a])
        profile=tuple(sorted((B for profile,count in tracker.items() if count>0 for B in profile*count),reverse=True))
        if profile:
            high=profile[0]
            length[(high,0)]+=b[0]-a[0]
            length[(high,1)]+=b[1]-a[1]
            joint[(profile,0)]+=b[0]-a[0]
            joint[(profile,1)]+=b[1]-a[1]
    return length,joint


@lru_cache(None)
def jet_slot_costs(m,top,den_alias,num_alias,right_count,left_count):
    proposed=[]
    for r in range(m):
        high=0
        for ell in range(1,m-r+1):
            derivative=m-ell-r
            less=derivative if den_alias else min(derivative,num_alias)
            singular=(right_count+left_count>0) if ell%2 else (right_count!=left_count)
            high=max(high,r-top+less+(ell+4 if singular else 0))
        proposed.append(high)
    return tuple(max(proposed[i:]) for i in range(m))


def arithmetic_certificate(sh,theta,xmin=Q(2,25),refined=True,xmax=None):
    import numpy as np
    # Coordinates scaled by 2 per n, so all numerators of signed endpoint
    # coefficients are integers, including half-unit shifts in the input.
    N=2*sh.length
    H=N*theta
    lower=xmin*N
    upper=2*(sh.right-sh.start) if xmax is None else xmax*N
    S=2*sh.start; C=sh.left+sh.right; Z=2*sh.right
    poles=[(2*sh.left+int(2*d),2*sh.right-int(2*d),1) for d in sh.offsets]
    zero=[(0,2*a,-1) for a in sh.zeros]+[(2*(sh.left+sh.right-a),2*(sh.left+sh.right),-1) for a in sh.zeros]
    extent=2*(sh.left+sh.right)
    bound=len(sh.offsets)+4
    qmax=floor(Q(extent)/lower)+2
    changes={}
    for a,b,t in poles+zero:
        for j in range(-qmax,qmax+1):
            for x,s in ((a,t),(b,-t)):
                k=(x,j)
                v,m,pc=changes.get(k,(0,0,0))
                changes[k]=v+s,m+(s if t==1 and j==0 else 0),pc+(s if t==1 else 0)
    markers=[(C,0),(Z,0),(S,1)]
    if refined:
        markers.extend((S,j) for j in range(1,qmax+1))
        markers.extend((2*C-S,-j) for j in range(1,qmax+1))
    for mark in markers:
        changes.setdefault(mark,(0,0,0))
    ends={a for a,b,t in poles+zero}|{b for a,b,t in poles+zero}|{C,Z,S,2*C-S,0}
    differences={abs(a-b) for a in ends for b in ends if a!=b}|{abs(a+b-2*C) for a in ends for b in ends if a+b!=2*C}
    # Folded endpoints may cross x/2. Include the doubled numerators of
    # those slope walls, in addition to pair intersections of raw lines.
    differences|={2*d for d in tuple(differences)}
    walls={lower,Q(upper)}
    walls.update(Q(d,j) for d in differences for j in range(1,4*qmax+5) if lower<Q(d,j)<upper)
    walls.update(2*H/j for j in range(1,ceil_q(2*H/lower)+1) if lower<2*H/j<upper)
    walls=sorted(walls)
    lines=np.array(sorted(changes),dtype=np.int64)
    deltas=np.array([changes[tuple(row)] for row in lines],dtype=np.int64)
    strict=split=joint_rate=lower*H*bound
    tiles=[]
    for l,r in zip(walls,walls[1:]):
        mid=(l+r)/2
        n,d=mid.numerator,mid.denominator
        projected=lines[:,0]*d+lines[:,1]*n
        perm=np.argsort(projected,kind='stable')
        points=projected[perm]; coords=lines[perm]
        sums=np.cumsum(deltas[perm],axis=0)
        normal=sum(t*(Q(b-a)//mid) for a,b,t in poles+zero)
        raw=[(0,0) for _ in range(bound+1)]
        segments=[]
        low_i=int(np.searchsorted(points,C*d,side='left'))
        high_i=int(np.searchsorted(points,Z*d,side='right'))
        for i in range(low_i,high_i-1):
            v,w=int(points[i]),int(points[i+1])
            if v<C*d or w>Z*d or v==w:
                continue
            a,m,pole_count=map(int,sums[i]); B=a-normal+(4 if v>=S*d+n else -1)
            if B<=0 or not m:
                continue
            assert B<=bound
            start,end=tuple(map(int,coords[i])),tuple(map(int,coords[i+1]))
            delta0,delta1=end[0]-start[0],end[1]-start[1]
            costs=(B,)*m
            if refined:
                top=normal+m-a
                right_count=(v+w-2*S*d)//(2*n)
                left_count=((4*C-2*S)*d-v-w)//(2*n)
                costs=jet_slot_costs(m,top,pole_count-m,pole_count-a,right_count,left_count)
                assert max(costs)<=B
            segments.append((start,end,tuple(c for c in costs if c>0)))
            raw_costs=[c-2*j if mid>2*H else c for j,c in enumerate(costs)]
            for j in range(1,max(costs)+1):
                k=sum(c>=j for c in raw_costs)
                a0,a1=raw[j]
                raw[j]=a0+delta0*k,a1+delta1*k
        u=sum((linear_cap(H,*c,l,r) for c in raw[1:]),Q(0))
        regions,joint_regions=folded_regions(segments,mid,C)
        margin=floor(2*H/mid)
        scores=[];joint_scores=[]
        profiles={key for key,i in joint_regions}
        if mid<N*Q(9,200):
            trials=sorted({0,margin//2,max(0,margin-5),max(0,margin-3),max(0,margin-1),margin})
        else:
            trials=range(margin+1)
        for q in trials:
            cost=Q(0)
            for j in range(1,bound+1):
                delta0=sum(((B-j)//2+q+1)*regions[(B,0)] for B in range(j,bound+1))
                delta1=sum(((B-j)//2+q+1)*regions[(B,1)] for B in range(j,bound+1))
                cost+=linear_cap(H,Q(delta0,2),Q(delta1,2),l,r)
            correction=sum((2*H-j*(l+r)/2)*(r-l) for j in range(q+1,margin+1))
            scores.append(cost+correction)
            lc=[(0,0) for _ in range(bound+1)]
            for p in profiles:
                a,b=joint_regions[(p,0)],joint_regions[(p,1)]
                slots=Counter()
                for k,B in enumerate(p):
                    score=B-2*max(0,k-q)
                    if score<1:
                        break
                    slots[score]+=1
                for score,count in slots.items():
                    x,y=lc[score]
                    lc[score]=x+a*count,y+b*count
            limits=list(lc)
            for score in range(bound-1,0,-1):
                x,y=lc[score];a,b=limits[score+1]
                limits[score]=x+a,y+b
            joint_scores.append(correction+sum((linear_cap(H,Q(a,2),Q(b,2),l,r) for a,b in limits[1:]),Q(0)))
        selected_strict=min(u,scores[0]); selected_split=min(u,*scores)
        strict+=selected_strict
        split+=selected_split
        selected_joint=min(selected_split,*joint_scores)
        joint_rate+=selected_joint
        tiles.append((sh.name,str(theta),str(l/N),str(r/N),str(u/(N*H)),str(scores[0]/(N*H)),str(selected_strict/(N*H)),str(selected_split/(N*H)),str(selected_joint/(N*H))))
    return strict/(N*H),split/(N*H),joint_rate/(N*H),tiles


def ceil_q(x):
    return -floor(-x)


def asymptotic_replay(screen_path,out,names):
    out.mkdir(exist_ok=True,parents=True)
    source=table(screen_path)
    listed=([(r,Q(r['theta_u'])) for r in source if r['profile'] in names][:12] if names else
            [(r,Q(r['theta_u'])) for r in shortlist(screen_path,'grid',2)+shortlist(screen_path,'gate',2)])
    if not listed:
        raise ValueError('no profiles match')
    summaries=[]; phases=[]; arithmetic=[]
    for r,t in listed:
        sh=parse_shape(r)
        c=Q(r['contour_c_u'])
        R,phase=phase_certificate(sh,t,c)
        print('Arb phase',sh.name,t,float(R),flush=True)
        A,B,J,tiles=arithmetic_certificate(sh,t)
        gaps=[R+arb(qstr(q)) for q in (A,B,J)]
        summaries.append((sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(map(str,sh.offsets)),str(t),str(c),str(R),str(A),str(B),str(J),str(gaps[0]),str(gaps[1]),str(gaps[2]),len(tiles)))
        phases.extend(phase);arithmetic.extend(tiles)
        print('budget',sh.name,t,float(A),float(B),float(J),float(gaps[2]),flush=True)
        csv_write(out/'s14-certified.csv',('profile','L0','U0','zeros','offsets','theta_u','contour_c_u','real_Arb_upper','strict_budget_Q','split_budget_Q','joint_budget_Q','strict_net_upper','split_net_upper','joint_net_upper','n_exact_tiles'),summaries)
        csv_write(out/'s14-phase-tiles.csv',('profile','theta_u','contour_c_u','theta_lo','theta_hi','roots','arb_cap_lo','arb_cap_hi','n_boxes'),phases)
        csv_write(out/'s14-arithmetic-tiles.csv',('profile','theta_u','p_low_u','p_high_u','unfolded','q_zero','strict_selected','split_selected','joint_selected'),arithmetic)




def confluent_recipes():
    bases=[(25,21,3,2),(25,22,3,2),(25,22,2,3),(25,21,2,3),
           (30,26,3,3),(30,26,4,2),(30,25,4,2),(30,27,3,3),(20,17,2,3),(20,17,3,2),
           (40,35,4,3),(40,34,4,3),(40,35,5,2)]
    for L,U,T,J in bases:
        S=U-T
        inner=tuple(range(U-5+J,U))+(U,)
        for dmax in (0,1):
            zeros=(S,)*J+tuple(max(S+1,a-dmax) for a in inner[-(5-J):])
            zeros=tuple(sorted(zeros))
            q0=sum(z>=S+T for z in zeros)
            attached=[S+T-z for z in zeros if S<z<S+T]
            for excess in range(2*J-1,2*J+2):
                m0=excess+q0
                tail=14-m0-len(attached)
                if tail<1:
                    continue
                for drift in (0,1):
                    offsets=tuple(sorted(map(Q,[0]*m0+attached+[T+drift*k for k in range(tail)])))
                    sh=Shape(f'confluent{L}-{U}-{T}-{J}-{excess}-{drift}-{dmax}',L,U,zeros,offsets)
                    theta=Q(J*T,L)
                    if (sh.theta_ok(theta) and max(offsets)<Q(45,100)*L and all(Q(L,2)<=x<=U for x in zeros)
                        and U+T<=L and confluent_parameters(sh,theta)):
                        yield sh,theta


def confluent_parameters(sh,theta):
    for J in (2,3,4):
        conditions=gate_parameters(sh,theta/J)
        if conditions is None:
            continue
        T,A,B=conditions
        if B-2*(J-1)<1:
            continue
        possible=range(sum(z>=sh.start+T for z in sh.zeros),sum(z>sh.start for z in sh.zeros)+1)
        D=B-4
        finite_units={}
        for q in possible:
            m=D+q
            U=fmpq_mat([[comb(D+3-a-b,m-1-a-b) if a+b<m else 0 for b in range(J)] for a in range(J)])
            if not U.det():
                break
            finite_units[q]=int(U.det())
        else:
            return T,A,B,J,finite_units
    return None


def confluent_mod_test(sh,n,theta,mats=None,blocks=None):
    T,A,B,J,units=confluent_parameters(sh,theta)
    p=A*n+1;h=J*T*n
    if not fmpz(p).is_prime() or p<max(16,2*h+1) or any(u%p==0 for u in units.values()):
        return None
    if mats is None:
        mats,blocks=exact_shape(sh,n,h)
    basis=integer_basis(h,((sh.left+sh.right)*n)%2)
    region=range(sh.right*n+2-T*n,sh.right*n+2)
    degrees=list(range(J))*len(region)
    nodes=[(blocks[k][0],a) for k in region for a in range(J)]
    V=fmpq_mat([[sum((basis[i,j]*comb(2*j,a)*x**(2*j-a) for j in range((a+1)//2,i+1)),fmpq(0))
                 for x,a in nodes] for i in range(h)])
    Vmod=nmod_mat([[reduction(V[i,j],p) for j in range(h)] for i in range(h)],p)
    assert Vmod.rank()==h
    inverse=V.inv()
    test=[[0]*h for _ in range(h)]
    for j,k in enumerate(region):
        _,jet,_=blocks[k]
        q=sum((k-p)<=n*z for z in sh.zeros)
        m=len(jet)
        assert m+4-q==B
        w=(-1)**(q+1)*reduction(jet[0]/fmpz(-p)**q,p)
        for a in range(J):
            for b in range(J):
                test[j*J+a][j*J+b]=(w*comb(m+3-q-a-b,m-1-a-b))%p if a+b<m else 0
    expected=nmod_mat(test,p)
    assert expected.rank()==h
    for idx,M in mats.items():
        W=inverse*M*inverse.transpose()
        X=nmod_mat([[reduction(W[i,j]*fmpz(p)**(B-degrees[i]-degrees[j]),p) for j in range(h)] for i in range(h)],p)
        if idx:
            assert X.rank()==0
        else:
            assert X==expected
    result=int(expected.det()*Vmod.det()*Vmod.det())%p
    return p,h,J,B,-B*h+(J-1)*h,result,';'.join(f'{q}:{u}' for q,u in units.items())


def confluent_scan(out):
    out.mkdir(exist_ok=True,parents=True)
    rows=[]
    for sh,t in confluent_recipes():
        R,c=phase_grid(sh,[t])[0]
        A,B=pole_grid(sh,[t],nprime=89,nspace=91)[0]
        rows.append((sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(map(str,sh.offsets)),str(t),str(c),float(sh.gap/sh.length),R,A,B,R+A,R+B))
    write_screen(out,rows)


def confluent_run(scan,out):
    out.mkdir(exist_ok=True,parents=True)
    result=[]; visited=set(); experiment=[]
    for row in table(scan):
        sh=parse_shape(row)
        t=Q(row['theta_u'])
        T,A,B,J,units=confluent_parameters(sh,t)
        key=(sh.length,sh.left,sh.start,t)
        if key in visited:
            continue
        visited.add(key)
        if len(visited)>6:
            break
        found=0
        for n in range(1,6):
            h=J*T*n
            if h>32:
                break
            if h<4:
                continue
            p=A*n+1
            if found<2 and p>max(16,2*h) and fmpz(p).is_prime() and all(u%p for u in units.values()):
                ans=confluent_mod_test(sh,n,t)
                result.append((sh.name,n,*ans))
                found+=1
                print('confluent gate',sh.name,n,ans,flush=True)
            if n in (1,2,3,4):
                finite_case(sh,n,(h,),out)
        csv_write(out/'confluent-gates.csv',('profile','n','p','h','jet_slots_per_node','B','v_p_determinant','normalized_det_mod_p','local_binomial_units'),result)




def log_order(p,k):
    power=p
    val=0
    while power<=k:
        val+=1
        power*=p
    return val


def local_joint_bound(blocks,p,h):
    # Actual Laurent and reflected-harmonic coefficients at each site, with
    # the same jet-capacity proof as for the rational asymptotic tiles.
    b=max(1,log_order(p,2*h-2))
    rows=[valuation(fmpq(factorial_z(2*i)),p) for i in range(h)]
    by_residue={}
    raw=[]
    for _,(x,jet,M) in blocks.items():
        costs=[b*r-valuation(a,p) for q,v in M.items() for r,a in enumerate(v) if a]
        if not costs or max(costs)<=0:
            continue
        # b=0 for p>2h; use b=1 there since the valuation of shifts
        # supplies one p-power per jet degree independently of basis size.
        B=int(max(costs))
        m=len(jet)
        raw.extend([B]*m)
        if p>2:
            u=reduction(x,p)
            rep=min(u,p-u)
            by_residue.setdefault(rep,[]).extend([B]*m)
    unfolded=sum(sorted(raw,reverse=True)[:h])
    if p==2:
        return unfolded
    selected=unfolded
    q_max=max(rows) if b<=1 else 0
    for q in range(q_max+1):
        candidates=sorted((max(0,B-2*max(0,j-q)) for t in by_residue.values()
                           for j,B in enumerate(sorted(t,reverse=True))),reverse=True)
        penalty=2*sum(max(0,a-q) for a in rows)
        selected=min(selected,sum(candidates[:h])+penalty)
    return selected


def grade_audit(sh,n,h,out):
    ctx.prec=128
    matrices,blocks=exact_shape(sh,n,h)
    v,spec=p_content_bounds(matrices,(sh.left+sh.right)*n+2)
    rows=[]
    for p,entry,lower,upper in v:
        if p>(sh.right-sh.start)*n:
            continue
        local=local_joint_bound(blocks,p,h)
        assert -local<=upper,(sh,n,h,p,local,upper)
        rigorous=max(-local,entry,lower)
        assert rigorous<=upper
        grp='p_le_2h' if p<=2*h else '2h_to_half_L' if 2*p<=sh.length*n else 'p_gt_both_2h_half_L'
        rows.append((sh.name,n,h,p,str(Q(p,sh.length*n)),grp,entry,local,lower,upper,abs(upper)*float(arb(p).log())/(sh.length*n*h),
                     (upper+local)*float(arb(p).log())/(sh.length*n*h),(lower-entry)*float(arb(p).log())/(sh.length*n*h)))
    csv_write(out/f'{sh.name}-{n}-{h}-joint-audit.csv',('profile','n','h','p','p_over_L0n','segment','entry_v_lower','local_jet_cost_upper','joint_lattice_v_lower','specialization_v_upper','abs_specialized_val_logp_nhL0','gap_local_jet_vs_specialization','exact_lattice_gain_lower'),rows)
    print('prime audit',sh.name,n,h,sum(r[-2] for r in rows),flush=True)





def linear_program_roots(inventory,delta,t):
    import numpy as np
    from scipy.optimize import linprog
    from math import pi
    y=(np.arange(750)+.157)*.0018
    roots=np.arange(107)*.0085+.006
    F=phase_values(inventory,y)
    M=np.column_stack([float(t)/2*pair_values(y,(x,),float(delta)) for x in roots])
    result=linprog(np.r_[np.zeros(len(roots)),1],A_ub=np.column_stack([M,-np.ones(len(y))]),b_ub=-F,
                   A_eq=[np.r_[np.ones(len(roots)),0]],b_eq=[1],bounds=[(0,None)]*len(roots)+[(None,None)],method='highs')
    assert result.success
    counts=[round(a*1000000) for a in result.x[:-1]]
    chosen=max(range(len(counts)),key=counts.__getitem__)
    counts[chosen]+=1000000-sum(counts)
    return tuple((Q(round(x*10000),10000),Q(w,1000000)) for x,w in zip(roots,counts) if w>0)


def weighted_phase_certificate(sh,theta,contour):
    ctx.prec=112
    inventory=phase_inventory(sh,contour)
    delta=sh.center/sh.length-contour
    integral=arb(0); parts=[]
    for i in range(8):
        x=theta*i/8;y=theta*(i+1)/8
        atoms=linear_program_roots(inventory,delta,(x+y)/2)
        roots,weights=zip(*atoms)
        a,na=certify_phase_sup(inventory,delta,roots,x, Q(1,300),weights)
        b,nb=certify_phase_sup(inventory,delta,roots,y, Q(1,300),weights)
        integral+=arb(qstr(y-x))*(a+b)/2
        parts.append((sh.name,str(theta),str(contour),str(x),str(y),';'.join(f'{a}:{w}' for a,w in atoms),str(a),str(b),na+nb))
    t=arb(qstr(theta))
    return integral/t+t*(3-2*(2*t).log()),parts


def improve_certificates(screen_path,out):
    rows=table(screen_path)
    out.mkdir(exist_ok=True,parents=True)
    summaries=[]; phases=[]; all_tiles=[]
    for r in rows:
        sh=parse_shape(r)
        theta=Q(r['theta_u'])
        # Test additional contours approaching the zero at the start of
        # the original unshifted numerator. The strip remains pole-free.
        old=Q(r['contour_c_u'])
        R,chosen,tiles=min([(R,c,tiles) for c in sorted({Q(1,50),old})
                           for R,tiles in [weighted_phase_certificate(sh,theta,c)]],key=lambda packet:float(packet[0]))
        print('weighted real',sh.name,float(R),flush=True)
        strict,split,joint,arithmetic=arithmetic_certificate(sh,theta,xmin=Q(9,200))
        ctx.prec=128
        combined=R+arb(qstr(joint))
        print('tighter cutoff',sh.name,float(joint),float(combined),flush=True)
        summaries.append((sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(map(str,sh.offsets)),str(theta),str(chosen),str(R),str(strict),str(split),str(joint),
                          str(R+arb(qstr(strict))),str(R+arb(qstr(split))),str(combined),len(arithmetic)))
        phases.extend(tiles);all_tiles.extend(arithmetic)
        csv_write(out/'s14-certified.csv',('profile','L0','U0','zeros','offsets','theta_u','contour_c_u','real_Arb_upper','strict_budget_Q','split_budget_Q','joint_budget_Q','strict_net_upper','split_net_upper','joint_net_upper','n_exact_tiles'),summaries)
        csv_write(out/'s14-phase-tiles.csv',('profile','theta_u','contour_c_u','theta_lo','theta_hi','roots_and_weights','arb_cap_lo','arb_cap_hi','n_boxes'),phases)
        csv_write(out/'s14-arithmetic-tiles.csv',('profile','theta_u','p_low_u','p_high_u','unfolded','q_zero','strict_selected','split_selected','joint_selected'),all_tiles)




def residue_period(sh):
    # In units x=2p/n every continuum endpoint is integral. The base
    # residue cost depends only on tau={1/x} and w=(k-center)/x modulo 1.
    import numpy as np
    center=sh.left+sh.right
    spans=[(2*sh.left+int(2*d)-center,2*sh.right-int(2*d)-center,1) for d in sh.offsets]
    spans += [(-center,2*a-center,-1) for a in sh.zeros]
    spans += [(center-2*a,center,-1) for a in sh.zeros]
    jump=Counter()
    endpoints=set()
    for a,b,e in spans:
        jump[a]+=e;jump[b]-=e
        endpoints.update((a,b))
    lengths=Counter()
    for a,b,e in spans:
        lengths[b-a]+=e
    slopes=[(a,j) for a,e in sorted(jump.items()) if e for j in range(min(0,a)-1,max(0,a)+1)]
    slopes.extend(((0,0),(0,-1)))
    slopes=np.array(sorted(set(slopes)),dtype=np.int64)
    events={Q(0),Q(1)}
    denominators={abs(a-b) for a in endpoints|{0} for b in endpoints|{0} if a!=b}|{d for d in lengths if lengths[d]}
    for d in denominators:
        events.update(Q(k,d) for k in range(1,d))
    events=sorted(events)
    output=[]
    for l,r in zip(events,events[1:]):
        mid=(l+r)/2
        n,d=mid.numerator,mid.denominator
        positions=slopes[:,0]*n-slopes[:,1]*d
        active=np.nonzero((0<=positions)&(positions<=d))[0]
        active=active[np.argsort(positions[active],kind='stable')]
        heights=[]
        integral=0; slope=0; second=0; second_slope=0
        normal=sum(e*((length*n)//d) for length,e in lengths.items())
        for i,j in zip(active,active[1:]):
            lo,hi=int(positions[i]),int(positions[j])
            if lo==hi:
                continue
            w=lo+hi
            value=4-normal+sum(e*(((2*b*n-w)//(2*d))-((2*a*n-w)//(2*d))) for a,b,e in spans)
            B=max(0,value)
            G=sum(j//2 for j in range(B))
            a0=int(slopes[i][1]-slopes[j][1]);a1=int(slopes[j][0]-slopes[i][0])
            integral+=a0*B;slope+=a1*B
            second+=a0*G;second_slope+=a1*G
        a,b,c,e=integral,slope,second,second_slope
        assert min(a+b*l,a+b*r,c+e*l,c+e*r)>=0
        output.append((l,r,a,b,c,e))
    return output


def periodic_low_budget(sh,theta,cut=Q(9,200),periods=45,exact_weights=False):
    # Use Arb for the sum, and exact rational inputs on every tile. A
    # left-endpoint upper Riemann weight is valid because F and G are >=0.
    # The inverse-square and inverse-cube tails use integral comparison.
    ctx.prec=120
    N=2*sh.length
    H=N*theta
    first=1/(cut*N)
    pieces=residue_period(sh)
    bound=arb(0); F_bar=Q(0); G_bar=Q(0)
    for l,r,a,b,c,d in pieces:
        I=(r-l)*(a+b*(l+r)/2)
        J=(r-l)*(c+d*(l+r)/2)
        F_bar+=I;G_bar+=J
        for k in range(floor(first),periods):
            left=max(first-k,l)
            if left>=r:
                continue
            X=(r-left)*(a+b*(r+left)/2)
            Y=(r-left)*(c+d*(r+left)/2)
            den=Q(k)+left
            if exact_weights:
                right=Q(k)+r
                delta=1/den-1/right
                logarithm=arb(qstr(right/den)).log()
                first_integral=arb(qstr((a-b*k)*delta))+b*logarithm
                second_integral=((a+c-(b+d)*k)*(1/den**2-1/right**2)/2+(b+d)*delta)/(2*H)
                bound+=first_integral+arb(qstr(second_integral))
            else:
                bound+=arb(qstr(X/(den**2)+(X+Y)/(2*H*den**3)))
    bound+=arb(qstr(F_bar/(periods-1)+(F_bar+G_bar)/(4*H*(periods-1)**2)))
    return bound/N,F_bar,G_bar,pieces


def close_small_primes(input_files,out,exact_weights=False):
    out.mkdir(exist_ok=True,parents=True)
    summary=[];checks=[]
    for csv in input_files:
        for r in table(csv):
            sh=parse_shape(r)
            theta=Q(r['theta_u'])
            cut=Q(9,200)
            budget,mean,second,pieces=periodic_low_budget(sh,theta,cut,exact_weights=exact_weights)
            R=arb(r['real_Arb_upper'])
            A=arb(qstr(Q(r['joint_budget_Q'])-(len(sh.offsets)+4)*cut))+budget
            net=A+R
            print('periodic low',sh.name,theta,'mean',float(mean),'old segment',float((len(sh.offsets)+4)*cut),'new segment',float(budget),'gap',float(net),flush=True)
            summary.append((sh.name,sh.length,sh.left,repr(sh.zeros),';'.join(map(str,sh.offsets)),str(theta),r['contour_c_u'],str(R),str(A),str(net),str(budget),str(mean),str(second),len(pieces)))
            checks.extend((sh.name,str(theta),str(l),str(u),a,b,c,d) for l,u,a,b,c,d in pieces)
            csv_write(out/'s14-certified.csv',('profile','L0','U0','zeros','offsets','theta_u','contour_c_u','real_Arb_upper','periodic_joint_budget_Arb','joint_net_upper','periodic_low_Arb','period_mean_B','period_mean_jet','n_period_tiles'),summary)
            csv_write(out/'s14-periodic-tiles.csv',('profile','theta_u','tau_lo','tau_hi','F_const','F_slope','G_const','G_slope'),checks)




def inverse_mod_integer(rows,p,mod):
    h=len(rows)
    X=[row.copy()+[int(i==j) for j in range(h)] for i,row in enumerate(rows)]
    for j in range(h):
        k=next(k for k in range(j,h) if X[k][j]%p)
        X[k],X[j]=X[j],X[k]
        z=pow(X[j][j],-1,mod)
        X[j]=[x*z%mod for x in X[j]]
        for k in range(h):
            if k==j or not X[k][j]:
                continue
            a=X[k][j]
            X[k]=[(x-a*y)%mod for x,y in zip(X[k],X[j])]
    assert all(X[i][j]==(i==j) for i in range(h) for j in range(h))
    return [row[h:] for row in X]


def confluent_modular_independent(sh,n,theta):
    T,A,B,J,units=confluent_parameters(sh,theta)
    p=A*n+1;h=J*T*n
    assert fmpz(p).is_prime() and p>max(2*h,16) and all(a%p for a in units.values())
    mod=p**(2*J-1)
    basis=integer_basis(h,((sh.left+sh.right)*n)%2)
    def red(a):
        return int(a.numerator)%mod*pow(int(a.denominator)%mod,-1,mod)%mod
    def series(x,r):
        return [sum((red(basis[i,k])*comb(2*k,r)*pow(x,2*k-r,mod) for k in range((r+1)//2,i+1)))%mod for i in range(h)]
    blocks=exact_shape(sh,n,h,blocks_only=True)
    region=list(range(sh.right*n+2-T*n,sh.right*n+2))
    vectors=[series(red(blocks[k][0]),r) for k in region for r in range(J)]
    lhs=[list(row) for row in zip(*vectors)]
    inverse=nmod_mat(inverse_mod_integer(lhs,p,mod),mod)
    result=nmod_mat(h,h,mod)
    expected=nmod_mat(h,h,p)
    for k,(x,jet,coeffs) in blocks.items():
        for s,c in coeffs.items():
            if s or k not in region:
                assert all(not red(fmpz(p)**B*a) for a in c if a),(k,s)
        if k not in region:
            continue
        index=k-region[0]
        size=min(len(jet),2*J-1)
        columns=nmod_mat([list(row) for row in zip(*(series(red(x),r) for r in range(size)))],mod)
        P=inverse*columns
        coeff=[red(fmpz(p)**B*a) for a in coeffs[0]]
        W=nmod_mat([[coeff[a+b] if a+b<len(coeff) else 0 for b in range(size)] for a in range(size)],mod)
        result+=P*W*P.transpose()
        q=sum((k-p)<=n*z for z in sh.zeros)
        m=len(jet)
        unit=(-1)**(q+1)*red(jet[0]/fmpz(-p)**q)
        for i in range(J):
            for j in range(J):
                expected[index*J+i,index*J+j]=unit*(comb(m+3-q-i-j,m-1-i-j) if i+j<m else 0)%p
    actual=nmod_mat(h,h,p)
    for i in range(h):
        for j in range(h):
            k,power=divmod(int(result[i,j]),p**(i%J+j%J))
            assert power==0
            actual[i,j]=k%p
    assert actual==expected and actual.rank()==h
    V=nmod_mat([[a%p for a in r] for r in lhs],p)
    return p,h,J,B,-B*h+(J-1)*h,int(actual.det()*V.det()*V.det())%p,';'.join(f'{q}:{u}' for q,u in units.items())



def prove_six(out):
    """Recompute the fixed S=14 proof certificate from its exact parameters."""
    out=Path(out);out.mkdir(exist_ok=True,parents=True)
    sh=Shape('confluent40-34-4-3-5-1-1',40,34,(30,30,30,32,33),tuple(map(Q,[0]*5+[1,2,4,5,6,7,8,9,10])))
    theta=Q(3,10);contour=Q(1,50);cut=Q(9,200)
    assert sh.theta_ok(theta)
    T,A,B,J,units=confluent_parameters(sh,theta)
    assert (T,A,B,J,units)==(4,40,9,3,{0:-50,1:-20,2:-1})
    R,phase=weighted_phase_certificate(sh,theta,contour)
    _,_,middle,tiles=arithmetic_certificate(sh,theta,xmin=cut)
    low,F,G,periodic=periodic_low_budget(sh,theta,cut)
    exact_low,_,_,_=periodic_low_budget(sh,theta,cut,exact_weights=True)
    common=arb(qstr(middle-(len(sh.offsets)+4)*cut))
    C=common+low
    exact_C=common+exact_low
    assert R<arb('-7.58994') and C<arb('7.54220')
    assert R+C<arb('-0.04774') and R+exact_C<arb('-0.04774')
    aux=[confluent_modular_independent(sh,n,theta) for n in (1,6)]
    assert all(z[5] for z in aux)
    csv_write(out/'proof-summary.csv',('R_upper','C_upper','net_upper','C_upper_exact_log_weights','net_upper_exact_log_weights','T','A','B','J'),[(str(R),str(C),str(R+C),str(exact_C),str(R+exact_C),T,A,B,J)])
    csv_write(out/'proof-analytic.csv',('profile','theta','c','theta_lo','theta_hi','root_weights','cap_lo','cap_hi','n_boxes'),phase)
    csv_write(out/'proof-high-primes.csv',('profile','theta_u','p_low_u','p_high_u','unfolded','q_zero','strict_selected','split_selected','joint_selected'),tiles)
    csv_write(out/'proof-periodic.csv',('tau_lo','tau_hi','F_const','F_slope','G_const','G_slope'),periodic)
    csv_write(out/'proof-gates.csv',('p','h','J','entry_B','v_p_det','normalized_det_mod_p','local_units'),aux)
    print('R upper',R,'C upper',C,'net upper',R+C,flush=True)
    print('Independent exact log weights',R+exact_C,'gate samples',aux,flush=True)

@lru_cache(None)
def harmonic(s, top):
    sums = [fmpq(0)]
    for k in range(1, top + 1):
        sums.append(sums[-1] + fmpq(1, fmpz(k)**s))
    return sums

def local_jet(k, zeros, poles, normalization, scale):
    order = poles[k] - zeros.get(k, 0)
    if order < 1:
        return []
    multiplicities = zeros.copy()
    multiplicities.subtract(poles)
    constants = {i-k:c for i,c in multiplicities.items() if i!=k and c}
    value = normalization * fmpq(prod(fmpz(d)**c for d,c in constants.items() if c>0),
                                 prod(fmpz(d)**(-c) for d,c in constants.items() if c<0))
    logs = [0 for _ in range(order)]
    for shift, c in constants.items():
        r = -scale[shift]
        power = r
        for j in range(1, order):
            logs[j] -= c * power
            power *= r
    coeffs = [fmpz(1)]
    for j in range(1, order):
        q, rem = divmod(sum(logs[l]*coeffs[j-l] for l in range(1,j+1)),j)
        assert not rem
        coeffs.append(q)
    return [value*x for x in coeffs]

def even_basis(h):
    table = [[fmpq(0) for _ in range(h)] for _ in range(h)]
    table[0][0] = fmpq(1)
    p = [0,1]
    for i in range(1,h):
        table[i][:len(p)]=[fmpq(2*a,factorial(2*i)) for a in p]
        p = [a-i*i*b for a,b in zip([0,*p],[*p,0])]
    return fmpq_mat(table)

def reduction(q,p):
    if int(q.denominator)%p==0:
        raise ValueError('nonintegral at p')
    return int(q.numerator)%p*pow(int(q.denominator)%p,-1,p)%p

def rational_content(matrices):
    h=matrices[0].nrows()
    numbers=list(matrices)
    ring=fmpz_mpoly_ctx.get([f'Z{s}' for s in numbers[1:]])
    gens=ring.gens()
    denom=1
    table=[]
    for i in range(h):
        row=[]
        den=lcm(*(matrices[s][i,j].denominator for s in numbers for j in range(h)))
        denom*=den
        for j in range(h):
            coeffs=[(matrices[s][i,j]*den).numerator for s in numbers]
            row.append(sum((c*g for c,g in zip(coeffs[1:],gens)),ring.constant(coeffs[0])))
        table.append(row)
    prev=ring.constant(1)
    sign=1
    for k in range(h-1):
        pos=next((i for i in range(k,h) if table[i][k]),None)
        if pos is None:
            return fmpq(0),0
        if pos!=k:
            table[pos],table[k]=table[k],table[pos]; sign=-sign
        pivot=table[k][k]
        for i in range(k+1,h):
            for j in range(k+1,h):
                q,r=divmod(pivot*table[i][j]-table[i][k]*table[k][j],prev)
                assert not r
                table[i][j]=q
        prev=pivot
    poly=table[-1][-1]*sign
    coefficients=poly.coeffs()
    return fmpq(gcd(*coefficients),denom),len(coefficients)

def valuation(z,p):
    if not z:
        return float('inf')
    a,b=abs(int(z.numerator)),int(z.denominator)
    result=0
    while a%p==0:
        a//=p;result+=1
    while b%p==0:
        b//=p;result-=1
    return result

def arb_det(matrices,n):
    h=matrices[0].nrows()
    for precision in (4096, 8192, 16384, 32768,65536):
        ctx.prec=precision
        z={s:arb(s).zeta() if s else arb(1) for s in matrices}
        M=arb_mat([[sum((arb(A[i,j])*z[s] for s,A in matrices.items()),arb(0))
                    for j in range(h)] for i in range(h)])
        value=M.det()
        if not value.contains(0):
            result=abs(value).log()/(n*n)
            if result.rel_accuracy_bits()>80:
                ctx.prec=128
                return result+arb(0),precision
    ctx.prec=128
    raise ValueError('determinant sign unresolved')

def csv_write(path,header,rows):
    with Path(path).open('w',encoding='utf-8-sig',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def replay_main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='mode',required=True)
    base=Path(__file__).resolve().parent
    for mode in ('core','controls','screen','confluent-screen','rank','gates','confluent-run','certify','tighten','finite','dump','gate-test','prime-audit','periodic','prove'):
        p=sub.add_parser(mode)
        p.add_argument('--out',type=Path,default=Path('s14-replay'))
        if mode in ('rank','gates','confluent-run','certify','tighten','finite','dump','gate-test','prime-audit'):
            p.add_argument('--screen',type=Path,default=base/'profiles.csv')
        if mode in ('finite','dump','gate-test','prime-audit'):
            p.add_argument('--profile',required=True)
            p.add_argument('--n',type=int,nargs='+',required=True)
            p.add_argument('--h',type=int,nargs='+')
            p.add_argument('--theta',type=Q)
        if mode=='periodic':
            p.add_argument('--inputs',nargs='+',type=Path,required=True)
            p.add_argument('--exact-weights',action='store_true')
        if mode=='gate-test':
            p.add_argument('--direct-modular',action='store_true')
        if mode in ('certify','tighten'):
            p.add_argument('--profiles',nargs='+',default=[])
            p.add_argument('--theta',type=Q)
    a=parser.parse_args()
    a.out.mkdir(exist_ok=True,parents=True)
    if a.mode=='prove':
        prove_six(a.out)
    elif a.mode=='core':
        run_core(a.out)
    elif a.mode=='controls':
        run_controls(a.out)
    elif a.mode=='screen':
        screening(a.out)
    elif a.mode=='confluent-screen':
        confluent_scan(a.out)
    elif a.mode=='rank':
        rank_cases(a.screen,a.out)
    elif a.mode=='gates':
        proposed_gates(a.screen,a.out)
    elif a.mode=='confluent-run':
        confluent_run(a.screen,a.out)
    elif a.mode=='periodic':
        close_small_primes(a.inputs,a.out,exact_weights=a.exact_weights)
    elif a.mode in ('certify','tighten'):
        path=a.screen
        if a.theta is not None or a.mode=='tighten':
            names=a.profiles or ['confluent30-26-3-3-6-1-1','grid169']
            rows=[r for r in table(path) if r['profile'] in names and (a.theta is None or Q(r['theta_u'])==a.theta)]
            rows=list({r['profile']:r for r in reversed(rows)}.values())
            if not rows:
                parser.error('No profiles have the requested theta.')
            path=a.out/'selected-profiles.csv'
            csv_write(path,list(rows[0]),[list(r.values()) for r in rows])
        if a.mode=='certify':
            asymptotic_replay(path,a.out,set(a.profiles or [r['profile'] for r in table(path)] if a.theta is not None else a.profiles))
        else:
            improve_certificates(path,a.out)
    elif a.mode in ('finite','dump','gate-test','prime-audit'):
        opts=[r for r in table(a.screen) if r['profile']==a.profile and (a.theta is None or Q(r['theta_u'])==a.theta)]
        if opts:
            sh=parse_shape(opts[0])
            t=a.theta or Q(opts[0]['theta_u'])
        else:
            sh=next((r for r in (CORE,ORIGINAL,DROP6) if r.name==a.profile),None)
            if sh is None or (a.theta is None and a.h is None):
                parser.error('Provide an available profile and theta or matrix size.')
            t=a.theta
        for n in a.n:
            hs=a.h if a.h else [floor(t*n*sh.length)]
            if a.mode=='finite':
                finite_case(sh,n,hs,a.out)
            elif a.mode=='dump':
                m,_=exact_shape(sh,n,max(hs))
                for h in hs:
                    rows=[(sh.name,n,h,i,j,q,str(A[i,j])) for q,A in m.items() for i in range(h) for j in range(i,h)]
                    csv_write(a.out/f'{sh.name}-{n}-{h}-matrix.csv',('profile','n','h','i','j','odd_zeta_or_constant','coefficient_Q'),rows)
            elif a.mode=='prime-audit':
                for h in hs:
                    grade_audit(sh,n,h,a.out)
            elif a.mode=='gate-test':
                if t is None:
                    t=Q(hs[0],sh.length*n)
                if confluent_parameters(sh,t):
                    print(sh.name,n,confluent_modular_independent(sh,n,t) if a.direct_modular else confluent_mod_test(sh,n,t))
                elif gate_parameters(sh,t):
                    print(sh.name,n,gate_witness(sh,n,t))
                else:
                    print(sh.name,n,'profile does not satisfy the all-n gate hypotheses')


if __name__=='__main__':
    replay_main()
