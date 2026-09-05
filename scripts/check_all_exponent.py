#!/usr/bin/env python3
"""Exact finite regressions for the all-exponent research note.

These check polynomial identities and bounded residue combinatorics only.
They do not verify monodromy density, algebraic correspondences, or HC.
Requires Python >=3.10 and SymPy. No floating-point decisions or assert statements.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
import math
import platform
from collections import defaultdict
from pathlib import Path
import sympy as sp

Word = tuple[int, ...]
V4 = ((0,1,2,3),(1,0,3,2),(2,3,0,1),(3,2,1,0))

def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)

def orbit(a: Word, n: int) -> set[Word]:
    return {tuple((sgn*a[i]) % n for i in p) for p in V4 for sgn in (1,-1)}

def pair_key(a: Word, n: int) -> Word:
    return tuple(min(t, (-t)%n) for t in ((a[0]+a[j])%n for j in (1,2,3)))

def j_zero(a: Word, n: int) -> bool:
    return n%2 == 0 and any((a[i]+a[j])%n == n//2 for i,j in ((0,1),(0,2),(1,2)))

def symbolic() -> dict:
    u,v,w,aa,bb=sp.symbols('u v w aa bb', nonzero=True)
    x=sp.Symbol('x')
    A=sp.Matrix([[u*v,v*(1-u)],[0,1]])
    B=sp.Matrix([[1,0],[1-w,v*w]])
    J=sp.factor(sp.trace(A)*sp.trace(B)*sp.trace(A*B)/(A.det()*B.det()))
    expected=(1+u*v)*(1+u*w)*(1+v*w)/(u*v*w)
    require(sp.cancel(J-expected)==0, 'Fricke identity')
    require(sp.expand((A*B).charpoly(x).as_expr()-(x-v)*(x-u*v*w))==0, 'product spectrum')
    require(sp.cancel(J+J.xreplace({u:-u,v:-v,w:-w}))==0,'half-turn sign')
    Js=sp.trace(aa*A)*sp.trace(bb*B)*sp.trace(aa*bb*A*B)/((aa*A).det()*(bb*B).det())
    require(sp.cancel(J-Js)==0,'independent scalar invariance')
    sym=u+1/u+v+1/v+w+1/w+u*v*w+1/(u*v*w)
    require(sp.cancel(J-sym)==0,'symmetric root expression')
    return {'identities':5,'product_characteristic_polynomial':'(X-v)(X-u*v*w)',
            'fricke_invariant':'(1+u*v)(1+u*w)(1+v*w)/(u*v*w)'}

def four_words(max_n: int) -> dict:
    total=collisions=separated=zero_cases=0
    rows=[]
    for n in range(2,max_n+1):
        buckets: dict[Word,list[Word]]=defaultdict(list)
        count=0
        for a,b,c in it.product(range(1,n),repeat=3):
            d=(-a-b-c)%n
            if not d: continue
            word=(a,b,c,d)
            buckets[pair_key(word,n)].append(word)
            count+=1
        paircount=sepcount=0
        for bucket in buckets.values():
            # All comparisons with one representative suffice to classify the
            # entire bucket into its orbit and (at most) a half-shifted orbit.
            a=bucket[0]
            oa=orbit(a,n)
            shifted=tuple((v+n//2)%n for v in a) if n%2==0 else ()
            os=orbit(shifted,n) if shifted and all(shifted) else set()
            for b in bucket:
                paircount+=1
                require(b in oa or b in os, f'pair reconstruction failed {n,a,b}')
                if b not in oa:
                    require(not j_zero(a,n), f'Fricke failed to distinguish {n,a,b}')
                    # Same pair spectrum + different orbit forces -J, nonzero.
                    sepcount+=1
            if shifted and all(shifted) and j_zero(a,n):
                require(shifted in oa,f'zero Fricke collision not already geometric {n,a}')
                zero_cases+=1
        total+=count; collisions+=paircount; separated+=sepcount
        rows.append({'modulus':n,'active_zero_sum_words':count,
                     'pair_spectrum_buckets':len(buckets),'nongraph_candidates_separated':sepcount})
    return {'max_modulus':max_n,'words':total,'representative_comparisons':collisions,
            'nongraph_candidates_separated':separated,'zero_invariant_orbit_checks':zero_cases,
            'per_modulus':rows}

def higher_rank(max_n: int) -> dict:
    # Pair agreement determines e_i-c_i to be one common element of 2-torsion.
    # A triple-product equality then kills that element, with no division by 2.
    checked=0
    for n in range(2,max_n+1):
        for a,b,c in it.product(range(n),repeat=3):
            if (a+b)%n or (a+c)%n or (b+c)%n: continue
            require(a==b==c and (2*a)%n==0, f'pair kernel {n,a,b,c}')
            if (a+b+c)%n==0:
                require(a==b==c==0, f'pair/triple reconstruction {n,a,b,c}')
            checked+=1
    return {'moduli':list(range(2,max_n+1)),'pair_kernel_solutions':checked}

def three_point_type(a: Word, d: int) -> dict:
    """Check the pure-type comparison with the connected three-point factor.

    This is the arithmetic in the proposed isogeny lemma, not a verification
    of the equivalence between weight-one Hodge structures and abelian varieties.
    """
    require(math.gcd(d, *a)==1, 'word must have actual conductor d')
    require(all(0<x<d for x in a) and sum(a)%d==0, 'branch validity')
    units=[u for u in range(1,d) if math.gcd(u,d)==1]
    qs={u:sum((u*x)%d for x in a)//d for u in units}
    s=len(a)
    require(all(q in (1,s-1) for q in qs.values()), 'not all definite')
    e=math.gcd(d,a[0],a[1]); m=d//e
    tri=(a[0]//e, a[1]//e, (-(a[0]+a[1])//e)%m)
    require(m>=3 and all(0<x<m for x in tri), 'inactive triangle')
    require(math.gcd(m,*tri)==1, 'triangle not connected')
    for u in units:
        tq=sum((u*x)%m for x in tri)//m
        require(tq==(1 if qs[u]==1 else 2), f'three-point type mismatch {d,a,u}')
    phi_d=len(units)
    phi_m=sum(math.gcd(u,m)==1 for u in range(1,m))
    require(phi_d%phi_m==0,'field-degree divisibility')
    return {'conductor':d,'word':a,'rank':s-2,'triangle_conductor':m,
            'triangle':tri,'field_degree':phi_d//phi_m,
            'predicted_isogeny_multiplicity':(s-2)*(phi_d//phi_m),
            'pure_types_match':True}

def definite_four_words(max_n: int) -> dict:
    # First row of an all-definite orbit has sum d or 3d. Negation exchanges
    # the two, so enumerating positive compositions of d into four parts
    # covers all such words up to simultaneous negation.
    checked=0; examples=[]; reduced=0
    for d in range(3,max_n+1):
        units=[u for u in range(1,d) if math.gcd(u,d)==1]
        for a in range(1,d-2):
            for b in range(1,d-a-1):
                for c in range(1,d-a-b):
                    word=(a,b,c,d-a-b-c)
                    if math.gcd(d,*word)!=1: continue
                    if not all(sum((u*x)%d for x in word) in (d,3*d) for u in units): continue
                    result=three_point_type(word,d)
                    checked+=1
                    if result['triangle_conductor']<d:
                        reduced+=1
                        if len(examples)<4: examples.append(result)
    return {'max_conductor':max_n,'normalization':'positive first-row sum d; negation covers sum 3d',
            'all_definite_primitive_words':checked,'proper_triangle_conductor_cases':reduced,
            'proper_conductor_examples':examples}

def examples() -> dict:
    a=(1,1,1,5); n=8; b=tuple((x+4)%8 for x in a)
    require(pair_key(a,n)==pair_key(b,n),'example pair equality')
    require(b not in orbit(a,n) and not j_zero(a,n),'example Fricke separation')
    return {'even_rank_two_collision':{'modulus':n,'first':a,'second':b,
             'same_pair_spectra':True,'same_graph_orbit':False,'Fricke_separates':True},
            'finite_part_triangle_checks':[three_point_type(a,d) for d,a in
             [(4,(1,1,1,1)),(6,(1,1,1,1,1,1)),(15,(1,2,4,8))]]}

def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-modulus',type=int,default=32)
    p.add_argument('--output',type=Path,default=Path('all_exponent_report.json'))
    args=p.parse_args()
    if not 2<=args.max_modulus<=80: p.error('max modulus must be between 2 and 80')
    report={'status':'passed','scope':'symbolic algebra and bounded arithmetic only; no geometric or Lean verification',
            'python':platform.python_version(),'sympy':sp.__version__,
            'symbolic':symbolic(),'four_point_reconstruction':four_words(args.max_modulus),
            'higher_rank_pair_triple_kernel':higher_rank(args.max_modulus),
            'all_definite_triangle_types':definite_four_words(args.max_modulus), 'examples':examples()}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k not in ('four_point_reconstruction','examples')},indent=2))
    print('Four-point words checked:',report['four_point_reconstruction']['words'])
    print('Nongraph candidates separated:',report['four_point_reconstruction']['nongraph_candidates_separated'])
    print('Report:',args.output)
if __name__=='__main__': main()
