"""Exact coefficient and finite-field controls for the 18-form checkpoint."""
from functools import lru_cache
from itertools import product
from math import comb, prod
from random import Random

from bilinear_controls import interpolation_elements, bilinear_descent
from frobenius_controls import conjugate_matrices
from norm_controls import Field, determinant, PERMS, SIGNS
from paired_controls import combined
from verify import require


def matrices(u):
    # Direct matrix transcription of CGLV, Thm 4.1; multiply column 2 by 3.
    v = 1-u
    return (
        ((-u,0,0),(0,-1,0),(0,0,v)), ((-v,0,0),(0,-1,0),(0,0,u)),
        ((-v,0,0),(0,v,0),(0,0,v)), ((-1,0,0),(0,0,-v),(0,-u,0)),
        ((v,0,0),(0,0,1),(0,-u,0)), ((u,0,0),(0,0,-u),(0,-u,0)),
        ((0,v,0),(-u,0,0),(0,0,1)), ((0,v,0),(-v,0,0),(0,0,-v)),
        ((0,u,0),(-v,0,0),(0,0,1)), ((0,-u,0),(0,0,v),(-1,0,0)),
        ((0,-v,0),(0,0,u),(-1,0,0)), ((0,1,0),(0,0,-1),(-1,0,0)),
        ((0,0,1),(-1,0,0),(0,-1,0)), ((0,0,1),(v,0,0),(0,u,0)),
        ((0,0,1),(u,0,0),(0,v,0)), ((0,0,v),(0,-u,0),(1,0,0)),
        ((0,0,v),(0,-v,0),(-v,0,0)), ((0,0,u),(0,-v,0),(1,0,0)))


def coefficient_control():
    # Every tensor coefficient, in Z[u]/(u^2-u+1), not random evaluations.
    f0, f1 = matrices(0), matrices(1)
    coeff = [[[(f0[t][r][i], f1[t][r][i]-f0[t][r][i]) for i in range(3)]
              for r in range(3)] for t in range(18)]
    def mul(x, y):
        a,b=x; c,d=y
        return a*c-b*d, a*d+b*c+b*d
    signs = dict(zip(PERMS, SIGNS))
    changed = 0
    for rr in product(range(3), repeat=3):
        for ii in product(range(3), repeat=3):
            summands = [mul(mul(c[rr[0]][ii[0]], c[rr[1]][ii[1]]),c[rr[2]][ii[2]]) for c in coeff]
            actual = tuple(sum(v[k] for v in summands) for k in range(2))
            expected = (3*signs.get(rr,0)*signs.get(ii,0), 0)
            require(actual == expected, "eighteen exact tensor coefficient")
            changed += actual != (2*signs.get(rr,0)*signs.get(ii,0),0)
    require(changed > 0, "wrong multiplier negative control")
    return {"ring": "Z[u]/(u^2-u+1)", "coefficients_checked": 729,
            "wrong_multiplier_rejected_coefficients": changed}


def pair_values(field, a, b, u):
    values=[]
    for form in matrices(u):
        cols=[]
        for j in range(3):
            z=field.zero
            for r,i in product(range(3),repeat=2):
                if form[r][i]:
                    z=field.add(z,field.scale(field.mul(a[r][j],b[i][j]),form[r][i]))
            cols.append(z)
        values.append(cols)
    return values


def finite_controls():
    rng=Random(191186)
    pair_checks=wrong_root=wrong_scale=nonsymmetric=0
    for p in (3,7,13,19,37,103):
        roots=[u for u in range(p) if (u*u-u+1)%p==0]
        require(bool(roots), "control root")
        for u in roots:
            for _ in range(12):
                a=[[rng.randrange(p) for _ in range(3)] for _ in range(3)]
                b=[[rng.randrange(p) for _ in range(3)] for _ in range(3)]
                def vals(root):
                    return [[sum(f[r][i]*a[r][j]*b[i][j] for r,i in product(range(3),repeat=2))%p
                             for j in range(3)] for f in matrices(root)]
                v=vals(u)
                expected=3*determinant(a,p)*determinant(b,p)%p
                require(sum(prod(x) for x in v)%p==expected, "finite eighteen identity")
                wrong_root += sum(prod(x) for x in vals(0))%p != expected
                nonsymmetric += sum(v[t][0]*v[t][1]*v[(t+1)%18][2] for t in range(18))%p != expected
                pair_checks+=1
    reports=[]
    fixtures=[(7,[1,1,0,1]), (13,[4,10,3,10,2,1]),
              (37,[28,20,13,17,11,35,25,12,1,28,30,26,10,1])]
    for p,modulus in fixtures:
        field=Field(p,modulus)
        require(field.irreducible(), "eighteen fixture irreducible")
        u=next(u for u in range(p) if (u*u-u+1)%p==0)
        m=(field.d-1)//2
        nodes=interpolation_elements(field,2*field.d-1)
        patterns=list(product(range(18),repeat=m)) if m<=2 else [
            (i,)*m for i in range(18)]+[tuple(rng.randrange(18) for _ in range(m)) for _ in range(8)]
        enumerated=descents=0
        for _ in range(2):
            matrix=[[tuple(rng.randrange(p) for _ in range(field.d)) for _ in range(3)] for _ in range(3)]
            conj=conjugate_matrices(field,matrix)
            paired=[pair_values(field,conj[2*v+1],conj[2*v+2],u) for v in range(m)]
            expected=field.power(field.determinant(matrix),(p**field.d-1)//(p-1))
            factored=field.determinant(conj[0])
            for vals in paired:
                subtotal=field.zero
                for v in vals:
                    subtotal=field.add(subtotal,field.mul(field.mul(v[0],v[1]),v[2]))
                factored=field.mul(factored,subtotal)
            require(factored==field.scale(expected,3**m), "eighteen factorized norm")
            total=field.zero
            for index,pattern in enumerate(patterns):
                a=combined(field,conj[0],paired,pattern)
                v=field.determinant(a)
                total=field.add(total,v)
                if index<12:
                    require(bilinear_descent(field,a,nodes)==v[0], "eighteen descent")
                    descents+=1
            if m<=2:
                require(total==field.scale(expected,3**m), "eighteen enumerated norm")
                require(field.scale(total,pow(3**m,-1,p))==expected, "eighteen normalization")
                wrong_scale += total != expected
                enumerated+=1
        reports.append({"p":p,"degree":field.d,"root":u,"modulus_low_degree_first":modulus,
            "patterns_per_matrix":len(patterns),"full_enumeration":m<=2,
            "full_norm_checks":enumerated,"factorized_norm_checks":2,"descent_checks":descents})
    absent=[p for p in (5,11,17,41) if not any((u*u-u+1)%p==0 for u in range(p))]
    require(len(absent)==4 and min(wrong_root,wrong_scale,nonsymmetric)>0, "eighteen negative controls")
    return {"pair_checks":pair_checks,"fields":reports,"negative_controls":{
        "invalid_root":wrong_root,"missing_normalization":wrong_scale,
        "different_form_in_third_column":nonsymmetric,"primes_without_required_root":absent},
        "scope":"finite controls supplement universal Lean proofs; degree 13 uses factorization and sampled terms"}


def exact_rows():
    rows=[[1]]
    for a in [4]*7+[5]*4:
        new=[0]*(len(rows[-1])+a*(a-1)//2)
        for e,c in enumerate(rows[-1]):
            for d in range(2*a):
                r=abs(2*d-(2*a-1))//2
                new[e+r*(r+1)//2]+=c
        rows.append(new)
    return rows


def multinomial_count():
    @lru_cache(None)
    def ways(a,r,left,e):
        if r==a:
            return int(left==0 and e==0)
        t=r*(r+1)//2
        return sum(comb(left,n)*ways(a,r+1,left-n,e-n*t) for n in range(left+1) if n*t<=e)
    return 2**11*sum(ways(4,0,7,e)*ways(5,0,4,32-e) for e in range(33))


def packing_controls():
    count=exact_rows()[11][32]
    require(count==multinomial_count()==872130560,"eighteen independent layer coefficient")
    return {"full_distribution_coefficient":str(count),"multinomial_coefficient":str(multinomial_count())}


if __name__=="__main__":
    import json
    print(json.dumps({"coefficients":coefficient_control(),"finite":finite_controls(),"packing":packing_controls()},indent=2))
