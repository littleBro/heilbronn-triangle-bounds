"""Independent finite controls for the tagged degree-five argument.

These enumerate specified finite fixtures, not the general probability theorem.
"""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import comb
from random import Random

from bilinear_controls import bilinear_descent, interpolation_elements
from eighteen_controls import pair_values
from frobenius_controls import conjugate_matrices
from norm_controls import Field
from paired_controls import combined
from search_packing import distribution
from verify import require


def packing_rows():
    return [[distribution(tuple((n,1) for n in [2]*min(i,5)+[4]*max(0,i-5)))[2*e]
             if 2*e < len(distribution(tuple((n,1) for n in [2]*min(i,5)+[4]*max(0,i-5))))
             else 0 for e in range(3)] for i in range(10)]


def det(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
           -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
           +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def packing_controls():
    require(packing_rows()[-1][2] == 2**9*comb(4,2) == 3072,"binomial layer")
    # A complete small support test including all tags and all norm positions.
    u, K0, d = [0,1,3], 7, 2
    shift = (K0-1)//2+d
    v = [K0-1-2*x for x in u]
    target = K0-1+2*shift
    triples = tagged = 0
    for i,j,h in product(range(3),repeat=3):
        require((u[i]+shift+u[j]+shift+v[h] == target) == (i==j==h),"shifted matching")
        triples += 1
    for t,i,l in product(range(d),range(shift+(K0-1)//2+1),range(K0)):
        require(t+i+l < target,"tag support separation")
        tagged += 1
    rng = Random(191501)
    wrong_shift = 0
    for _ in range(32):
        forms = [[[rng.randrange(7) for _ in range(3)] for _ in range(3)] for _ in range(3)]
        tags = [[rng.randrange(7) for _ in range(d)] for _ in range(3)]
        expected = sum(det(a) for a in forms) % 7
        for offset in (shift,0):
            goal = K0-1+2*offset
            polynomials = [[{} for _ in range(3)] for _ in range(3)]
            for row,col,a in product(range(3),repeat=3):
                pos = (u[a]+offset if row<2 else v[a])
                polynomials[row][col][pos] = forms[a][row][col]
            for col in range(3):
                polynomials[0][col][0] = polynomials[0][col].get(0,0)+1
                for t in range(d):
                    polynomials[1][col][t] = polynomials[1][col].get(t,0)+tags[col][t]
            actual = 0
            for perm in permutations(range(3)):
                sign = (-1)**sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
                for x,y,z in product(*(polynomials[row][perm[row]].items() for row in range(3))):
                    if x[0]+y[0]+z[0] == goal:
                        actual += sign*x[1]*y[1]*z[1]
            if offset:
                require(actual % 7 == expected,"tagged determinant coefficient")
            else:
                wrong_shift += actual % 7 != expected
    require(wrong_shift > 0,"unshifted tags corrupt coefficient")
    return {"table_entries":30,"binomial_count":3072,"small_matching_triples":triples,
            "small_tag_separation_cases":tagged,"sampled_coefficient_identities":32,
            "unshifted_tag_counterexamples":wrong_shift}


def tagged_case(k, labels, B=5003, choices=2):
    r,d = 2,2
    # Every residue uses its positive representative; low tags are arbitrary labels.
    top = [[1]+[r]*(k-1) for _ in range(3)]
    middle = [[x or r for x in label]+[r]*max(0,k-d) for label in labels]
    middle = [x[:k] for x in middle]
    options = []
    for _label in labels:
        # Prescribe zero in row three, so the positive Schur tails are exercised.
        sets = [tuple(r*(t+1) for t in range(choices)) for _ in range(k)]
        options.append(list(product(*sets)))
    powB = [B**i for i in range(k)]
    cv = lambda word: sum(x*p for x,p in zip(word,powB))
    top_n = [cv(x) for x in top]
    mid_n = [cv(x) for x in middle]
    same = next((i,j) for i in range(3) for j in range(i+1,3) if labels[i]==labels[j])
    other = next(i for i in range(3) if i not in same)
    a = next((i for i in range(d) if labels[same[0]][i]!=labels[other][i]),None)
    counts = Counter()
    for bottom in product(*options):
        c = [top_n,mid_n,[cv(x) for x in bottom]]
        minors = [c[0][0]*c[i][j]-c[i][0]*c[0][j] for i in (1,2) for j in (1,2)]
        b=0
        for j in range(1,k+1):
            if all(x % (B**j)==0 for x in minors):
                b=j
        value = det(c) % (B**k)
        small = min(value,B**k-value) <= B**(k-1)//2
        # Independent coefficient calculation, with no modular arithmetic.
        coefficient = 0
        for i in range(k):
            for j in range(k-i):
                v = k-1-i-j
                coefficient += det([[top[col][i] for col in range(3)],
                                    [middle[col][j] for col in range(3)],
                                    [bottom[col][v] for col in range(3)]])
        require(not small or coefficient==0,"small residue forces zero high coefficient")
        counts['total'] += 1
        counts['moment'] += B**b
        if small:
            counts['small'] += 1
            counts['weighted'] += B**b
            for j in range(1,k+1):
                if b>=j: counts[j] += 1
        if a is not None and a<k:
            require(b<=a,"tag bounds minor valuation")
    return a,counts


def collision_controls():
    labels=list(product(range(2),repeat=2))
    total=groups=tails=0
    for x,y in permutations(labels,2):
        for triple in ((x,x,y),(x,y,x),(y,x,x)):
            a,c=tagged_case(4,triple)
            n=c['total']; M=2; B=5003
            require(Fraction(c['small'],n)<=Fraction(1,M),"fresh digit")
            for j in range(1,a+1):
                require(Fraction(c[j],n)<=Fraction(1,M**(2*j+1)),"joint tail")
                tails+=1
            bound=Fraction(1,M)*(1+sum(Fraction(B,M*M)**j for j in range(1,a+1)))
            require(Fraction(c['weighted'],n)<=bound,"weighted truncated moment")
            groups+=1; total+=n
    # No fresh digit: a=1, k=2 makes v=0, already inside the Schur prefix.
    a,c=tagged_case(2,((0,0),(0,0),(0,1)))
    require(a==1 and Fraction(c[1],c['total'])>Fraction(1,2**3),"freshness omission rejected")
    # Omitting the distinguishing tag can make different labels have identical top rows.
    _,untagged=tagged_case(2,((0,0),(0,0),(0,0)),choices=3)
    require(untagged['small']==untagged['total'] and
            Fraction(untagged['weighted'],untagged['total'])>Fraction(2,3),"missing tag rejected")
    return {"r":2,"tag_dimension":2,"k":4,"prime_base":5003,"digit_choices":2,
            "complete_label_groups":groups,"matrices_enumerated":total,
            "joint_tail_inequalities":tails,"weighted_moment_inequalities":groups,
            "no_fresh_digit_counterexample":{"k":2,"a":1,"joint_probability":str(Fraction(c[1],c['total'])),"incorrect_bound":"1/8"},
            "no_distinguishing_tag_rejected":True,
            "scope":"complete finite digit distributions at the displayed parameters; general theorem remains written"}


def field_controls():
    p=37
    modulus=[2,1,0,0,0,1]
    field=Field(p,modulus)
    # Find and then record the first irreducible x^5+x+c fixture deterministically.
    for c in range(1,p):
        modulus=[c,1,0,0,0,1]; field=Field(p,modulus)
        if field.irreducible(): break
    require(field.irreducible(),"degree-five fixture")
    rng=Random(191503)
    u=next(a for a in range(p) if (a*a-a+1)%p==0)
    nodes=interpolation_elements(field,9)
    descents=wrong=matrices=0
    for _ in range(2):
        matrix=[[tuple(rng.randrange(p) for _ in range(5)) for _ in range(3)] for _ in range(3)]
        conjugates=conjugate_matrices(field,matrix)
        pairs=[pair_values(field,conjugates[2*v+1],conjugates[2*v+2],u) for v in range(2)]
        expected=field.power(field.determinant(matrix),(p**5-1)//(p-1))
        total=field.zero
        for index,pattern in enumerate(product(range(18),repeat=2)):
            a=combined(field,conjugates[0],pairs,pattern)
            determinant=field.determinant(a)
            total=field.add(total,determinant)
            if index<16:
                require(bilinear_descent(field,a,nodes)==determinant[0],"nine-node descent")
                wrong+=bilinear_descent(field,a,nodes[:-1])!=determinant[0]
                descents+=1
        require(total==field.scale(expected,9),"complete degree-five norm expansion")
        require(total!=expected,"normalization omission rejected")
        matrices+=1
    require(wrong>0,"omitted interpolation node rejected")
    return {"prime":p,"degree":5,"modulus_low_degree_first":modulus,"root":u,
            "matrices_fully_enumerated":matrices,"patterns_per_matrix":324,
            "sampled_nine_node_descents":descents,"omitted_node_counterexamples":wrong,
            "omitted_normalization_rejected":True}


if __name__ == "__main__":
    import json
    print(json.dumps({"packing":packing_controls(),"collisions":collision_controls(),"field":field_controls()},indent=2))
