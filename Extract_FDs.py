'''
X->Y
X is determining set, Y is dependent variable
What to do:
For each attribute in attrubute_set:
    1. Finding hyper-graph of maximal refutations(H) for attribute using recursive calls
    and, dictionary on each step for linear worst case time & space complexity on each node
    2. Finding compliment hyper-graph(H'), where each of maximal refutation is complimented
    3. Finding slices(H'), each of element is RHS(determining set) for current attribute

Worst Case Time Complexity of Algorithm is T*N*(2**N-1)
T is Number of Tuples is Relation
N is number of Attributes in relation

This algorithm is scalable in term of checking any refutation with multiple number of cores
So, overall parallel time complexity will be divided by K (Number of Processing units used)

'''

import itertools
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import time,sys

def cartesian_product(A,B):
    "A ∨ B = {E[i] ∪ E[j] |1 ≤ i ≤ n(A), 1 ≤ j ≤ n(A)}"
    return {a|b for a in A for b in B}

def minimization(A):
    "μ(H) = {X ∈ E; ¬∃Y ∈ E, Y ⊆ X}" #It is Proper-Subset operation
    return  { a for a in A if not any(x<a for x in A)}

def clutter(A):
    "ν(H) = {X|X ⊆ A; ∃Y ∈ E, Y ⊆ X}"
    return { frozenset(x)|a for a in A for ln in range(len(sym)-len(a)+1) for x in itertools.combinations(sym-a,ln)}

def inverse_clutter(A):
    "v'(H) = {X|X ⊆ A; ∃Y ∈ E, Y ⊃ X}"
    return { frozenset(x) for a in A for ln in range(len(a)+1) for x in itertools.combinations(a,ln)}

def blocker(A):
    "τ(H) = {X ⊆ A; ∀Y ∈ E,X ∩ Y != ∅}"
    return { frozenset(x) for ln in range(len(sym)+1) for x in itertools.combinations(sym,ln) if all(frozenset(x)&a for a in A)}

def slices(A):
    "λ(H) = μ(τ(H))"
    return minimization(blocker(A))

def valid_refutation(S,D):
    "Checks if S->D is refuted on available instance or not"
    tmp = {}
    for tup in df.itertuples():
        key = tuple(tup[x] for x in S)
        if key in tmp:
            tmp[key].add(tup[D])
            if len(tmp[key])>1:
                return True
        else:
            tmp[key] = { tup[D] }
    return False

def dfs_recursive(S,D):
    'S is determining set, D is dependent variable'
    if valid_refutation(S,D):
        dct[D].add(S)
    else:
        if len(S)>1:
            for x in S:
                dfs_recursive(S-{x},D)    

def bfs_recursive_1(S,D):
    'S is determining set, D is dependent variable'
    global queue
    if any(S<x for x in dct[D]):
        return
    if valid_refutation(S,D):
        dct[D].add(S)
    else:
        if len(S)>1:
            for x in S:
                queue.append( (S-{x},D) )

def run_recursive_1(S,D):
    'This function processes queue, for BFS traversal of search space'
    global queue
    queue = [(S,D)]
    while queue:
        s,d = queue.pop(0)
        bfs_recursive(s,d)

def bfs_recursive_2(S,D,Q):
    'S is determining set, D is dependent variable'
    global RC_T,RC_A
    RC_T+=1
    if any(S<x for x in dct[D]):
        return
    RC_A+=1
    if valid_refutation(S,D):
        dct[D].add(S)
    else:
        if len(S)>1:
            for x in S:
                Q.add( S-{x} )

def run_recursive_2(S,D):
    'This function processes queue, for BFS traversal of search space'
    global queue
    queue = {0:{S}}
    while queue:
        level = min(queue)
        value = queue[level]
        del queue[level]
        if not value:
            break
        #print(D,len(value),value)
        queue[level+1] = set()
        for s in value:
            bfs_recursive_2(s,D,queue[level+1])

def out(file_name=None):
    "Function to produce output on Console or File for Anu"
    ext_sym = set()
    for L in FDs:
        ext_sym.update({x for x in L})
        ext_sym.update({x for x in FDs[L]})
    ext_sym = sym - ext_sym

    if file_name:
        f1 = open(file_name,'w')
        bckout = sys.stdout if sys.stdout else sys.__stdout__
        sys.stdout = sys.__stdout__ = f1
        for L in FDs:
            print( ({lkup_1[x] for x in L},{lkup_1[x] for x in FDs[L]}) )
        if ext_sym:
            print('\n'+'{'+','.join(lkup_1[x] for x in ext_sym)+'}')
        else:
            print('\n')
        f1.close()
        sys.stdout = sys.__stdout__ = bckout
        
    else:
        print('\nExtracted FDs are')
        for L in FDs:
            print(','.join(lkup_1[x] for x in L),end=' -> ')
            print(','.join(lkup_1[x] for x in FDs[L]))
        if ext_sym:
            print('\nExtended Symbol Set')
            print('{'+','.join(lkup_1[x] for x in ext_sym)+'}')


sym,queue,df,names,lkup_1,lkup_2,sym,dct,FDs,RC = None,None,None,None,None,None,None,None,None,None

def main(file_name):
    global sym,queue,df,names,lkup_1,lkup_2,sym,dct,FDs,RC_T,RC_A

    sym,queue,RC_T,RC_A = None,None,0,0
    #input('Enter path of CSV file\n')
    df = pd.read_csv(file_name)
    names = df.columns.values
    lkup_1 = { i+1:names[i] for i in range(len(names)) }
    lkup_2 = { names[i]:i+1 for i in range(len(names)) }
    sym = set(lkup_1)

    # Dictionary containing determining set for each of dependent attribute as key
    dct,FDs = {},{}

    init = time.clock()

    for dependent_attribute in sym:
        dct[dependent_attribute],FDs[dependent_attribute] = set(),set()
        
        run_recursive_2( frozenset(sym)-{dependent_attribute} , dependent_attribute )

        #print(dependent_attribute,len(dct[dependent_attribute]),sum(len(x) for x in dct[dependent_attribute]))

        #Eliminating all subsets
        dct[dependent_attribute] = {ele for ele in dct[dependent_attribute] if not any(ele<x for x in dct[dependent_attribute])}

        #Finding complement of hyper-edges
        dct[dependent_attribute] = { ( frozenset(sym)-(ele|{dependent_attribute}) ) for ele in dct[dependent_attribute] }

        #Finding Slices
        dct[dependent_attribute] = slices( dct[dependent_attribute] )

    #Dictionary containing X->Y final FDs
    FDs = {}
    for Y in dct:
        for X in dct[Y]:
            if X in FDs:
                FDs[X].add(Y)
            else:
                FDs[X] = {Y}

    #out()
    return (time.clock()-init,RC_A)

def worst(n,t):
    file_name = str(n)+'x'+str(t)+'.csv'
    f = open(file_name,'w')
    st = ','.join(str(x) for x in range(n)) + '\n'
    for i in range(t+1):
        _ = f.write(st)
    f.close()
    return main(file_name)

def test(a,b,d1,d2):
    ls = {}
    for n in range(a,b+1):
        ls[n] = []
        for t in range(d1,d2+1):
            t = 10**t
            #print(n,t,end=' ')
            ls[n].append( worst(n,t) )
        print(ls[n])
    df = pd.DataFrame({(key,ls[key][0][1]):[round(x[0],3) for x in ls[key]] for key in ls})
    return df



'''
X = [1,2,3,4,5,6,7,8,9,10,11,12]
RC_DFS = [1,2,9,40,205,1236,8659]
RC_BFS = []
RC_T_ADV = [1,2,9,28,75,186,441,1016,2295,5110,11253,24564]
'''
