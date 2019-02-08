'''
This Project is Aimed to Perform Basic & Advanced DB Decomposition related
Operation, which will be based upon concept of functional dependencies

Order will be like This:
1. Input collection of FDs
2. Finding Minimal Cover of Input FDs
3. Finding Candidate Keys for any Relation,
    based on applicable FDs from Entire FD set
4. Input Of Schema of Relations Designed Initially
5. Calling Of Functions to perform decomposition towards higher normal forms

Useful_statements_to_copy_and_execute:
    FDs = minimal_cover(FDs)
    print_FDs(FDs)
    print_keys(  candidate_keys(  set(lkup_1.keys())  )[0]  )
    print_schema(  NF_2 (  frozenset(lkup_1.keys())  )  )
    print_schema(  NF_3 (  frozenset(lkup_1.keys())  )  )
    print_schema(  NF_BC(  frozenset(lkup_1.keys())  )  )

Data-Structures
FDs: it is a SET containing 2-tuples, in which each element is a FROZEN-SET of elements
SCHEMA: it is SET type, containing each relation as FROZEN-SET
D_FLAG: dictionary which keeps whether a Relation is to be tested for Decomposition or not

Note: SCHEMA & D_FLAG do have equal number of entries, even relation of SCHEMA is Key to D_FLAG dictionary
'''

import time,sys,os,itertools

FDs    = None # SET CONTAINING ALL FDs
sym    = None # SET CONTAINING ALL SYMBOLS, (Tokens when extended), can be used as Global Schema also
lkup_1 = None # INTEGER TO ATTRIBUTE NAME MAPPING
lkup_2 = None # ATTRIBUTE NAME TO INTEGER MAPPING
OUTPUT_STREAMS = None #Global variable containing active output streams
COST,init = None,None #Time taken & clock checkpoints, excluding waiting for choice during BCNF
# Global Schema References, will be updated during recursive calls
SCHEMA,SCHEMA_2NF,SCHEMA_3NF,SCHEMA_BCNF = None,None,None,None

def fetch_input(FLAG):
    global FDs,sym,lkup_1,lkup_2
    FDs,sym,lkup_1,lkup_2 = set(),set(),{},{}
    if not FLAG:
        print('Enter all FDs')
    while True:    
        ip = input()
        #Break if these is no input
        if not ip:
            break
        #Most standard way to take input in terms of Attribute names
        if ip.startswith('(') and ip.endswith(')'):
            tmp = eval(ip)
            if set(type(x) for x in tmp)=={tuple}:
                #Multiple Tuples are there is a line
                for L,R in tmp:
                    #Each of LHS or RHS can be string or iterable containing attributes as string
                    L = frozenset({L}) if type(L)==str else frozenset(L)
                    R = frozenset({R}) if type(R)==str else frozenset(R)
                    FDs.add( (L,R) )
                    sym.update( L | R )
            else:
                #Single tuple in a line
                L,R = tmp
                #Each of LHS or RHS can be string or iterable containing attributes as string
                L = frozenset({L}) if type(L)==str else frozenset(L)
                R = frozenset({R}) if type(R)==str else frozenset(R)
                FDs.add( (L,R) )
                sym.update( L | R )


        #Taking Input of all FDs in single line
        elif ip.startswith('{') and ip.endswith('}'):
            tmp = ip.strip('{}').split(',')
            for ip in tmp:
                ip = ip.split('->')
                L, R = ip[0].strip(), ip[1].strip()
                FDs.add( (frozenset(L),frozenset(R)) )
                sym.update( set(L) | set(R) )
        #Taking Input of one FD in a line
        else:
            ip = ip.split('->')
            L, R = ip[0].strip(), ip[1].strip()
            FDs.add( (frozenset(L),frozenset(R)) )
            sym.update( set(L) | set(R) )
    if not FLAG:
        ip = input('Enter Extended Attribute Set\n')
    else:
        ip = input()
    if ip:
        sym.update({x for x in ip.strip('{}').split(',')})
        
    for i,j in enumerate(sorted(sym)):
        lkup_1[i] = j
        lkup_2[j] = i

    FDs = { (frozenset(lkup_2[i] for i in l), frozenset(lkup_2[i] for i in r)) for l,r in FDs }

def print_FDs(FDs):
    'Function to print FDs sorted by attributes in Lexicographical order'
    for l,r in sorted(FDs,key=lambda FD:(sorted(lkup_1[i] for i in FD[0]),sorted(lkup_1[i] for i in FD[0]))):
        my_print( ','.join(sorted(lkup_1[i] for i in l)),my_end=' -> ')
        my_print( ','.join(sorted(lkup_1[i] for i in r)))

def print_keys(KEYS):
    'Function to print keys sorted by attributes in Lexicographical order'
    my_print( tuple( sorted(lkup_1[i] for i in entry) for entry in sorted(KEYS,key = lambda x:''.join(lkup_1[j] for j in sorted(x))) ) , my_sep=' , ' )

def print_rltn(RLTN):
    'Function to print relation sorted by attributes in Lexicographical order'
    my_print( sorted(lkup_1[i] for i in RLTN) , my_end='' )

def print_schema(SCHEMA):
    'Function to print schema sorted by attributes in Lexicographical order'
    my_print( tuple( sorted(lkup_1[i] for i in rltn) for rltn in sorted(SCHEMA,key = lambda x:''.join(lkup_1[j] for j in sorted(x))) ) , my_sep=' , ' )
    
def applicable_FDs(FDs,RLTN):
    'Function to find applicable set of FDs on a relation'
    tmp_FDs = set() # FDs applicable for current relation must be extracted
    for l,r in FDs:
        if l <= RLTN:
            tmp_FDs.add( (l,frozenset(i for i in r if i in RLTN)) )
    return minimal_cover(tmp_FDs)

def closure(x,FDs): # x must be SET Datatype always
    'Set whose closure is to be computed must be passed'
    while True:
        tmp = x.copy()
        for l,r in FDs:
            if l <= x:
                x.update(r)
        if tmp == x:
            break
    return x

def covering(L_FDs,R_FDs):
    'This Function Checks if L_FDs is a cover of R_FDs'
    for l,r in R_FDs:
        if not r <= closure(set(l),L_FDs):
            return False
    return True

def closure_FDs(FDs):
    'Function find out closure of each LHS of FD set, not closure of FD set'
    tmp_FDs = set()
    for l,r in FDs:
        tmp_FDs.add( (l, frozenset(closure(set(r),FDs))) )
    return tmp_FDs

def minimal_cover(FDs):
    # STEP1 of FINDING MINIMAL COVER
    'Decomposing Each of RHS, into Single Element'
    tmp = set()
    for l,r in FDs:
        for i in r:
            tmp.add( (l,frozenset({i})) )
    FDs = tmp

    # STEP2 of FINDING MINIMAL COVER
    'Checking if any FD is redundant'
    while True:
        tmp = FDs.copy()
        for i in FDs:
            prev = closure(set(i[0]),tmp)
            tmp.remove(i)
            new  = closure(set(i[0]),tmp)
            if new < prev:
                tmp.add( i )
        if tmp == FDs:
            break
        else:
            FDs = tmp

    # STEP3 of FINDING MINIMAL COVER
    'Checking if any term on LHS is Redundant'
    while True:
        tmp = FDs.copy()
        for i in FDs:   
            for j in i[0]:
                tmp.remove(i)
                if j not in closure(set(i[0]-{j}),tmp):
                    tmp.add(i)
                else:
                    i = (i[0]-{j},i[1])
                    tmp.add( (i[0]-{j},i[1]) )
        if tmp == FDs:
            break
        else:
            FDs = tmp

    # OPTIONAL RE-COMBINATION STEP (will decrease number of FDs)
    'FDs having LHS Same, then RHS can be merged using UNION rule (A->B & A->C) <==> (A->BC)'
    tmp = {}
    for l,r in FDs:
        if l in tmp:
            tmp[l].update(r)
        else:
            tmp[l] = set(r)
    FDs = { (i,frozenset(tmp[i])) for i in tmp }
    return FDs

def candidate_keys(RLTN):
    'Attribute set of Relation, for finding Candidate keys be passed'
    keys = set()       # This set will be returned conating all candidate keys
    tmp_FDs = applicable_FDs(FDs,RLTN)
    # Attributes which are essential to be in each candidate key
    non_ess = set( i for l,r in tmp_FDs for i in r )
    ess = RLTN - non_ess

    for i in range(len(non_ess)+1):
        for j in itertools.combinations(non_ess,i):
            val = ess|set(j)
            if closure(set(val),tmp_FDs) == RLTN:
                if not any( k<val for k in keys ):
                    keys.add(frozenset(val))

    prime_attr = set()
    for i in keys:
        prime_attr.update(i)
        
    return keys , prime_attr , RLTN-prime_attr

def merge_schema(SCHEMA):
    'Checks if any relation is subset of other in schema, delete the sub-relation from schema'
    tmp_schema = SCHEMA.copy()
    while True:
        tmp = set()
        for i in SCHEMA:
            if any(i<rltn for rltn in SCHEMA):
                tmp.add(i)
        SCHEMA.difference_update(tmp)
        if tmp_schema == SCHEMA:
            break
        else:
            SCHEMA = tmp_schema
    return SCHEMA

def is_lossless(SCHEMA):
    'Checks if the schema is a loss-less join decomposition'
    #It should be a binary operator
    tmp = { x for rltn in SCHEMA for x in rltn }
    for rltn in SCHEMA:
        tmp.intersection_update(rltn)
    keys = { key for rltn in SCHEMA for key in candidate_keys(rltn)[0] }
    #if Intersecting elements do form a superkey of any sub-relation
    return any( tmp>=key for key in keys)

def NF_2(RLTN):
    'There should not be any partial dependency'
    global SCHEMA,SCHEMA_2NF
    SCHEMA = { RLTN }
    D_FLAG = { x:True for x in SCHEMA }
    SCHEMA_2NF = SCHEMA.copy()
    while True:
        for rltn in SCHEMA_2NF.copy():
            if D_FLAG[rltn]:
                decompose,pull = set(),set()
                keys,prime,non_prime = candidate_keys(rltn)
                tmp_FDs = applicable_FDs(FDs,rltn)
                for l,r in tmp_FDs:
                    if not (l <= pull):
                        # CONDITION FOR 2NF
                        if any(l<i for i in keys) and r&non_prime:
                            tmp = set( r&non_prime )
                            while True:
                                tmp2 = tmp.copy()
                                for i,j in tmp_FDs:
                                    if i <= tmp:
                                        tmp.update(j-l)
                                if tmp == tmp2:
                                    break
                                else:
                                    tmp2 = tmp
                            decompose.add( (l,frozenset(tmp)) )
                            pull.update( tmp )
                tmp = set()
                for l,r in decompose:
                    tmp.update(r)
                    
                leftover = frozenset(rltn-tmp)
                res = merge_schema( {leftover} | {l|r for l,r in decompose} )
                consistent_FDs_flag,inconsistent_set = True,set()
                while True:
                    res_2 = res.copy()
                    for tmp_rltn in res_2:
                        if not is_lossless({leftover,tmp_rltn}):
                            consistent_FDs_flag = False
                            inconsistent_set.update( {(l,r) for l,r in tmp_FDs if (l|r)<=tmp_rltn} )
                            res.remove( leftover )
                            res.remove( tmp_rltn )
                            leftover = leftover|tmp_rltn
                            res.add( leftover )
                    res = merge_schema( res )
                    if res == merge_schema( res_2 ):
                        break
                if inconsistent_set:
                    my_print('\nSet of FDs inconsistent for 2NF decomposition')
                    print_FDs(inconsistent_set)
                for tmp_rltn in res:
                    if not is_lossless({leftover,tmp_rltn}):
                        my_print('Loss-Less 2NF Decomposition not possible')
                        res = { rltn }
                        break
                if res == { rltn }:
                    D_FLAG[rltn] = False
                else:
                    SCHEMA_2NF.remove( rltn )
                    del D_FLAG[rltn]
                    SCHEMA_2NF.update( res )
                    for tmp_rltn in res:
                        D_FLAG[tmp_rltn] = True
        if not any(D_FLAG[rltn] for rltn in D_FLAG):
            break
    SCHEMA_2NF = merge_schema( SCHEMA_2NF )
    return SCHEMA_2NF

def NF_3(RLTN):
    'LHS must be Super Key OR RHS be Prime attribute'
    global SCHEMA_3NF
    SCHEMA_2NF = NF_2(RLTN)
    D_FLAG = { x:True for x in SCHEMA_2NF }
    SCHEMA_3NF = SCHEMA_2NF.copy()
    while True:
        for rltn in SCHEMA_3NF.copy():
            if D_FLAG[rltn]:
                decompose,pull = set(),set()
                keys,prime,non_prime = candidate_keys(rltn)
                tmp_FDs = applicable_FDs(FDs,rltn)
                for l,r in tmp_FDs:
                    if not (l <= pull):
                        # CONDITION FOR 3NF
                        if not any(i<=l for i in keys) and r&non_prime:
                            tmp = set( r&non_prime )
                            while True:
                                tmp2 = tmp.copy()
                                for i,j in tmp_FDs:
                                    if i <= tmp:
                                        tmp.update(j-l)
                                if tmp == tmp2:
                                    break
                                else:
                                    tmp2 = tmp
                            decompose.add( (l,frozenset(tmp)) )
                            pull.update( tmp )
                tmp = set()
                for l,r in decompose:
                    tmp.update(r)
                leftover = frozenset(rltn-tmp)
                res = merge_schema( {leftover} | {l|r for l,r in decompose} )
                consistent_FDs_flag,inconsistent_set = True,set()
                while True:
                    res_2 = res.copy()
                    for tmp_rltn in res_2:
                        if not is_lossless({leftover,tmp_rltn}):
                            consistent_FDs_flag = False
                            inconsistent_set.update( {(l,r) for l,r in tmp_FDs if (l|r)<=tmp_rltn} )
                            res.remove( leftover )
                            res.remove( tmp_rltn )
                            leftover = leftover|tmp_rltn
                            res.add( leftover )
                    res = merge_schema( res )
                    if res == merge_schema( res_2 ):
                        break
                if inconsistent_set:
                    my_print('\nSet of FDs inconsistent for 3NF decomposition')
                    print_FDs(inconsistent_set)
                for tmp_rltn in res:
                    if not is_lossless({leftover,tmp_rltn}):
                        my_print('Loss-Less 3NF Decomposition not possible')
                        res = { rltn }
                        break
                if res == { rltn }:
                    D_FLAG[rltn] = False
                else:
                    SCHEMA_3NF.remove( rltn )
                    del D_FLAG[rltn]
                    SCHEMA_3NF.update( res )
                    for tmp_rltn in res:
                        D_FLAG[tmp_rltn] = True
        if not any(D_FLAG[rltn] for rltn in D_FLAG):
            break
    SCHEMA_3NF = merge_schema( SCHEMA_3NF )
    return SCHEMA_3NF

def NF_BC(RLTN):
    '''LHS must be superkey'''
    global SCHEMA_BCNF,COST,init
    SCHEMA_3NF = NF_3(RLTN)
    D_FLAG = { x:True for x in SCHEMA_3NF }
    SCHEMA_BCNF = SCHEMA_3NF.copy()
    while True:
        for rltn in SCHEMA_BCNF.copy():
            if D_FLAG[rltn]:
                decompose,pull = set(),set()
                keys,prime,non_prime = candidate_keys(rltn)
                tmp_FDs = applicable_FDs(FDs,rltn)
                for l,r in tmp_FDs:
                    if not (l <= pull):
                        # CONDITION FOR BCNF
                        if not any(i<=l for i in keys):
                            tmp = set( r )
                            while True:
                                tmp2 = tmp.copy()
                                for i,j in tmp_FDs:
                                    if i <= tmp:
                                        tmp.update(j-l)
                                if tmp == tmp2:
                                    break
                                else:
                                    tmp2 = tmp
                            decompose.add( (l,frozenset(tmp)) )
                            pull.update( tmp )
                tmp = set()
                for l,r in decompose:
                    tmp.update(r)
                leftover = frozenset(rltn-tmp)
                res = merge_schema( {leftover} | {l|r for l,r in decompose} )
                consistent_FDs_flag,inconsistent_set = True,set()
                while True:
                    res_2 = res.copy()
                    for tmp_rltn in res_2:
                        if not is_lossless({leftover,tmp_rltn}):
                            consistent_FDs_flag = False
                            inconsistent_set.update( {(l,r) for l,r in tmp_FDs if (l|r)<=tmp_rltn} )
                            res.remove( leftover )
                            res.remove( tmp_rltn )
                            leftover = leftover|tmp_rltn
                            res.add( leftover )
                    res = merge_schema( res )
                    if res == merge_schema( res_2 ):
                        break
                if inconsistent_set:
                    my_print('\nSet of FDs inconsistent for BCNF decomposition')
                    print_FDs(inconsistent_set)
                for tmp_rltn in res:
                    if not is_lossless({leftover,tmp_rltn}):
                        my_print('Loss-Less BCNF Decomposition not possible')
                        res = { rltn }
                        break
                #Code-Block for checking FD Preserving & Giving choice
                rltn_2 = res
                tmp_FDs_2 = set()
                for i in rltn_2:
                    tmp_FDs_2.update( applicable_FDs(FDs,i) )
                if covering(tmp_FDs_2,tmp_FDs):
                    res = rltn_2
                else:
                    my_print('\nOn converting')
                    print_rltn(rltn)
                    my_print(' to',my_end=' ')
                    print_schema(rltn_2)
                    my_print('BCNF is not FD preserving, these FDs are violated')
                    print_FDs(tmp_FDs-tmp_FDs_2)
                    COST += time.clock()-init
                    if input('Press 1 for BCNF, (3NF is taken as default) : ')=='1':
                        res =  rltn_2
                    else:
                        res =  { rltn }
                    init = time.clock()
                if res == { rltn }:
                    D_FLAG[rltn] = False
                else:
                    SCHEMA_BCNF.remove( rltn )
                    del D_FLAG[rltn]
                    SCHEMA_BCNF.update( res )
                    for tmp_rltn in res:
                        D_FLAG[tmp_rltn] = True
        if not any(D_FLAG[rltn] for rltn in D_FLAG):
            break
    SCHEMA_BCNF = merge_schema( SCHEMA_BCNF )
    return SCHEMA_BCNF

def anu(FILE=None):
    global FDs,OUTPUT_STREAMS,COST,init
    if FILE:    #If a file to be processed is sent, use it, else use console I/O
        bckin  = sys.__stdin__  if sys.__stdin__  else sys.stdin
        bckout = sys.__stdout__ if sys.__stdout__ else sys.stdout
        sys.stdin  = sys.__stdin__ = open(FILE)
        sys.stdout = sys.__stdout__ = open(FILE[:FILE.index('.')]+'_NORM'+FILE[FILE.index('.'):],'w')
        # Org. streams into BACKUP,  connected to FILE STREAM
        OUTPUT_STREAMS = { sys.__stdout__  if sys.__stdout__  else sys.stdout }
        fetch_input(True)
        print('Attribute Set is')
        print_rltn(frozenset(lkup_1))
        print('\n\nInitial FDs are')
        print_FDs(FDs)
        print()
    else:
        OUTPUT_STREAMS = { sys.__stdout__  if sys.__stdout__  else sys.stdout }
        fetch_input(False)
    COST,init = 0,time.clock()
    FDs = minimal_cover(FDs)
    print(''' "Canonical Cover" of FDs set is''')
    print_FDs(FDs)
    print('''\n "Candidate Keys" of Universal Relation are''')
    print_keys(  candidate_keys(  set(lkup_1.keys())  )[0]  )
    if FILE:
        # Org. streams restored for console I/O during BCNF
        bckin, sys.__stdin__, sys.stdin  = sys.stdin, bckin, bckin
        bckout,sys.__stdout__,sys.stdout = sys.stdout,bckout,bckout
        OUTPUT_STREAMS.add(sys.stdout)
    NF_BC(  frozenset(lkup_1.keys())  )
    if FILE:
        OUTPUT_STREAMS.remove(sys.stdout)
        bckin, sys.__stdin__, sys.stdin  = sys.stdin, bckin, bckin
        bckout,sys.__stdout__,sys.stdout = sys.stdout,bckout,bckout
    print('''\n "2NF" Decomposition of Universal Relation is''')
    print_schema(  SCHEMA_2NF  )
    print('''\n 3NF Decomposition of Universal Relation is''')
    print_schema(  SCHEMA_3NF  )
    print('''\n "BCNF" Decomposition of Universal Relation is''')
    print_schema(  SCHEMA_BCNF  )
    if FILE:
        sys.stdout.close()
        bckin, sys.__stdin__, sys.stdin  = sys.stdin, bckin, bckin
        bckout,sys.__stdout__,sys.stdout = sys.stdout,bckout,bckout
    COST += time.clock()-init
    print(round(COST,6),'Seconds')

def anu_all(DIR=None):
    if DIR:
        os.chdir(DIR)
    for file in os.listdir():
        if file.endswith('anu') and ('NORM' not in file):
            print('Processing',file)
            anu(file)
    os.chdir('..')

def my_print(value,my_sep=' ',my_end='\n'):
    'Custom print function to send data to 2 output streams'
    for stream in OUTPUT_STREAMS:
        print(value,sep=my_sep,end=my_end,file=stream)

# REPL for Interaction
print('\n\t\tWelcome to ANU (A Modern Approach to RDBMS Normalization)')
while True:
    try:
        exec(input('>>> '))
    except Exception as des:
        print(des)

'''
Below are some examples taken from standard sources, to demonstrate various aspects of project

Example.1 with I/O format 1
Source: https://dba.stackexchange.com/questions/31039/decomposition-of-a-relation-to-2nf-then-to-3nf
Source: https://gateoverflow.in/4348/to-decompose-the-give-relation-into-3nf-and-bcnf
{ AB->C , F->GH , B->F , D->IJ , A->DE , BD->FI , AF->DG , DI->J } #Last 3 Redundant FDs intentionally added

    Obtained 2NF Schema by project, same as given on website
R0 = {A, B, C}
R1 = {A, D, E, I, J}
R2 = {B, F, G, H}

    Obtained 3NF Schema by project, same as given on website
R0  = {A, B, C}
R1a = {A, D, E}
R1b = {D, I, J}
R2a = {B, F}
R2b = {F, G, H}


Example.2 with I/O format 2
Source: https://stackoverflow.com/questions/23681453/finding-a-relation-in-3nf-but-not-in-bcnf
BC->E
DE->A
A->B
BCNF Schema Not possible


Example.3 with I/O format 3
Source: https://stackoverflow.com/questions/8133071/decomposition-that-does-not-preserve-functional-dependency
( ({'Shimla','Jaipur'},{'Takshila'}) , ({'Takshila'},{'Jaipur'}) )

({'S','J','T'})
This is not in BCNF, since T->J holds and T is not a key.

Decomposing it into R1 = (T, J) and R2 = (T, S) with {T} and {T, S} being keys respectively leads to BCNF.
However, the dependency {S, J} -> {T} is lost.

Example.4
Source: http://www.mathcs.emory.edu/~cheung/Courses/377/Syllabus/9-NormalForms/examples.html
Enter all F.D.(s)
{ A->BCDE , E->FGH , I->J , AI->K , AL->M }

Obtained Keys by project, same as given on website
({'I', 'L', 'A'},)

Obtained BCNF Schema by project, same as given on website
({'I', 'A', 'K'}, {'M', 'L', 'A'}, {'H', 'F', 'G', 'E'}, {'I', 'L', 'A'}, {'C', 'D', 'E', 'B', 'A'}, {'I', 'J'})

Example.5
Source: https://www.cs.colostate.edu/~cs430dl/yr2018sp/more_examples/Ch8/Decomposition%20into%20BCNF.pdf
Part.A
{A -> BC, C -> DE}
Obtained BCNF Schema by project, same as given on website
({'A', 'C', 'B'}, {'D', 'C', 'E'})

Part.B
{AB -> C, B -> D, C -> A}
Obtained BCNF Schema (Non-Dependency preserving) by project, same as given on website
({'D', 'B'}, {'C', 'B'}, {'A', 'C'})

FAILURE:
Griffith Example.8
3NF: Decomposed ABCDE into ABCD & ACE which is not done by Griffith
BCNF: Magnification of error introduced at 3NF stage

Griffith Example.10
BCNF: Different answers Some FDs are In-consistent for BCNF, also Non-FD preserving BCNF

Griffith Example.12
{ A->B , AB->D , D->A , C->E }
3NF to BCNF: How ACD can be tranformed to ABD, while AB is there during 2NF

Example.6
Source: Bhargav Thankey
{A->BC,CEF->D,BD->EF,A->D,ACEF->G,B->A,CEFG->H,L->K,A->L,BFE->J,J->I,BJ->M}
'''
