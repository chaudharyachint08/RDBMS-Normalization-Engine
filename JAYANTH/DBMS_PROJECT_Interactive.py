'''
This Project is Aimed to Perform Basic & Advanced DB Decomposition related
Operation, which will be based upon concept of functional dependencies
Order will be like This

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
    print_schema(  NF_2(  set(lkup_1.keys())  )  )
    print_schema(  NF_3(  set(lkup_1.keys())  )  )
    print_schema(  NF_BC(  set(lkup_1.keys())  )  )
'''

import itertools

lkup_1 = {} # INTEGER TO CHARACTER MAPPING
lkup_2 = {} # CHARACTER TO INTEGER MAPPING
sym = set() # SET CONTAINING ALL SYMBOLS, (Tokens when extended), can be used as Global Schema also
FDs = set() # SET CONTAINING ALL FDs

print('Enter all F.D.(s)')
while True:
    ip = input()
    if not ip:
        break
    if ip.startswith('{') and ip.endswith('}'):
        tmp = ip.strip('{}').split(',')
        for ip in tmp:
            ip = ip.split('->')
            L, R = ip[0].strip(), ip[1].strip()
            FDs.add( (frozenset(L),frozenset(R)) )
            sym.update( set(L) | set(R) )
    elif ip.startswith('(') and ip.endswith(')'):
        tmp = eval(ip)
        for L,R in tmp:
            FDs.add( (frozenset(L),frozenset(R)) )
            sym.update( set(L) | set(R) )
    else:
        ip = ip.split('->')
        L, R = ip[0].strip(), ip[1].strip()
        FDs.add( (frozenset(L),frozenset(R)) )
        sym.update( set(L) | set(R) )

        
for i,j in enumerate(sorted(sym)):
    lkup_1[i] = j
    lkup_2[j] = i

FDs = { (frozenset(lkup_2[i] for i in l), frozenset(lkup_2[i] for i in r)) for l,r in FDs }

def print_FDs(FDs):
    for l,r in sorted(FDs,key=lambda FD:(sorted(lkup_1[i] for i in FD[0]),sorted(lkup_1[i] for i in FD[0]))):
        print( *sorted(lkup_1[i] for i in l), sep=',',end=' -> ')
        print( *sorted(lkup_1[i] for i in r), sep=',')

def print_keys(KEYS):
    print( tuple( sorted(lkup_1[i] for i in entry) for entry in sorted(KEYS,key = lambda x:''.join(lkup_1[j] for j in sorted(x))) ) , sep=' , ' )

def print_rltn(RLTN):
    print( sorted(lkup_1[i] for i in RLTN) , end='' )

def print_schema(SCHEMA):
    print( tuple( sorted(lkup_1[i] for i in rltn) for rltn in sorted(SCHEMA,key = lambda x:''.join(lkup_1[j] for j in sorted(x))) ) , sep=' , ' )
    
def applicable_FDs(FDs,RLTN):
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
    # CLOSURE FUNCTION MAY NOT BE NEEDED FOR THIS PROJECT
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
    #It should be a binary boolean operator
    tmp = { x for rltn in SCHEMA for x in rltn }
    for rltn in SCHEMA:
        tmp.intersection_update(rltn)
    keys = { key for rltn in SCHEMA for key in candidate_keys(rltn)[0] }
    #if Intersecting elements do form a superkey of any sub-relation
    return any( tmp>=key for key in keys)

def NF_2(RLTN):
    '''After the Decomposition, there shouldn't be any partial dependency'''
    decompose = set()
    keys,prime,non_prime = candidate_keys(RLTN)
    for l,r in FDs:
        # CONDITION FOR 2NF (Non-Prime Determined by Partial Key)
        if any(l<i for i in keys) and r&non_prime:
            tmp = set( r&non_prime )
            while True:
                tmp2 = tmp.copy()
                for i,j in FDs:
                    if i <= tmp:
                        tmp.update(j)
                if tmp == tmp2:
                    break
                else:
                    tmp2 = tmp
            decompose.add( (l,frozenset(tmp)) )      
    tmp = set()
    for l,r in decompose:
        tmp.update(r)

    res = merge_schema( {frozenset(RLTN-tmp)} | {l|r for l,r in decompose} )
    for tmp_rltn in res:
        if not is_lossless({frozenset(RLTN-tmp),tmp_rltn}):
            print('Loss-Less 2NF Decomposition not possible')
            return {frozenset(RLTN)}
    SCHEMA_2NF =  res
    return SCHEMA_2NF

def NF_3(RLTN):
    '''LHS must be Super Key OR RHS be Prime attribute'''
    SCHEMA_2NF = NF_2(RLTN)
    SCHEMA_3NF = set()
    for rltn in SCHEMA_2NF:
        decompose = set()
        keys,prime,non_prime = candidate_keys( rltn )
        tmp_FDs = applicable_FDs(FDs,rltn)
        for l,r in tmp_FDs:
            # CONDITION FOR 3NF (Non-Prime Determining Non-Prime Attribute)
            if not any(i<=l for i in keys) and r&non_prime:
                tmp = set( r&non_prime )
                while True:
                    tmp2 = tmp.copy()
                    for i,j in tmp_FDs:
                        if i <= tmp:
                            tmp.update(j)
                    if tmp == tmp2:
                        break
                    else:
                        tmp2 = tmp
                decompose.add( (l,frozenset(tmp)) )      
        tmp = set()
        for l,r in decompose:
            tmp.update(r)
        res = merge_schema( {frozenset(rltn-tmp)} | {l|r for l,r in decompose} )
        for tmp_rltn in res:
            if not is_lossless({frozenset(RLTN-tmp),tmp_rltn}):
                print('Loss-Less 3NF Decomposition not possible')
                return SCHEMA_2NF
        SCHEMA_3NF.update( res )

    SCHEMA_3NF = merge_schema( SCHEMA_3NF )
    return SCHEMA_3NF

def NF_BC(RLTN):
    '''LHS must be superkey'''
    SCHEMA_3NF  = NF_3(RLTN)
    SCHEMA_BCNF = set()
    for rltn in SCHEMA_3NF:
        decompose = set()
        keys,prime,non_prime = candidate_keys( rltn )
        tmp_FDs = applicable_FDs(FDs,rltn)
        for l,r in tmp_FDs:
            # CONDITION FOR BCNF (Non-Prime Determining Non-Prime Attribute)
            if not any(i<=l for i in keys):
                tmp = set( r )
                while True:
                    tmp2 = tmp.copy()
                    for i,j in tmp_FDs:
                        if i <= tmp:
                            tmp.update(j)
                    if tmp == tmp2:
                        break
                    else:
                        tmp2 = tmp
                decompose.add( (l,frozenset(tmp)) )
        tmp = set()
        for l,r in decompose:
            tmp.update(r)

        res = rltn_2 = merge_schema( {frozenset(rltn-tmp)} | {l|r for l,r in decompose} )
        for tmp_rltn in res:
            if not is_lossless({frozenset(RLTN-tmp),tmp_rltn}):
                print('Loss-Less BCNF Decomposition not possible')
                return SCHEMA_3NF
        '''
        CHEKING OF FUNCTIONAL DEPENDENCY PRESERVING BEHAVIOUR
        if FD Preserving is Violated, printing which FDs are lost
        '''
        tmp_FDs_2 = set()
        for i in rltn_2:
            tmp_FDs_2.update( applicable_FDs(FDs,i) )
    
        if covering(tmp_FDs_2,tmp_FDs):
            SCHEMA_BCNF.update( rltn_2 )
        else:
            print('On converting')
            print_rltn(rltn)
            print(' to',end=' ')
            print_schema(rltn_2)

            print('BCNF is not FD preserving, these FDs are violated')
            print_FDs(tmp_FDs-tmp_FDs_2)
            if input('Press 1 for BCNF, (3NF is taken as default) : ')=='1':
                SCHEMA_BCNF.update( rltn_2 )
            else:
                SCHEMA_BCNF.update( {rltn} )

    SCHEMA_BCNF = merge_schema( SCHEMA_BCNF )
    return SCHEMA_BCNF


def do_all():
    CMDs = ( 'FDs = minimal_cover(FDs)','print_FDs(FDs)','print_keys(  candidate_keys(  set(lkup_1.keys())  )[0]  )',
    'print_schema(  NF_2(  set(lkup_1.keys())  )  )','print_schema(  NF_3(  set(lkup_1.keys())  )  )',
    'print_schema(  NF_BC(  set(lkup_1.keys())  )  )' )
    for i in CMDs:
        print(i)
        exec(i)
        print()

        
#Function call to perform all test commands
do_all()


'''
Schema will be of SET type, where each relation will be FROZEN_SET type
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
Griffith Example.2
BCNF: Due to not handling cyclic FD decomposition in BCNF (others also), introduce WHILE loops

Griffith Example.8
3NF: Decomposed ABCDE into ABCD & ACE which is not done by Griffith
BCNF: Due to not handling cyclic FD decomposition in BCNF (others also), introduce WHILE loops

Griffith Example.10
BCNF: Due to not handling cyclic FD decomposition in BCNF (others also), introduce WHILE loops

Griffith Example.12
{ A->B , AB->D , D->A , C->E }
On converting 2NF to 3NF, ACD was not decomposed by Griffith but project does into AD,CD
3NF to BCNF: Even if website is correct, how can ACD can be tranformed to ABD, while AB is there during 2NF

CHECKPOINT
SOLUTION:
Use indefinite WHILE loop & Flag Set/Reset based approach for Higher Normal form conversion on each step
Flags should be stored as separate dictionary, with VALUES as FLAG value
if 1 then has to convert to higher normal form, else leave it
'''
