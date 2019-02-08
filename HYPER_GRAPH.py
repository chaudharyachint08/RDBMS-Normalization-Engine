import itertools

mat = set()
nV = int(input('Enter Number of Vertices').strip())
V = frozenset(range(nV))

print('Enter Hyper-Edges ')
while True:
    ip = input()
    if not ip:
        break
    mat.add(frozenset(int(x) for x in ip.strip().split()))

def cartesian_product(A,B):
    "A ∨ B = {E[i] ∪ E[j] |1 ≤ i ≤ n(A), 1 ≤ j ≤ n(A)}"
    return {a|b for a in A for b in B}

def minimization(A):
    "μ(H) = {X ∈ E; ¬∃Y ∈ E, Y ⊆ X}" #It is Proper-Subset operation
    return  { a for a in A if not any(x<a for x in A)}

def clutter(A):
    "ν(H) = {X|X ⊆ A; ∃Y ∈ E, Y ⊆ X}"
    return { frozenset(x)|a for a in A for ln in range(nV-len(a)+1) for x in itertools.combinations(V-a,ln)}

def inverse_clutter(A):
    "v'(H) = {X|X ⊆ A; ∃Y ∈ E, Y ⊃ X}"
    return { frozenset(x) for a in A for ln in range(len(a)+1) for x in itertools.combinations(a,ln)}

def blocker(A):
    "τ(H) = {X ⊆ A; ∀Y ∈ E,X ∩ Y != ∅}"
    return { frozenset(x) for ln in range(nV+1) for x in itertools.combinations(V,ln) if all(frozenset(x)&a for a in A)}

def slices(A):
    "λ(H) = μ(τ(H))"
    return minimization(blocker(A))
