from cvc5.pythonic import *
from cardinality import *

if __name__ == '__main__':
    p1 = Const('p1', SetSort(IntSort()))
    p2 = Const('p2', SetSort(IntSort()))
    p3 = Const('p3', SetSort(IntSort()))
    p4 = Const('p4', SetSort(IntSort()))
    a, c, size = Ints('a c size')
    solve(
        IsSubset(p1, p2),
        IsSubset(p4, p3),
        Not(IsSubset(p1, p3)),
        Not(IsSubset(p1, p4)),
        Not(IsSubset(p2, p1)), 
        Not(IsSubset(p2, p3)),
        Not(IsSubset(p2, p4)),
        Not(IsSubset(p3, p1)),
        Not(IsSubset(p3, p2)),
        Not(IsSubset(p3, p4)),
        Not(IsSubset(p4, p1)),
        Not(IsSubset(p4, p2)),
        Singleton(a) == p1,
        Singleton(c) == p4,
        SetMinus(p2, p1) != EmptySet(IntSort()),
        size == Cardinality(p2)
    )


