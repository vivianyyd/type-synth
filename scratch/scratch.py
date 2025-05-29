from cvc5.pythonic import *
from cardinality import *

if __name__ == '__main__':
    #x, y = Reals('x y')
    #solve(0 < x, 0 < y, x + y < 1, x <= y)
    # If we get the model (the satisfying assignment) explicitly, we can evaluate terms under it.
    #s = Solver()
    #s.add(0 < x, 0 < y, x + y < 1, x <= y)
    #assert sat == s.check()
    #m = s.model()
    #print('x:', m[x], 'x - y:', m[x - y])

    #a, b = Ints('a b')
    #solve(0 < a, 0 < b, a + b < 1, a <= b)

    #A, B, C = [Set(name, IntSort()) for name in "ABC"]
    #prove((A | B) & C == (A & C) | (B & C))
    #prove(IsSubset(EmptySet(IntSort()), A))

    f = Function('f', IntSort(), IntSort(), IntSort())
    x = Int('x')
    y = Int('y')
    #solve(ForAll([x, y], f(x, y) >= x))

    #solve(ForAll([x], y == 1))

    # Goal: a is the lowest non-negative number == 0
    a, b = Ints('a b')
    geq0 = Lambda([x], x >= 0)
    #geq0 = Function('geq0', IntSort(), BoolSort())
    #ForAll([x], geq0(x) == (x >= 0)) # Can't solve
    #t = geq0(a)
    solve(
        a >= 0,
        ForAll([b], Implies(b >= 0, a <= b))
    )

