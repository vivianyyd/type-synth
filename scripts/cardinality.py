from cvc5.pythonic import *

def _to_expr_ref(a, ctx, r=None):
    """
    It would've been nice if I could simply import this.
    """
    if isinstance(a, ExprRef):
        print(1)
        ast = a.ast
        if r is None:
            print(2)
            r = a.reverse_children
    elif isinstance(a, pc.Term):  # I think this is always the case for cardinality
        if r is None:  # I think this is always the case for cardinality
            r = False
        ast = a
    else:
        raise SMTException("Non-term/expression given to _to_expr_ref")
    sort = ast.getSort()
    if sort.isInteger():  # I think this is always the case for cardinality and have deleted most other options
        if ast.getKind() == Kind.CONST_INTEGER:
            return IntNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)  # I think this is always the case for cardinality
    return ExprRef(ast, ctx, r)  # Kept it just in case


def Cardinality(s):
    """
    Stared at cvc5 pythonic api SetComplement to write this
    """
    ctx = s.ctx
    return _to_expr_ref(ctx.solver.mkTerm(Kind.SET_CARD, s.ast), ctx)


