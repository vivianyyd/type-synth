from cvc5.pythonic import *
from cardinality import *
if __name__ == '__main__':
	v3_0 = Int('v3_0')
	L0, L2 = Ints('L0 L2')
	_0_0 = Const('_0_0', SetSort(IntSort()))
	_i_0 = Const('_i_0', SetSort(IntSort()))
	_i_0_0 = Const('_i_0_0', SetSort(IntSort()))
	_cons_0 = Const('_cons_0', SetSort(IntSort()))
	_cons_1 = Const('_cons_1', SetSort(IntSort()))
	_cons_2 = Const('_cons_2', SetSort(IntSort()))
	solve(
        L0 == 0,
        L2 == 1,
		L0 == Cardinality(_0_0),
		L2 == Cardinality(_i_0),
		#L2 == Cardinality(_i_0_0),
		#L2 == Cardinality(_cons_1),
		#L2 == Cardinality(_cons_2),
		_cons_0 == Singleton(v3_0),
		_0_0 == EmptySet(IntSort()),
		_i_0 == EmptySet(IntSort()),
		_i_0_0 == EmptySet(IntSort()),
		_cons_0 != EmptySet(IntSort()),
		_cons_0 == _cons_1,
		_cons_0 == _cons_2,
		_cons_1 != EmptySet(IntSort()),
		_cons_1 == _cons_2,
		_cons_2 != EmptySet(IntSort()),
		SetMinus(_cons_1, _cons_0) == EmptySet(IntSort()),
		SetMinus(_cons_2, SetUnion(_cons_0, _cons_1)) == EmptySet(IntSort()),
	)



