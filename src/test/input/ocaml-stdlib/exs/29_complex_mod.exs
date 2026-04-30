// 0_basics.types, 1_comparison.types, 6_float.types, 29_complex_mod.types

// Constants
Complex.zero
Complex.one
Complex.i

// Unary: t -> t
(Complex.neg Complex.zero)
(Complex.neg Complex.one)
(Complex.neg Complex.i)
(Complex.conj Complex.zero)
(Complex.conj Complex.one)
(Complex.conj Complex.i)
(Complex.inv Complex.one)
(Complex.inv Complex.i)
(Complex.sqrt Complex.one)
(Complex.sqrt Complex.zero)
(Complex.exp Complex.zero)
(Complex.exp Complex.one)
(Complex.log Complex.one)
(Complex.pow Complex.zero Complex.one)
(Complex.pow Complex.one Complex.zero)

// Binary: t -> t -> t
(Complex.add Complex.zero Complex.one)
(Complex.add Complex.one Complex.i)
(Complex.add Complex.zero Complex.zero)
(Complex.sub Complex.one Complex.zero)
(Complex.sub Complex.i Complex.one)
(Complex.mul Complex.zero Complex.one)
(Complex.mul Complex.one Complex.i)
(Complex.div Complex.one Complex.i)
(Complex.div Complex.i Complex.one)

// Float-returning: t -> float
(Complex.norm2 Complex.zero)
(Complex.norm2 Complex.one)
(Complex.norm2 Complex.i)
(Complex.norm Complex.zero)
(Complex.norm Complex.one)
(Complex.norm Complex.i)
(Complex.arg Complex.zero)
(Complex.arg Complex.one)
(Complex.arg Complex.i)

// polar: float -> float -> t
(Complex.polar Flt Flt)
(Complex.polar (Complex.norm Complex.one) (Complex.arg Complex.i))
(Complex.polar Flt (Complex.arg Complex.i))

// Chaining: unary ops on unary results
(Complex.neg (Complex.neg Complex.zero))
(Complex.neg (Complex.conj Complex.one))
(Complex.conj (Complex.neg Complex.i))
(Complex.inv (Complex.inv Complex.one))
(Complex.sqrt (Complex.sqrt Complex.one))
(Complex.exp (Complex.log Complex.one))
(Complex.neg (Complex.add Complex.zero Complex.one))
(Complex.conj (Complex.mul Complex.one Complex.i))
(Complex.inv (Complex.neg Complex.one))

// Binary ops on results of unary ops
(Complex.add (Complex.neg Complex.zero) (Complex.conj Complex.one))
(Complex.mul (Complex.neg Complex.one) (Complex.inv Complex.one))
(Complex.sub (Complex.conj Complex.i) (Complex.neg Complex.zero))
(Complex.div (Complex.neg Complex.one) (Complex.inv Complex.i))
(Complex.pow (Complex.neg Complex.one) (Complex.conj Complex.zero))
(Complex.add (Complex.sqrt Complex.one) (Complex.exp Complex.zero))
(Complex.mul (Complex.exp Complex.zero) (Complex.log Complex.one))

// Float outputs from norm/norm2/arg: use in float arithmetic
((=) (Complex.norm Complex.zero) Flt)
((=) (Complex.norm2 Complex.one) Flt)
((+.) (Complex.norm Complex.zero) (Complex.norm Complex.one))
((+.) (Complex.norm2 Complex.zero) (Complex.norm2 Complex.one))
((-.) (Complex.norm Complex.one) (Complex.norm Complex.i))
(( *. ) (Complex.norm Complex.one) (Complex.norm Complex.one))
((+.) (Complex.arg Complex.i) Flt)
(Complex.polar (Complex.norm Complex.one) (Complex.norm Complex.one))
(Complex.polar (Complex.norm2 Complex.i) (Complex.arg Complex.one))

// norm output used in comparisons
((<) (Complex.norm Complex.zero) (Complex.norm Complex.one))
((=) (Complex.norm Complex.zero) Flt)
((>) (Complex.norm Complex.one) (Complex.norm Complex.zero))

// Invalid
(Complex.add Complex.zero Flt)
(Complex.norm Flt)
(Complex.polar Complex.one Flt)
(Complex.mul Complex.zero Flt)
