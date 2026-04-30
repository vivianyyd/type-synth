// 0_basics.types, 1_comparison.types, 6_float.types, 29_complex_mod.types

// Constants
zero
one
i

// Unary: t -> t
(neg zero)
(neg one)
(neg i)
(conj zero)
(conj one)
(conj i)
(inv one)
(inv i)
(sqrt one)
(sqrt zero)
(exp zero)
(exp one)
(log one)
(pow zero one)
(pow one zero)

// Binary: t -> t -> t
(add zero one)
(add one i)
(add zero zero)
(sub one zero)
(sub i one)
(mul zero one)
(mul one i)
(div one i)
(div i one)

// Float-returning: t -> float
(norm2 zero)
(norm2 one)
(norm2 i)
(norm zero)
(norm one)
(norm i)
(arg zero)
(arg one)
(arg i)

// polar: float -> float -> t
(polar Flt Flt)
(polar (norm one) (arg i))
(polar Flt (arg i))

// Chaining: unary ops on unary results
(neg (neg zero))
(neg (conj one))
(conj (neg i))
(inv (inv one))
(sqrt (sqrt one))
(exp (log one))
(neg (add zero one))
(conj (mul one i))
(inv (neg one))

// Binary ops on results of unary ops
(add (neg zero) (conj one))
(mul (neg one) (inv one))
(sub (conj i) (neg zero))
(div (neg one) (inv i))
(pow (neg one) (conj zero))
(add (sqrt one) (exp zero))
(mul (exp zero) (log one))

// Float outputs from norm/norm2/arg: use in float arithmetic
(= (norm zero) Flt)
(= (norm2 one) Flt)
(+. (norm zero) (norm one))
(+. (norm2 zero) (norm2 one))
(-. (norm one) (norm i))
( *. (norm one) (norm one))
(+. (arg i) Flt)
(polar (norm one) (norm one))
(polar (norm2 i) (arg one))

// norm output used in comparisons
(< (norm zero) (norm one))
(= (norm zero) Flt)
(> (norm one) (norm zero))

// Invalid
(add zero Flt)
(norm Flt)
(polar one Flt)
(mul zero Flt)
