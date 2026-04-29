// 0-basics.types, 4-arith.types, 5-bitwise.types

(land Num Num)
(lor Num Num)
(lxor Num Num)
(lnot Num)
(lsl Num Num)
(lsr Num Num)
(asr Num Num)

(land (lnot Num) Num)
(lor (lsl Num Num) (lsr Num Num))
(lxor (land Num Num) (lor Num Num))
(lnot (lnot Num))
(asr (lsl Num Num) Num)
(land Num (lnot (lxor Num Num)))

(succ (land Num Num))
(abs (lnot Num))
(+ (land Num Num) (lor Num Num))

(land Num Str)
(lsl Str Num)
(lxor true Num)
(lnot Str)
(lor Num Flt)

// all bitwise ops return int: chain them
(lnot (lnot (lnot Num)))
(land (land Num Num) Num)
(lor Num (lor Num Num))
(lxor (lxor Num Num) Num)
(lsl (lsr Num Num) Num)
(asr (asr Num Num) Num)

// combine: outputs of bitwise ops fed into other bitwise ops
(land (lsl Num Num) (lsr Num Num))
(lor (lnot Num) (lsl Num Num))
(lxor (land Num Num) (lor Num Num))
(lnot (lxor (land Num Num) (lor Num Num)))
(asr (land (lsl Num Num) Num) Num)
(land (lnot (lnot Num)) (lxor Num Num))

// bitwise output is int: use in arithmetic
(succ (land Num Num))
(pred (lor Num Num))
(+ (land Num Num) (lor Num Num))
(- (lsl Num Num) (lsr Num Num))
( * (land Num Num) Num)
(abs (lnot Num))
(mod (land Num Num) (succ Num))

// arithmetic output is int: use in bitwise
(land (succ Num) Num)
(lor Num (abs Num))
(lxor (+ Num Num) (- Num Num))
(lsl (abs Num) Num)
(lnot (succ (succ Num)))

// invalid chaining
(lsl (land Num Num) Str)
(land (succ Num) true)
