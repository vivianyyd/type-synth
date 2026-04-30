// 0_basics.types, 1_comparison.types, 4_arith.types, 55_obj_mod.types

// repr: 'a -> t  (box any value as an Obj.t)
(Obj.repr Num)
(Obj.repr Str)
(Obj.repr true)
(Obj.repr Char)

// obj: t -> 'a  (unbox; result is polymorphic)
(Obj.obj (Obj.repr Num))
(Obj.obj (Obj.repr Str))

// magic: 'a -> 'b  (unsafe cast)
(Obj.magic Num)
(Obj.magic Str)
(Obj.magic true)

// Predicates: t -> bool
(Obj.is_block (Obj.repr Num))
(Obj.is_block (Obj.repr Str))
(Obj.is_int (Obj.repr Num))
(Obj.is_int (Obj.repr true))

// tag, size, reachable_words: t -> int
(Obj.tag (Obj.repr Num))
(Obj.tag (Obj.repr Str))
(Obj.size (Obj.repr Str))
(Obj.size (Obj.repr (cons Num [])))
(Obj.reachable_words (Obj.repr Str))

// field: t -> int -> t
(Obj.field (Obj.repr Str) Num)
(Obj.field (Obj.repr (cons Num [])) Num)

// double_field: t -> int -> float
(Obj.double_field (Obj.repr Flt) Num)

// new_block: int -> int -> t
(Obj.new_block Num Num)

// dup: t -> t
(Obj.dup (Obj.repr Str))
(Obj.dup (Obj.repr Num))
(Obj.dup (Obj.new_block Num Num))

// with_tag: int -> t -> t
(Obj.with_tag Num (Obj.repr Str))
(Obj.with_tag (Obj.tag (Obj.repr Str)) (Obj.repr Str))

// Integer tag constants
Obj.first_non_constant_constructor_tag
Obj.last_non_constant_constructor_tag
Obj.string_tag
Obj.double_tag
Obj.closure_tag
Obj.object_tag

// Chaining: repr returns Obj.t — use in all Obj ops
(Obj.is_block (Obj.repr Num))
(Obj.is_int (Obj.repr Num))
(Obj.tag (Obj.repr Str))
(Obj.size (Obj.repr Str))
(Obj.dup (Obj.repr Num))
(Obj.field (Obj.repr Str) Num)
(Obj.with_tag Obj.string_tag (Obj.repr Str))

// tag returns int — use in arithmetic and as argument to with_tag
((=) (Obj.tag (Obj.repr Str)) Num)
(succ (Obj.tag (Obj.repr Str)))
((<) (Obj.tag (Obj.repr Str)) Obj.string_tag)
((=) (Obj.tag (Obj.repr Str)) Obj.string_tag)
(Obj.with_tag (Obj.tag (Obj.repr Num)) (Obj.repr Num))
(Obj.with_tag (succ (Obj.tag (Obj.repr Str))) (Obj.repr Str))

// size / reachable_words return int
((=) (Obj.size (Obj.repr Str)) Num)
(succ (Obj.size (Obj.repr (cons Num []))))
((<) (Obj.size (Obj.repr Num)) (Obj.size (Obj.repr Str)))
(Obj.field (Obj.repr Str) (Obj.size (Obj.repr Str)))

// double_field returns float
((+.) (Obj.double_field (Obj.repr Flt) Num) Flt)
((=) (Obj.double_field (Obj.repr Flt) Num) Flt)

// is_block / is_int return bool
((=) (Obj.is_block (Obj.repr Str)) true)
((=) (Obj.is_int (Obj.repr Num)) true)
(not (Obj.is_block (Obj.repr Num)))
(not (Obj.is_int (Obj.repr Str)))

// field returns Obj.t — chain into more obj ops
(Obj.tag (Obj.field (Obj.repr Str) Num))
(Obj.is_block (Obj.field (Obj.repr Str) Num))
(Obj.dup (Obj.field (Obj.repr Str) Num))

// dup returns Obj.t — chain
(Obj.tag (Obj.dup (Obj.repr Str)))
(Obj.is_int (Obj.dup (Obj.repr Num)))

// with_tag returns Obj.t
(Obj.tag (Obj.with_tag Num (Obj.repr Str)))
(Obj.is_block (Obj.with_tag Obj.string_tag (Obj.repr Str)))

// Extension_constructor submodule
(Obj.Extension_constructor.name (Obj.Extension_constructor.of_val Num))
(Obj.Extension_constructor.id (Obj.Extension_constructor.of_val Num))
((=) (Obj.Extension_constructor.id (Obj.Extension_constructor.of_val Num)) Num)
((=) (Obj.Extension_constructor.name (Obj.Extension_constructor.of_val Num)) Str)

// Obj.Ephemeron submodule
(Obj.Ephemeron.create Num)
(Obj.Ephemeron.length (Obj.Ephemeron.create Num))
(Obj.Ephemeron.check_key (Obj.Ephemeron.create Num) Num)
(Obj.Ephemeron.check_data (Obj.Ephemeron.create Num))

// Invalid: Obj.t used where plain values expected, and vice versa
(succ (Obj.repr Num))
((^) (Obj.repr Str) Str)
(not (Obj.repr true))
(Obj.tag Num)
(Obj.size Str)
(Obj.is_block Num)
(Obj.field Num Num)
(succ (Obj.is_block (Obj.repr Num)))
(not (Obj.tag (Obj.repr Str)))
