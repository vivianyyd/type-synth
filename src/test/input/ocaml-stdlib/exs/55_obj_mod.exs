// 0_basics.types, 1_comparison.types, 4_arith.types, 55_obj_mod.types

// repr: 'a -> t  (box any value as an Obj.t)
(repr Num)
(repr Str)
(repr true)
(repr Char)

// obj: t -> 'a  (unbox; result is polymorphic)
(obj (repr Num))
(obj (repr Str))

// magic: 'a -> 'b  (unsafe cast)
(magic Num)
(magic Str)
(magic true)

// Predicates: t -> bool
(is_block (repr Num))
(is_block (repr Str))
(is_int (repr Num))
(is_int (repr true))

// tag, size, reachable_words: t -> int
(tag (repr Num))
(tag (repr Str))
(size (repr Str))
(size (repr (cons Num [])))
(reachable_words (repr Str))

// field: t -> int -> t
(field (repr Str) Num)
(field (repr (cons Num [])) Num)

// double_field: t -> int -> float
(double_field (repr Flt) Num)

// new_block: int -> int -> t
(new_block Num Num)

// dup: t -> t
(dup (repr Str))
(dup (repr Num))
(dup (new_block Num Num))

// with_tag: int -> t -> t
(with_tag Num (repr Str))
(with_tag (tag (repr Str)) (repr Str))

// Integer tag constants
first_non_constant_constructor_tag
last_non_constant_constructor_tag
string_tag
double_tag
closure_tag
object_tag

// Chaining: repr returns Obj.t — use in all Obj ops
(is_block (repr Num))
(is_int (repr Num))
(tag (repr Str))
(size (repr Str))
(dup (repr Num))
(field (repr Str) Num)
(with_tag string_tag (repr Str))

// tag returns int — use in arithmetic and as argument to with_tag
(= (tag (repr Str)) Num)
(succ (tag (repr Str)))
(< (tag (repr Str)) string_tag)
(= (tag (repr Str)) string_tag)
(with_tag (tag (repr Num)) (repr Num))
(with_tag (succ (tag (repr Str))) (repr Str))

// size / reachable_words return int
(= (size (repr Str)) Num)
(succ (size (repr (cons Num []))))
(< (size (repr Num)) (size (repr Str)))
(field (repr Str) (size (repr Str)))

// double_field returns float
(+. (double_field (repr Flt) Num) Flt)
(= (double_field (repr Flt) Num) Flt)

// is_block / is_int return bool
(= (is_block (repr Str)) true)
(= (is_int (repr Num)) true)
(not (is_block (repr Num)))
(not (is_int (repr Str)))

// field returns Obj.t — chain into more obj ops
(tag (field (repr Str) Num))
(is_block (field (repr Str) Num))
(dup (field (repr Str) Num))

// dup returns Obj.t — chain
(tag (dup (repr Str)))
(is_int (dup (repr Num)))

// with_tag returns Obj.t
(tag (with_tag Num (repr Str)))
(is_block (with_tag string_tag (repr Str)))

// Extension_constructor submodule
(Extension_constructor.name (Extension_constructor.of_val Num))
(Extension_constructor.id (Extension_constructor.of_val Num))
(= (Extension_constructor.id (Extension_constructor.of_val Num)) Num)
(= (Extension_constructor.name (Extension_constructor.of_val Num)) Str)

// Obj.Ephemeron submodule
(Ephemeron.create Num)
(Ephemeron.length (Ephemeron.create Num))
(Ephemeron.check_key (Ephemeron.create Num) Num)
(Ephemeron.check_data (Ephemeron.create Num))

// Invalid: Obj.t used where plain values expected, and vice versa
(succ (repr Num))
(^ (repr Str) Str)
(not (repr true))
(tag Num)
(size Str)
(is_block Num)
(field Num Num)
(succ (is_block (repr Num)))
(not (tag (repr Str)))
