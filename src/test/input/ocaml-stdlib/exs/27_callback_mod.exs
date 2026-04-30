// 0_basics.types, 27_callback_mod.types

// register: string -> 'a -> unit (polymorphic in second argument)
(register Str Num)
(register Str Str)
(register Str true)
(register Str false)

// Invalid
(register Num Str)
(register true Num)
