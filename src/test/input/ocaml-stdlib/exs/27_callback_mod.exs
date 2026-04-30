// 0_basics.types, 27_callback_mod.types

// register: string -> 'a -> unit (polymorphic in second argument)
(Callback.register Str Num)
(Callback.register Str Str)
(Callback.register Str true)
(Callback.register Str false)

// Invalid
(Callback.register Num Str)
(Callback.register true Num)
