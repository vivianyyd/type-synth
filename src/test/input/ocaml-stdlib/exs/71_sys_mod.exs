// 0_basics.types, 1_comparison.types, 4_arith.types, 6_float.types, 7_str.types, 71_sys_mod.types

// String constants
Sys.executable_name
Sys.os_type
Sys.ocaml_version

// Int constants
Sys.io_buffer_size
Sys.word_size
Sys.int_size
Sys.max_string_length
Sys.max_array_length
Sys.max_floatarray_length

// Bool constants
Sys.unix
Sys.win32
Sys.cygwin
Sys.big_endian
Sys.development_version

// file_exists, is_directory, is_regular_file: string -> bool
(Sys.file_exists Str)
(Sys.is_directory Str)
(Sys.is_regular_file Str)

// remove: string -> unit
(Sys.remove Str)

// rename: string -> string -> unit
(Sys.rename Str Str)

// getenv: string -> string
(Sys.getenv Str)

// getenv_opt: string -> string option
(Sys.getenv_opt Str)

// command: string -> int
(Sys.command Str)

// time: unit -> float
(Sys.time Unit)

// chdir, rmdir: string -> unit
(Sys.chdir Str)
(Sys.rmdir Str)

// mkdir: string -> int -> unit
(Sys.mkdir Str Num)

// getcwd: unit -> string
(Sys.getcwd Unit)

// readdir: string -> string array
(Sys.readdir Str)

// runtime_variant, runtime_parameters: unit -> string
(Sys.runtime_variant Unit)
(Sys.runtime_parameters Unit)

// poll_actions: unit -> unit
(Sys.poll_actions Unit)

// signal constants (int/signal type)
Sys.sigabrt
Sys.sigint
Sys.sigterm
Sys.sigusr1
Sys.sigusr2

// signal_to_string: signal -> string
(Sys.signal_to_string Sys.sigabrt)
(Sys.signal_to_string Sys.sigint)

// signal_of_int: int -> signal
(Sys.signal_of_int Num)

// signal_to_int: signal -> int
(Sys.signal_to_int Sys.sigabrt)
(Sys.signal_to_int Sys.sigint)

// catch_break: bool -> unit
(Sys.catch_break true)
(Sys.catch_break false)

// runtime_warnings_enabled: unit -> bool
(Sys.runtime_warnings_enabled Unit)

// enable_runtime_warnings: bool -> unit
(Sys.enable_runtime_warnings true)
(Sys.enable_runtime_warnings false)

// opaque_identity: 'a -> 'a
(Sys.opaque_identity Num)
(Sys.opaque_identity Str)
(Sys.opaque_identity true)

// Chaining: file_exists/is_directory/is_regular_file return bool
((=) (Sys.file_exists Str) true)
(not (Sys.file_exists Str))
(not (Sys.is_directory Str))
(not (Sys.is_regular_file Str))
((&&) (Sys.file_exists Str) (Sys.is_regular_file Str))
((||) (Sys.is_directory Str) (Sys.is_regular_file Str))

// getenv returns string
((=) (Sys.getenv Str) Str)
((^) (Sys.getenv Str) Str)
(Sys.file_exists (Sys.getenv Str))
(Sys.is_directory (Sys.getenv Str))
(Sys.getenv (Sys.getenv Str))

// getcwd returns string
((=) (Sys.getcwd Unit) Str)
((^) (Sys.getcwd Unit) Str)
(Sys.file_exists (Sys.getcwd Unit))
(Sys.is_directory (Sys.getcwd Unit))
(Sys.chdir (Sys.getcwd Unit))
(Sys.readdir (Sys.getcwd Unit))

// command returns int
((=) (Sys.command Str) Num)
(succ (Sys.command Str))
((<) (Sys.command Str) Num)
((=) (Sys.command Str) (Sys.command Str))

// time returns float
((=) (Sys.time Unit) Flt)
((+.) (Sys.time Unit) Flt)
(( *. ) (Sys.time Unit) (Sys.time Unit))
((<) (Sys.time Unit) Flt)

// signal_to_int returns int
((=) (Sys.signal_to_int Sys.sigabrt) Num)
(succ (Sys.signal_to_int Sys.sigterm))
((<) (Sys.signal_to_int Sys.sigint) (Sys.signal_to_int Sys.sigterm))
(Sys.signal_of_int (Sys.signal_to_int Sys.sigabrt))

// signal_of_int returns signal
(Sys.signal_to_string (Sys.signal_of_int Num))
(Sys.signal_to_int (Sys.signal_of_int Num))

// signal_to_string returns string
((=) (Sys.signal_to_string Sys.sigabrt) Str)
((^) (Sys.signal_to_string Sys.sigabrt) Str)

// runtime_warnings_enabled returns bool
((=) (Sys.runtime_warnings_enabled Unit) true)
(not (Sys.runtime_warnings_enabled Unit))
(Sys.enable_runtime_warnings (Sys.runtime_warnings_enabled Unit))

// opaque_identity is identity — output same type as input
(succ (Sys.opaque_identity Num))
((^) (Sys.opaque_identity Str) Str)
(not (Sys.opaque_identity true))
(Sys.opaque_identity (Sys.opaque_identity Num))
((=) (Sys.opaque_identity Num) Num)

// int constants usable in arithmetic
(succ Sys.word_size)
((<) Sys.word_size Sys.int_size)
((=) Sys.io_buffer_size Num)
((+) Sys.word_size Sys.io_buffer_size)

// Invalid
(Sys.file_exists Num)
(Sys.is_directory Num)
(Sys.getenv Num)
(Sys.command Num)
(Sys.signal_to_string Num)
(Sys.signal_of_int Str)
(succ (Sys.file_exists Str))
(not (Sys.command Str))
((+.) (Sys.signal_to_int Sys.sigabrt) Flt)
