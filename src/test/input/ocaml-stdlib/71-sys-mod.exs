// 0-basics.types, 1-comparison.types, 4-arith.types, 6-float.types, 7-str.types, 71-sys-mod.types

// String constants
executable_name
os_type
ocaml_version

// Int constants
io_buffer_size
word_size
int_size
max_string_length
max_array_length
max_floatarray_length

// Bool constants
unix
win32
cygwin
big_endian
development_version

// file_exists, is_directory, is_regular_file: string -> bool
(file_exists Str)
(is_directory Str)
(is_regular_file Str)

// remove: string -> unit
(remove Str)

// rename: string -> string -> unit
(rename Str Str)

// getenv: string -> string
(getenv Str)

// getenv_opt: string -> string option
(getenv_opt Str)

// command: string -> int
(command Str)

// time: unit -> float
(time Unit)

// chdir, rmdir: string -> unit
(chdir Str)
(rmdir Str)

// mkdir: string -> int -> unit
(mkdir Str Num)

// getcwd: unit -> string
(getcwd Unit)

// readdir: string -> string array
(readdir Str)

// runtime_variant, runtime_parameters: unit -> string
(runtime_variant Unit)
(runtime_parameters Unit)

// poll_actions: unit -> unit
(poll_actions Unit)

// signal constants (int/signal type)
sigabrt
sigint
sigterm
sigusr1
sigusr2

// signal_to_string: signal -> string
(signal_to_string sigabrt)
(signal_to_string sigint)

// signal_of_int: int -> signal
(signal_of_int Num)

// signal_to_int: signal -> int
(signal_to_int sigabrt)
(signal_to_int sigint)

// catch_break: bool -> unit
(catch_break true)
(catch_break false)

// runtime_warnings_enabled: unit -> bool
(runtime_warnings_enabled Unit)

// enable_runtime_warnings: bool -> unit
(enable_runtime_warnings true)
(enable_runtime_warnings false)

// opaque_identity: 'a -> 'a
(opaque_identity Num)
(opaque_identity Str)
(opaque_identity true)

// Chaining: file_exists/is_directory/is_regular_file return bool
(= (file_exists Str) true)
(not (file_exists Str))
(not (is_directory Str))
(not (is_regular_file Str))
(&& (file_exists Str) (is_regular_file Str))
(|| (is_directory Str) (is_regular_file Str))

// getenv returns string
(= (getenv Str) Str)
(^ (getenv Str) Str)
(file_exists (getenv Str))
(is_directory (getenv Str))
(getenv (getenv Str))

// getcwd returns string
(= (getcwd Unit) Str)
(^ (getcwd Unit) Str)
(file_exists (getcwd Unit))
(is_directory (getcwd Unit))
(chdir (getcwd Unit))
(readdir (getcwd Unit))

// command returns int
(= (command Str) Num)
(succ (command Str))
(< (command Str) Num)
(= (command Str) (command Str))

// time returns float
(= (time Unit) Flt)
(+. (time Unit) Flt)
(*. (time Unit) (time Unit))
(< (time Unit) Flt)

// signal_to_int returns int
(= (signal_to_int sigabrt) Num)
(succ (signal_to_int sigterm))
(< (signal_to_int sigint) (signal_to_int sigterm))
(signal_of_int (signal_to_int sigabrt))

// signal_of_int returns signal
(signal_to_string (signal_of_int Num))
(signal_to_int (signal_of_int Num))

// signal_to_string returns string
(= (signal_to_string sigabrt) Str)
(^ (signal_to_string sigabrt) Str)

// runtime_warnings_enabled returns bool
(= (runtime_warnings_enabled Unit) true)
(not (runtime_warnings_enabled Unit))
(enable_runtime_warnings (runtime_warnings_enabled Unit))

// opaque_identity is identity — output same type as input
(succ (opaque_identity Num))
(^ (opaque_identity Str) Str)
(not (opaque_identity true))
(opaque_identity (opaque_identity Num))
(= (opaque_identity Num) Num)

// int constants usable in arithmetic
(succ word_size)
(< word_size int_size)
(= io_buffer_size Num)
(+ word_size io_buffer_size)

// Invalid
(file_exists Num)
(is_directory Num)
(getenv Num)
(command Num)
(signal_to_string Num)
(signal_of_int Str)
(succ (file_exists Str))
(not (command Str))
(+. (signal_to_int sigabrt) Flt)
