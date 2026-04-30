// 0_basics.types, 1_comparison.types, 7_str.types, 37_filename_mod.types

// String constants
Filename.current_dir_name
Filename.parent_dir_name
Filename.dir_sep
Filename.null

// concat: string -> string -> string
(Filename.concat Str Str)
(Filename.concat Filename.current_dir_name Str)
(Filename.concat Str Filename.parent_dir_name)
(Filename.concat Filename.dir_sep Str)

// basename, dirname: string -> string
(Filename.basename Str)
(Filename.dirname Str)

// extension, remove_extension, chop_extension: string -> string
(Filename.extension Str)
(Filename.remove_extension Str)
(Filename.chop_extension Str)

// is_relative, is_implicit: string -> bool
(Filename.is_relative Str)
(Filename.is_implicit Str)

// check_suffix: string -> string -> bool
(Filename.check_suffix Str Str)
(Filename.check_suffix Str Filename.dir_sep)

// chop_suffix: string -> string -> string
(Filename.chop_suffix Str Str)

// quote: string -> string
(Filename.quote Str)
(Filename.quote Filename.current_dir_name)

// get_temp_dir_name: unit -> string
(Filename.get_temp_dir_name Unit)

// temp_file: string -> string -> string
(Filename.temp_file Str Str)

// Chaining: concat returns string
((=) (Filename.concat Str Str) Str)
(Filename.basename (Filename.concat Str Str))
(Filename.dirname (Filename.concat Str Str))
(Filename.extension (Filename.concat Str Str))
(Filename.is_relative (Filename.concat Str Str))
(Filename.quote (Filename.concat Str Str))
(Filename.concat (Filename.dirname Str) (Filename.basename Str))
(Filename.concat Filename.current_dir_name (Filename.basename Str))
(Filename.concat (Filename.get_temp_dir_name Unit) Str)
(Filename.concat (Filename.get_temp_dir_name Unit) (Filename.temp_file Str Str))
(Filename.concat (Filename.dirname Str) (Filename.concat Filename.dir_sep (Filename.basename Str)))

// basename/dirname return string
((=) (Filename.basename Str) Str)
((=) (Filename.dirname Str) Str)
((^) (Filename.basename Str) Str)
((^) (Filename.dirname Str) Filename.dir_sep)
(Filename.is_relative (Filename.dirname Str))
(Filename.is_relative (Filename.basename Str))
(Filename.check_suffix Str (Filename.extension Str))
(Filename.extension (Filename.basename Str))
(Filename.remove_extension (Filename.basename Str))

// extension/remove_extension/chop_extension return string
((=) (Filename.extension Str) Str)
((^) Str (Filename.extension Str))
(Filename.concat (Filename.remove_extension Str) (Filename.extension Str))
(Filename.check_suffix Str (Filename.extension Str))
(Filename.is_relative (Filename.remove_extension Str))

// quote returns string
((=) (Filename.quote Str) Str)
((^) (Filename.quote Str) Str)
(Filename.concat (Filename.quote Str) Str)

// get_temp_dir_name returns string
((=) (Filename.get_temp_dir_name Unit) Str)
(Filename.basename (Filename.get_temp_dir_name Unit))
(Filename.is_relative (Filename.get_temp_dir_name Unit))

// temp_file returns string
((=) (Filename.temp_file Str Str) Str)
(Filename.basename (Filename.temp_file Str Str))
(Filename.dirname (Filename.temp_file Str Str))
(Filename.extension (Filename.temp_file Str Str))

// is_relative/is_implicit/check_suffix return bool
((=) (Filename.is_relative Str) true)
((=) (Filename.is_implicit Str) false)
((=) (Filename.check_suffix Str Str) true)
(not (Filename.is_relative Str))
(not (Filename.check_suffix Str Str))

// Invalid
(Filename.concat Num Str)
(Filename.basename Num)
(Filename.is_relative Num)
(Filename.check_suffix Str Num)
(Filename.extension Num)
