// 0-basics.types, 1-comparison.types, 7-str.types, 37-filename-mod.types

// String constants
current_dir_name
parent_dir_name
dir_sep
null

// concat: string -> string -> string
(concat Str Str)
(concat current_dir_name Str)
(concat Str parent_dir_name)
(concat dir_sep Str)

// basename, dirname: string -> string
(basename Str)
(dirname Str)

// extension, remove_extension, chop_extension: string -> string
(extension Str)
(remove_extension Str)
(chop_extension Str)

// is_relative, is_implicit: string -> bool
(is_relative Str)
(is_implicit Str)

// check_suffix: string -> string -> bool
(check_suffix Str Str)
(check_suffix Str dir_sep)

// chop_suffix: string -> string -> string
(chop_suffix Str Str)

// quote: string -> string
(quote Str)
(quote current_dir_name)

// get_temp_dir_name: unit -> string
(get_temp_dir_name Unit)

// temp_file: string -> string -> string
(temp_file Str Str)

// Chaining: concat returns string
(= (concat Str Str) Str)
(basename (concat Str Str))
(dirname (concat Str Str))
(extension (concat Str Str))
(is_relative (concat Str Str))
(quote (concat Str Str))
(concat (dirname Str) (basename Str))
(concat current_dir_name (basename Str))
(concat (get_temp_dir_name Unit) Str)
(concat (get_temp_dir_name Unit) (temp_file Str Str))
(concat (dirname Str) (concat dir_sep (basename Str)))

// basename/dirname return string
(= (basename Str) Str)
(= (dirname Str) Str)
(^ (basename Str) Str)
(^ (dirname Str) dir_sep)
(is_relative (dirname Str))
(is_relative (basename Str))
(check_suffix Str (extension Str))
(extension (basename Str))
(remove_extension (basename Str))

// extension/remove_extension/chop_extension return string
(= (extension Str) Str)
(^ Str (extension Str))
(concat (remove_extension Str) (extension Str))
(check_suffix Str (extension Str))
(is_relative (remove_extension Str))

// quote returns string
(= (quote Str) Str)
(^ (quote Str) Str)
(concat (quote Str) Str)

// get_temp_dir_name returns string
(= (get_temp_dir_name Unit) Str)
(basename (get_temp_dir_name Unit))
(is_relative (get_temp_dir_name Unit))

// temp_file returns string
(= (temp_file Str Str) Str)
(basename (temp_file Str Str))
(dirname (temp_file Str Str))
(extension (temp_file Str Str))

// is_relative/is_implicit/check_suffix return bool
(= (is_relative Str) true)
(= (is_implicit Str) false)
(= (check_suffix Str Str) true)
(not (is_relative Str))
(not (check_suffix Str Str))

// Invalid
(concat Num Str)
(basename Num)
(is_relative Num)
(check_suffix Str Num)
(extension Num)
