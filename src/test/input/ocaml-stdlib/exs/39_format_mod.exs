// 0_basics.types, 1_comparison.types, 4_arith.types, 13_io.types, 17_out.types, 39_format_mod.types

// Formatter constants
Format.std_formatter
Format.err_formatter
Format.str_formatter

// Creating formatters
(Format.formatter_of_out_channel stdout)
(Format.formatter_of_out_channel stderr)

// flush_str_formatter: unit -> string
(Format.flush_str_formatter Unit)

// get_str_formatter: unit -> formatter
(Format.get_str_formatter Unit)

// pp_print_*: formatter -> value -> unit
(Format.pp_print_string Format.std_formatter Str)
(Format.pp_print_int Format.std_formatter Num)
(Format.pp_print_float Format.std_formatter Flt)
(Format.pp_print_char Format.std_formatter Char)
(Format.pp_print_bool Format.std_formatter true)
(Format.pp_print_bool Format.std_formatter false)
(Format.pp_print_nothing Format.std_formatter Unit)
(Format.pp_print_text Format.std_formatter Str)
(Format.pp_print_string Format.err_formatter Str)
(Format.pp_print_int Format.err_formatter Num)
(Format.pp_print_string (Format.formatter_of_out_channel stdout) Str)
(Format.pp_print_int (Format.formatter_of_out_channel stdout) Num)

// pp_print_newline, pp_print_space, pp_print_cut: formatter -> unit -> unit
(Format.pp_print_newline Format.std_formatter Unit)
(Format.pp_print_space Format.std_formatter Unit)
(Format.pp_print_cut Format.std_formatter Unit)
(Format.pp_force_newline Format.std_formatter Unit)
(Format.pp_print_if_newline Format.std_formatter Unit)

// Box management: formatter -> ... -> unit
(Format.pp_open_box Format.std_formatter Num)
(Format.pp_close_box Format.std_formatter Unit)
(Format.pp_open_hbox Format.std_formatter Unit)
(Format.pp_open_vbox Format.std_formatter Num)
(Format.pp_open_hvbox Format.std_formatter Num)
(Format.pp_open_hovbox Format.std_formatter Num)

// Margin/indentation: getters return int
(Format.pp_get_margin Format.std_formatter Unit)
(Format.pp_get_max_indent Format.std_formatter Unit)

// Margin/indentation: setters
(Format.pp_set_margin Format.std_formatter Num)
(Format.pp_set_max_indent Format.std_formatter Num)

// Tag printing
(Format.pp_get_print_tags Format.std_formatter Unit)
(Format.pp_get_mark_tags Format.std_formatter Unit)
(Format.pp_set_tags Format.std_formatter true)
(Format.pp_set_print_tags Format.std_formatter false)
(Format.pp_set_mark_tags Format.std_formatter true)

// Break hints
(Format.pp_print_break Format.std_formatter Num Num)
(Format.pp_set_tab Format.std_formatter Unit)
(Format.pp_print_tab Format.std_formatter Unit)

// pp_set_formatter_out_channel
(Format.pp_set_formatter_out_channel Format.std_formatter stdout)

// Chaining: formatter_of_out_channel output used in pp_print_*
(Format.pp_print_string (Format.formatter_of_out_channel stdout) Str)
(Format.pp_print_int (Format.formatter_of_out_channel stderr) Num)
(Format.pp_print_bool (Format.formatter_of_out_channel stdout) true)
(Format.pp_open_box (Format.formatter_of_out_channel stdout) Num)
(Format.pp_close_box (Format.formatter_of_out_channel stdout) Unit)

// get_str_formatter output used in pp_print_*
(Format.pp_print_string (Format.get_str_formatter Unit) Str)
(Format.pp_print_int (Format.get_str_formatter Unit) Num)

// pp_get_margin/pp_get_max_indent return int
((=) (Format.pp_get_margin Format.std_formatter Unit) Num)
((=) (Format.pp_get_max_indent Format.std_formatter Unit) Num)
(succ (Format.pp_get_margin Format.std_formatter Unit))
((<) (Format.pp_get_margin Format.std_formatter Unit) Num)
(Format.pp_set_margin Format.std_formatter (Format.pp_get_margin Format.std_formatter Unit))
(Format.pp_set_max_indent Format.std_formatter (Format.pp_get_max_indent Format.std_formatter Unit))
(Format.pp_open_box Format.std_formatter (Format.pp_get_margin Format.std_formatter Unit))
(Format.pp_print_break Format.std_formatter (Format.pp_get_margin Format.std_formatter Unit) Num)

// pp_get_print_tags/pp_get_mark_tags return bool
((=) (Format.pp_get_print_tags Format.std_formatter Unit) true)
(not (Format.pp_get_mark_tags Format.std_formatter Unit))
(Format.pp_set_print_tags Format.std_formatter (Format.pp_get_print_tags Format.std_formatter Unit))

// flush_str_formatter returns string
((=) (Format.flush_str_formatter Unit) Str)
(Format.pp_print_string Format.std_formatter (Format.flush_str_formatter Unit))

// Unit return: chain print into print_newline
(Format.pp_print_newline Format.std_formatter (Format.pp_print_string Format.std_formatter Str))
(Format.pp_print_newline Format.std_formatter (Format.pp_print_int Format.std_formatter Num))
(Format.pp_print_space Format.std_formatter (Format.pp_print_string Format.std_formatter Str))
(Format.pp_close_box Format.std_formatter (Format.pp_open_box Format.std_formatter Num))

// Invalid
(Format.pp_print_int Format.std_formatter Str)
(Format.pp_print_string Format.std_formatter Num)
(Format.pp_print_bool Format.std_formatter Num)
(Format.pp_get_margin Num Unit)
(Format.pp_set_margin Format.std_formatter Str)
