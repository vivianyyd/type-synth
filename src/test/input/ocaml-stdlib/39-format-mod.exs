// 0-basics.types, 1-comparison.types, 4-arith.types, 13-io.types, 17-out.types, 39-format-mod.types

// Formatter constants
std_formatter
err_formatter
str_formatter

// Creating formatters
(formatter_of_out_channel stdout)
(formatter_of_out_channel stderr)

// flush_str_formatter: unit -> string
(flush_str_formatter Unit)

// get_str_formatter: unit -> formatter
(get_str_formatter Unit)

// pp_print_*: formatter -> value -> unit
(pp_print_string std_formatter Str)
(pp_print_int std_formatter Num)
(pp_print_float std_formatter Flt)
(pp_print_char std_formatter Char)
(pp_print_bool std_formatter true)
(pp_print_bool std_formatter false)
(pp_print_nothing std_formatter Unit)
(pp_print_text std_formatter Str)
(pp_print_string err_formatter Str)
(pp_print_int err_formatter Num)
(pp_print_string (formatter_of_out_channel stdout) Str)
(pp_print_int (formatter_of_out_channel stdout) Num)

// pp_print_newline, pp_print_space, pp_print_cut: formatter -> unit -> unit
(pp_print_newline std_formatter Unit)
(pp_print_space std_formatter Unit)
(pp_print_cut std_formatter Unit)
(pp_force_newline std_formatter Unit)
(pp_print_if_newline std_formatter Unit)

// Box management: formatter -> ... -> unit
(pp_open_box std_formatter Num)
(pp_close_box std_formatter Unit)
(pp_open_hbox std_formatter Unit)
(pp_open_vbox std_formatter Num)
(pp_open_hvbox std_formatter Num)
(pp_open_hovbox std_formatter Num)

// Margin/indentation: getters return int
(pp_get_margin std_formatter Unit)
(pp_get_max_indent std_formatter Unit)

// Margin/indentation: setters
(pp_set_margin std_formatter Num)
(pp_set_max_indent std_formatter Num)

// Tag printing
(pp_get_print_tags std_formatter Unit)
(pp_get_mark_tags std_formatter Unit)
(pp_set_tags std_formatter true)
(pp_set_print_tags std_formatter false)
(pp_set_mark_tags std_formatter true)

// Break hints
(pp_print_break std_formatter Num Num)
(pp_set_tab std_formatter Unit)
(pp_print_tab std_formatter Unit)

// pp_set_formatter_out_channel
(pp_set_formatter_out_channel std_formatter stdout)

// Chaining: formatter_of_out_channel output used in pp_print_*
(pp_print_string (formatter_of_out_channel stdout) Str)
(pp_print_int (formatter_of_out_channel stderr) Num)
(pp_print_bool (formatter_of_out_channel stdout) true)
(pp_open_box (formatter_of_out_channel stdout) Num)
(pp_close_box (formatter_of_out_channel stdout) Unit)

// get_str_formatter output used in pp_print_*
(pp_print_string (get_str_formatter Unit) Str)
(pp_print_int (get_str_formatter Unit) Num)

// pp_get_margin/pp_get_max_indent return int
(= (pp_get_margin std_formatter Unit) Num)
(= (pp_get_max_indent std_formatter Unit) Num)
(succ (pp_get_margin std_formatter Unit))
(< (pp_get_margin std_formatter Unit) Num)
(pp_set_margin std_formatter (pp_get_margin std_formatter Unit))
(pp_set_max_indent std_formatter (pp_get_max_indent std_formatter Unit))
(pp_open_box std_formatter (pp_get_margin std_formatter Unit))
(pp_print_break std_formatter (pp_get_margin std_formatter Unit) Num)

// pp_get_print_tags/pp_get_mark_tags return bool
(= (pp_get_print_tags std_formatter Unit) true)
(not (pp_get_mark_tags std_formatter Unit))
(pp_set_print_tags std_formatter (pp_get_print_tags std_formatter Unit))

// flush_str_formatter returns string
(= (flush_str_formatter Unit) Str)
(pp_print_string std_formatter (flush_str_formatter Unit))

// Unit return: chain print into print_newline
(pp_print_newline std_formatter (pp_print_string std_formatter Str))
(pp_print_newline std_formatter (pp_print_int std_formatter Num))
(pp_print_space std_formatter (pp_print_string std_formatter Str))
(pp_close_box std_formatter (pp_open_box std_formatter Num))

// Invalid
(pp_print_int std_formatter Str)
(pp_print_string std_formatter Num)
(pp_print_bool std_formatter Num)
(pp_get_margin Num Unit)
(pp_set_margin std_formatter Str)
