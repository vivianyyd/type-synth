// 0_basics.types, 1_comparison.types, 13_io.types, 17_out.types

(open_out Str)
(open_out_bin Str)

(flush stdout)
(flush stderr)
(flush (open_out Str))
(flush_all Unit)

(output_char stdout Char)
(output_string stdout Str)
(output_substring stdout Str Num Num)
(output_byte stdout Num)
(output_binary_int stdout Num)
(output_value stdout Num)
(output_value stdout Str)
(output_value stdout true)

(seek_out stdout Num)
(pos_out stdout)
(out_channel_length stdout)
(close_out stdout)
(close_out_noerr stdout)
(set_binary_mode_out stdout true)
(set_binary_mode_out stdout false)

(output_char (open_out Str) Char)
(output_string (open_out Str) Str)
(close_out (open_out Str))

(output_char stdout Num)
(output_string stdout Num)
(flush stdin)
(output_byte stdout Str)
(output_binary_int stdout Str)
(open_out Num)
(seek_out stdout Str)

// open_out returns out_channel: use in all output operations
(output_string (open_out Str) Str)
(output_char (open_out Str) Char)
(output_byte (open_out_bin Str) Num)
(output_binary_int (open_out_bin Str) Num)
(flush (open_out Str))
(close_out (open_out Str))
(close_out_noerr (open_out Str))
(seek_out (open_out Str) Num)
(pos_out (open_out Str))
(out_channel_length (open_out Str))
(set_binary_mode_out (open_out Str) true)

// pos_out/out_channel_length return int: use in output operations
(= (pos_out stdout) Num)
(= (out_channel_length stdout) Num)
(output_byte stdout (pos_out stdout))
(seek_out stdout (pos_out stdout))
(output_binary_int stdout (out_channel_length stdout))
(= (pos_out (open_out Str)) Num)
(< (pos_out stdout) (out_channel_length stdout))

// chain: open, write, query position
(seek_out (open_out Str) (pos_out stdout))
(output_byte (open_out Str) (pos_out stdout))

// invalid: int outputs used where channel expected
(flush (pos_out stdout))
(output_string (out_channel_length stdout) Str)
