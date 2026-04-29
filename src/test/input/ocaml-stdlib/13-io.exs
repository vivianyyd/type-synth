// 0-basics.types, 1-comparison.types, 13-io.types, 17-out.types, 18-in.types

(output_string stdout Str)
(output_char stdout Char)
(output_byte stdout Num)
(output_binary_int stdout Num)
(output_value stdout Num)
(output_value stdout Str)
(output_value stdout true)
(flush stdout)
(flush stderr)
(pos_out stdout)
(out_channel_length stdout)

(input_char stdin)
(input_line stdin)
(input_byte stdin)
(input_binary_int stdin)
(really_input_string stdin Num)
(pos_in stdin)
(in_channel_length stdin)

(output_string stdin Str)
(input_char stdout)
(flush stdin)

// pos_out/out_channel_length return int: use in further output operations
(= (pos_out stdout) Num)
(= (out_channel_length stdout) Num)
(output_byte stdout (pos_out stdout))
(seek_out stdout (pos_out stdout))
(output_binary_int stdout (out_channel_length stdout))

// pos_in/in_channel_length return int: use in further input operations
(= (pos_in stdin) Num)
(= (in_channel_length stdin) Num)
(really_input_string stdin (in_channel_length stdin))
(seek_in stdin (pos_in stdin))

// input functions return values that can be compared
(= (input_line stdin) Str)
(= (input_byte stdin) Num)
(= (input_binary_int stdin) Num)

// invalid: int output used where channel expected
(flush (pos_out stdout))
(output_string (pos_in stdin) Str)
