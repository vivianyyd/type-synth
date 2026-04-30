// 0_basics.types, 1_comparison.types, 13_io.types, 18_in.types

(open_in Str)
(open_in_bin Str)

(input_char stdin)
(input_line stdin)
(input_byte stdin)
(input_binary_int stdin)
(really_input_string stdin Num)

(seek_in stdin Num)
(pos_in stdin)
(in_channel_length stdin)
(close_in_noerr stdin)
(set_binary_mode_in stdin true)
(set_binary_mode_in stdin false)

(input_char (open_in Str))
(input_line (open_in Str))
(close_in_noerr (open_in Str))
(really_input_string (open_in Str) Num)

(= (input_line stdin) Str)
(= (input_byte stdin) Num)

(input_char stdout)
(input_line stdout)
(really_input_string stdin Str)
(set_binary_mode_in stdin Num)
(open_in Num)

// open_in returns in_channel: use in all input operations
(input_char (open_in Str))
(input_line (open_in Str))
(input_byte (open_in Str))
(input_binary_int (open_in_bin Str))
(really_input_string (open_in Str) Num)
(seek_in (open_in Str) Num)
(pos_in (open_in Str))
(in_channel_length (open_in Str))
(close_in_noerr (open_in Str))
(set_binary_mode_in (open_in Str) false)

// pos_in/in_channel_length return int: use in further input operations
(= (pos_in stdin) Num)
(= (in_channel_length stdin) Num)
(really_input_string stdin (in_channel_length stdin))
(seek_in stdin (pos_in stdin))
(= (pos_in (open_in Str)) Num)
(< (pos_in stdin) (in_channel_length stdin))

// input functions return values: use outputs further
(= (input_line stdin) Str)
(= (input_byte stdin) Num)
(= (input_binary_int stdin) Num)
(= (input_char stdin) Char)
(= (input_line (open_in Str)) Str)
(= (really_input_string stdin Num) Str)

// chain: open_in, read, compare result
(= (input_line (open_in Str)) (input_line (open_in Str)))
(= (input_byte (open_in Str)) (input_byte (open_in Str)))
(really_input_string (open_in Str) (in_channel_length (open_in Str)))

// invalid: int/string outputs used where channel expected
(input_char (pos_in stdin))
(input_line (in_channel_length stdin))
