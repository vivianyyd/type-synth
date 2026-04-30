// 0_basics.types, 14_stdout.types, 17_out.types, 21_termination.types

(at_exit print_newline)
(at_exit flush_all)
(at_exit (fun u1 -> print_newline u1))
(at_exit (fun u2 -> flush_all u2))
(at_exit (fun u3 -> ignore (print_newline u3)))

(at_exit succ)
(at_exit print_string)
(at_exit print_int)
