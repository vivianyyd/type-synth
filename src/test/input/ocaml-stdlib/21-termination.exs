// 0-basics.types, 14-stdout.types, 17-out.types, 21-termination.types

(at_exit print_newline)
(at_exit flush_all)
(at_exit (fun u1 -> print_newline u1))
(at_exit (fun u2 -> flush_all u2))
(at_exit (fun u3 -> ignore (print_newline u3)))

(at_exit succ)
(at_exit print_string)
(at_exit print_int)
