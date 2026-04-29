// 0-basics.types, 1-comparison.types, 12-list.types

(@ [] [])
(@ (cons Num []) [])
(@ [] (cons Num []))
(@ (cons Num []) (cons Num []))
(@ (cons Str []) (cons Str []))
(@ (cons true []) (cons true []))

(@ (cons Num (cons Num [])) (cons Num []))
(@ (cons Str []) (cons Str (cons Str [])))
(@ [] (cons Char (cons Char [])))

(@ (@ (cons Num []) []) (cons Num []))
(@ (cons Num []) (@ [] (cons Num [])))

(= (@ [] []) [])

(@ (cons Num []) (cons Str []))
(@ (cons true []) (cons Num []))
(@ (cons Char []) (cons Str []))

// @ returns a list: use as argument to @ or cons
(@ (@ (cons Num []) (cons Num [])) (cons Num []))
(@ (cons Num []) (@ (cons Num []) (cons Num [])))
(@ (@ (cons Str []) (cons Str [])) (@ (cons Str []) []))
(@ (@ [] []) (@ (cons true []) (cons true [])))

// cons applied to output of @
(cons Num (@ (cons Num []) (cons Num [])))
(cons Str (@ [] (cons Str [])))

// @ result used to show element type constraint
(= (@ (cons Num []) []) (cons Num []))
(= (@ [] (cons Str [])) (cons Str []))

// longer chains: three appends
(@ (@ (@ (cons Num []) (cons Num [])) (cons Num [])) (cons Num []))
(@ (cons Str []) (@ (cons Str []) (@ (cons Str []) [])))

// invalid: appending lists of different element types, one side from @
(@ (@ (cons Num []) []) (cons Str []))
(@ (cons true []) (@ (cons Num []) []))
