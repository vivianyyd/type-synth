(set-logic HORN)

(declare-datatypes ((type 0) (tlist 0)) ((
    (lab (l Int) (p tlist))
    (fn (left type) (rite type))
    (var (n Int))
)( 
    (nil)
    (cons (hd type) (tl tlist) ) 
)))

; original, variable, replacement, result
(declare-fun issub (type Int type type) Bool)

(assert (forall ( (t1 type) (t2 type) (v Int) (rep type) (r1 type) (r2 type)) 
    (=>
    (and (issub t1 v rep r1) (issub t2 v rep r2))
    (issub (fn t1 t2) v rep (fn r1 r2))
    )
))

(assert (forall ( (v Int) (rep type))
    (issub (var v) v rep rep)
))

(define-fun-rec allsub ((lst tlist) (v Int) (rep type) (result tlist)) Bool
    (match lst (
        ( (nil) (
            match result (
                ((nil) true)
                ((cons _ _) false)
            )
        ))
        ((cons hd tl) (
            match result (
                ((nil) false)
                ((cons rhd rtl) (and (issub hd v rep rhd) (allsub tl v rep rtl)))
            )
        ))
    ))
)

(assert (forall ( (l Int) (p tlist) (v Int) (rep type) (psub tlist)) 
    (=>
    (allsub p v rep psub)
    (issub (lab l p) v rep (lab l psub))
    )
))

;(define-fun moregen ((t1 type) (t2 type)) Bool
;    (exists ((v Int) (rep type)) (issub t1 v rep t2))
;)



(check-sat)
