(set-logic HORN)

;TODO these are mutually recursive
(declare-datatypes ((type 0) (tlist 0))(
    ((lab (l Int) (p tlist))
     (fn (left type) (rite type))
     (var (n Int)))
    ((nil) (cons (hd type) (tl tlist) ) )))

(define-funs-rec 
    ((sub ((t type) (v Int) (r type)) type) 
    (allsub ((lst tlist) (v Int) (rep type)) tlist))
    (
        (match t (
            ((lab l p) ( lab l (allsub p v rep) ))
            ((fn l r) (fn (sub l v rep) (sub r v rep)))
            ((var n) (ite () () ())) ; TODO
        ))
        ; ----------------------
        (match lst (
            ( (nil) ( nil ))
            ((cons hd tl) (cons (sub hd v rep) (allsub tl v rep)))
        ))
    )
)

; SUBSTITUTION IN FUNCTIONS
(assert (forall ( (t1 type) (t2 type) (v Int) (rep type) (r1 type) (r2 type)) 
    (=>
    (and (issub t1 v rep r1) (issub t2 v rep r2))
    (issub (fn t1 t2) v rep (fn r1 r2))
    )
))

; SUBSTITUTION IN VARIABLES
; TODO is there something with variable capture or something I need to care about
(assert (forall ( (v Int) (rep type))
    (issub (var v) v rep rep)
))

; SUBSTITUTION IN LABELS
(assert (forall ( (l Int) (p tlist) (v Int) (rep type) (psub tlist)) 
    (=>
    (allsub p v rep psub)
    (issub (lab l p) v rep (lab l psub))
    )
))

(define-fun moregen ((t1 type) (t2 type)) Bool
    (exists ((v Int) (rep type)) (issub t1 v rep t2))
)



(check-sat)
