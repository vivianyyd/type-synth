;(set-logic HORN)

(declare-datatypes ((type 0) (tlist 0))(
    ((lab (l Int) (p tlist))
     (fn (left type) (rite type))
     (var (n Int)))
    ((nil) (cons (hd type) (tl tlist) ) )))

(define-funs-rec 
    ((sub ((t type) (v Int) (rep type)) type) 
    (allsub ((lst tlist) (v Int) (rep type)) tlist))
    ;
    ((match t (
        ((lab l p) ( lab l (allsub p v rep) ))
        ((fn l r) (fn (sub l v rep) (sub r v rep)))
        ((var n) (ite (= v n) rep t))
    ))
    ;
    (match lst (
        ( (nil) nil)
        ((cons hd tl) (cons (sub hd v rep) (allsub tl v rep)))
    )))
)

(define-fun moregen ((t1 type) (t2 type)) Bool
    (exists ((v Int) (rep type)) (= t2 (sub t1 v rep)))
)

(assert (moregen (var 0) (var 1)))

(check-sat)
