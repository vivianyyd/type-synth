(set-logic HORN)

( declare-datatype List ( par ( E )
    ( ( nil )
    ( cons ( hd E ) ( tl ( List E )) ))))

(declare-datatypes ((type 0) )(
    ((lab (l Int) (p (List type)))
     (fn (left type) (rite type))
     (var (n Int)))   ))

(define-funs-rec 
    ((sub ((t type) (v Int) (rep type)) type) 
    (allsub ((lst (List type)) (v Int) (rep type)) (List type)))
    ;
    ((match t (
        ((lab l p) ( lab l (allsub p v rep) ))
        ((fn l r) (fn (sub l v rep) (sub r v rep)))
        ((var n) (ite (= v n) rep t))
    ))
    ;
    (match lst (
        ( (nil)  ( as nil ( List type )) )
        ((cons hd tl) (cons (sub hd v rep) (allsub tl v rep)))
    )))
)

(declare-datatype binding (( b ( v Int ) ( t type) )))

(define-fun-rec unify ((param type) (arg type)) (List binding)
    ( match param (
        ((lab l p) (as nil ( List binding )) )
        ((fn l r) (as nil ( List binding ))  )
        ((var v) (cons (b v arg) (as nil ( List binding )) ))
    
    )
    )
)

; TODO define unify/more general explicitly

(check-sat)
