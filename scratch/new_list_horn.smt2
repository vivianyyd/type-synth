(set-logic HORN)

(declare-datatype list ( 
    ( nil)
    (cons (hd Int) (tl list) ) 
) )

(declare-fun C (list list list) Bool)

(define-fun len ( ( l list) ) Int 
    (- (_size l) 1 ) 
)

(assert (forall ( ( y list) ) (C nil y y) ) )

(assert (forall ( ( x list) (y list) (r list) (i Int) )
(=> (C x y r)
(C (cons i x) y (cons i r) ) ) ) )

(assert (forall ( ( x list) (y list) (r list) )
(=> (and (not (= r nil) ) (C x y r) )
(or (= (hd r) (hd x) )
(= (hd r) (hd y) ) ) ) ) )

(assert (forall ( ( x list) (y list) (r list) )
(=> (C x y r)
(= (len r) (+ (len x) (len y) ) ) ) ) )

(check-sat)
