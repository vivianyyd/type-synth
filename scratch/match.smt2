(set-logic HORN)

(declare-datatype Color ( ( red ) ( green ) ( blue ) ))

(assert (forall ((c Color)) 
    (match c ((red true) (green true) (blue false)))))

(check-sat)

;(assert (forall ((c Color)) 
;    ( 
;    ite (c is red) 
;        (true)
;        (ite (c is green) 
;            (true)
;            (ite (c is blue) 
;                (true)
;                (false)))
;    )
;    ))    

;(ite (q1 t) (let ((x11 (s11 t)) · · · (x1k1 (s1k1 t))) t1)
;    (ite (q2 t) (let ((x21 (s21 t)) · · · (x2k2 (s2k2 t))) t2)
;    (ite (qm t) (let ((xm,1 (sm,1 t)) · · · (xm,km (sm,km  t))) tm)
;    (let ((xm+1,1 (sm+1,1 t)) · · · (xm+1,km+1 (sm+1,km+1    t))) tm+1) · · · )

