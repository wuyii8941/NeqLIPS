(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -56555072 (pow b 4)) (* -43382336 (pow a 4)) (* -169869312 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 6659712 (pow a 2) (pow b 2)) (* 61777664 b (pow a 3)) (* 201369344 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)