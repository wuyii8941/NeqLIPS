(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -56555072 (pow b 4)) (* -43382336 (pow a 4)) (* (pow (+ (* 416232 (pow (+ (* 2 a) (* 2 b)) 4)) (* 61777664 b (pow a 3))) 2) (pow (+ (* 6659712 (pow (+ (* 2 a) (* 2 b)) 4)) (* 61777664 b (pow a 3))) -1)) (* -113246208 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -56623104 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 201369344 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)