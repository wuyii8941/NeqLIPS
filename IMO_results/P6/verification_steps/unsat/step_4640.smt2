(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -113110144 (pow b 4)) (* -86764672 (pow a 4)) (* 832464 (pow (+ a b) 4)) (* -226492416 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -113246208 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 145775753948718561121796096 (pow a 3) (pow b 3) (pow (+ (* 123555328 b) (* 402738688 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)