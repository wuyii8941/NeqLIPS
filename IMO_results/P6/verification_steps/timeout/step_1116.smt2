(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -14801 (pow b 4)) (* -11585 (pow a 4)) (* (pow (+ (* 11562 (pow a 2)) (* 11108 b (pow a 3)) (* 45188 a (pow b 3))) -1) (pow (+ (* 11108 b (pow a 3)) (* 11562 b (pow a 2)) (* 45188 a (pow b 3))) 2)) (* -27648 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -13824 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)