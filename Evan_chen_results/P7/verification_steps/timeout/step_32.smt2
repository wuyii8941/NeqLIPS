(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (* -1 (pow a 2)) (* -1 (pow b 2)) (* -1 (pow c 2)) (* b (pow (* a b c) (pow 3 -1))) (* c (pow (* a b c) (pow 3 -1))) (* (pow (+ 2 (* 2 (pow a (/ 2 3)) (pow b (/ 2 3)) (pow c (/ 2 3)))) -1) (pow (+ a (* (pow a (/ 2 3)) (pow b (/ 2 3)) (pow c (/ 2 3)))) 2))) 0)))
(check-sat)
(get-model)
(exit)