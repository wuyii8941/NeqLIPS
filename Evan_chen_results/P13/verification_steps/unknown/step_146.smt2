(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (* a b c d) 1))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (>= d 0))
(assert (not (<= (+ a b c d (* (pow (* (pow c (* 3 c d)) (pow (* b c) (pow b 3)) (pow (* b (pow a 3)) a)) (pow (+ a (pow b 3) (* c d)) -1)) (+ (* -1 a) (* -1 (pow b 3)) (* -1 c d))) (* -1 a (pow d 4))) 0)))
(check-sat)
(get-model)
(exit)