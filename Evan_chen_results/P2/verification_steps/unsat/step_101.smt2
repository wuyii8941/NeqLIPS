(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (* -1 (pow a 4)) (* -1 (pow b 4)) (* -1 (pow c 4)) (* (pow (+ 1 (pow b 2) (* (pow a 2) (pow b 2))) -1) (pow (+ (* a c) (* c (pow b 2)) (* (pow a 2) (pow b 2))) 2))) 0)))
(check-sat)
(get-model)
(exit)