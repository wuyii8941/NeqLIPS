(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -2 a (pow b 8)) (* -2 b (pow c 8)) (* -2 c (pow a 8)) (* a (pow b 3) (pow c 5)) (* a (pow c 3) (pow (+ (/ 8 13) (* (/ 5 13) b)) 13)) (* b (pow a 3) (pow c 5)) (* c (pow a 3) (pow b 5)) (* 2 (pow a 5) (pow b 2) (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)