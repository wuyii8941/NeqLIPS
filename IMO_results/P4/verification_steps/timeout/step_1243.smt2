(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ -1 (* a b (pow (+ (pow b 5) (* 2 (pow a 3) (pow b (/ 1 2)))) -1)) (* a c (pow (+ (pow a 5) (pow c 5) (* a c)) -1)) (* b (pow (+ (* 3 (pow b 5)) (* 3 (pow c 5)) (* 3 b c)) -1) (+ 2 (pow c 3)))) 0)))
(check-sat)
(get-model)
(exit)