(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ -1 (* a b (pow (+ (* a b) (* 2 (pow a (/ 5 2)) (pow b (/ 5 2)))) -1)) (* a c (pow (+ (pow c 5) (* 2 (pow a 3) (pow c (/ 1 2)))) -1)) (* b c (pow (+ (pow b 5) (pow c 5) (* b c)) -1))) 0)))
(check-sat)
(get-model)
(exit)