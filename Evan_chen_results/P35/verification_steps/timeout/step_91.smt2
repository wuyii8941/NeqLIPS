(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (* a b) (* a c) (* b c)) 1))
(assert (<= (* a b c) (* (/ 1 9) (pow 3 (/ 1 2)))))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ -1 (* 3 a b c (pow (+ (* 2 a) (* 2 b) (* 2 c) (* (/ 1 3) (pow a -1)) (* (/ 1 3) (pow b -1)) (* (/ 1 3) (pow c -1))) (pow 3 -1)))) 0)))
(check-sat)
(get-model)
(exit)