(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 2) (* (/ -1 9) (pow a 2) (pow b 2) (pow c 2) (pow (+ (pow (* (pow a 3) (+ b c)) (* 1 (pow 3 -1))) (pow (* (pow b 3) (+ a c)) (* 1 (pow 3 -1))) (pow (* (pow c 3) (+ a b)) (* 1 (pow 3 -1)))) 3))) 0)))
(check-sat)
(get-model)
(exit)