(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 2 3) (pow b 3) (pow c 3) (* -1 (pow (+ a b c) 3)) (* (/ 1 3) (pow a 9)) (* 24 a b c)) 0)))
(check-sat)
(get-model)
(exit)