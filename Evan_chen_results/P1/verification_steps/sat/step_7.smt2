(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (/ 2 3) (* -1 (pow a 2)) (* -1 (pow b 2)) (* -1 (pow c 2)) (* (/ 1 3) (pow (+ (* a b) (* b c)) 3)) (* a c)) 0)))
(check-sat)
(get-model)
(exit)