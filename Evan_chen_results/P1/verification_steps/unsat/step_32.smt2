(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (* (/ -1 2) (pow b 2)) (* a c) (* b c) (* -1 (pow (+ (/ 1 2) (pow c 2)) -1) (pow (+ (pow c 2) (* (/ 1 2) a)) 2))) 0)))
(check-sat)
(get-model)
(exit)