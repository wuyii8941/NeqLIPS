(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (/ 1 2) (* -1 (pow a 2)) (* -1 (pow b 2)) (* -1 (pow c 2)) (* a c) (* b c) (* (/ 1 2) (pow a 2) (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)