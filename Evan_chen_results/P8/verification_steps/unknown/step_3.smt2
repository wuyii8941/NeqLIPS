(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (+ (* (pow a 3) (pow c 4)) (* (pow a 4) (pow b 3)) (* (pow b 4) (pow c 3)) (* (pow (+ (pow b 7) (pow c 7)) (pow (+ 1 (pow a 7)) -1)) (+ -1 (* -1 (pow a 7))))) 0)))
(check-sat)
(get-model)
(exit)