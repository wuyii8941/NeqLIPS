(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (+ (* -1 a (pow c 4)) (* -1 b (pow a 4)) (* -1 c (pow b 4)) (* a b (pow c 3)) (* a c (pow b 3)) (* b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)