(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (+ (* a b) (* a c) (* b c) (* (pow (* (pow b b) (pow c c)) (pow (+ b c (pow a 2)) -1)) (+ (* -1 b) (* -1 c) (* -1 (pow a 2))))) 0)))
(check-sat)
(get-model)
(exit)