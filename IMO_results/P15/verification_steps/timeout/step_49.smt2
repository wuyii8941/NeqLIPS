(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (pow (+ a b c) 2)) 4))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (* (/ 1 3) (+ a b) (+ (pow (+ a c) 6) (pow (+ (* -1 (+ 4 (* 4 a b)) (+ (* (pow (+ a c) 2) (+ 1 (* b c))) (* (pow (+ b c) 2) (+ 1 (* a c))))) (* 9 (pow (+ a b) 2) (pow (+ a c) 2) (pow (+ b c) 2))) 3) (* (pow (+ a b) 3) (pow (+ b c) 6)))) 0)))
(check-sat)
(get-model)
(exit) 0)))
(check-sat)
(get-model)
(exit)