(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 6 (* -2 (pow (+ a b) -2)) (* -2 (pow (+ a c) -2)) (* -2 (pow (+ b c) -2)) (* (pow (* (/ 64 25) (pow b 2) (pow c 2) (pow (* 2 b) (* a (pow (+ a b) -2))) (pow (* c (pow (+ a c) -2)) (* 2 a)) (pow (+ 1 (pow (+ b c) 4)) -2)) (pow (+ 2 (* 2 a) (* a (pow (+ a b) -2))) -1)) (+ -2 (* -2 a) (* -1 a (pow (+ a b) -2))))) 0)))
(check-sat)
(get-model)
(exit)