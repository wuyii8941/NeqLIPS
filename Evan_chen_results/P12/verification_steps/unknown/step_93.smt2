(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 6 (* (pow (* 2 (pow (* 2 (pow (+ a c) -2)) (+ 1 (* a c))) (pow (+ 1 (* b c)) 2) (pow (+ a b) -2) (pow (+ b c) -4) (+ 1 (* a b))) (pow (+ 4 (* a c)) -1)) (+ -4 (* -1 a c)))) 0)))
(check-sat)
(get-model)
(exit)