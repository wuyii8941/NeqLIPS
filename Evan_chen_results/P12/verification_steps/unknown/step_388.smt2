(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 6 (* (pow (+ a c) -2) (+ -2 (* -2 a c))) (* (pow (+ b c) -2) (+ -2 (* -2 b c))) (* (pow (* 2 (pow (* 2 b) a)) (pow (+ 1 a) -1)) (pow (+ a b) -2) (+ -1 (* -1 a)))) 0)))
(check-sat)
(get-model)
(exit)