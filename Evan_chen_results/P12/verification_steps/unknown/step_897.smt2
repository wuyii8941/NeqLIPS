(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 6 (* -2 (pow (+ a b) -2)) (* -2 (pow (+ a c) -2)) (* -2 (pow (+ b c) -2)) (* (pow (* (pow (* 2 a (pow (+ (/ 1 2) (* (/ 1 2) (pow (+ a c) 4))) -1)) c) (pow (* 2 c (pow (+ b c) -2)) b)) (pow (+ b c) -1)) (+ (* -1 b) (* -1 c))) (* -2 a b (pow (+ a b) -2))) 0)))
(check-sat)
(get-model)
(exit)