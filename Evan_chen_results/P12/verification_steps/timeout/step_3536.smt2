(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 6 (* -2 (pow (+ (/ 1 2) (* (/ 1 2) (pow (+ a b) 4))) -1)) (* -2 (pow (+ (/ 1 2) (* (/ 1 2) (pow (+ b c) 4))) -1)) (* -4 (pow (+ 1 (pow (+ a c) 2)) -1) (pow (+ a c) -1)) (* -16 b c (pow (+ 15662508866454208207582488492733 (* 5 (pow (+ b c) 4))) -1)) (* -2 a b (pow (+ a b) -2)) (* -2 a c (pow (+ a c) -2))) 0)))
(check-sat)
(get-model)
(exit)