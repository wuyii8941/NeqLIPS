(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ -64 (* 3 (pow (+ (pow (+ a b) 2) (* 2 (pow c 2))) -2) (pow (+ a b (* 2 c)) 4)) (* 3 (pow (+ (pow (+ a c) 2) (* 2 (pow b 2))) -2) (pow (+ a c (* 2 b)) 4)) (* 6 (pow (+ 4 (pow (+ b c) 2)) -1) (pow (+ (pow (+ b c) 2) (* 2 (pow a 2))) -2) (pow (+ (pow (+ b c) 2) (* 4 a)) 2) (pow (+ b c (* 2 a)) 2))) 0)))
(check-sat)
(get-model)
(exit)