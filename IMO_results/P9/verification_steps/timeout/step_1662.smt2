(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ -8 (pow (* (+ (pow (+ a b (* 2 c)) 2) (pow (+ a c (* 2 b)) 2)) (+ (* (pow (+ a b (* 2 c)) 2) (pow (+ (pow a 2) (pow b 2) (* 2 (pow c 2)) (* 2 a b)) -2)) (* (pow (+ a c (* 2 b)) 2) (pow (+ (pow a 2) (pow c 2) (* 2 (pow b 2)) (* 2 a c)) -2)))) (/ 1 2)) (* (pow (+ (* 2 (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1) (+ b c)) (* 8 a (pow (+ (pow b 2) (pow c 2) (* 2 (pow a 2)) (* 2 b c)) -1))) 2) (+ (* (/ 1 5) (pow a 2)) (* (/ 1 10) (pow b 2)) (* (/ 1 10) (pow c 2)) (* (/ 1 5) b c)))) 0)))
(check-sat)
(get-model)
(exit)