(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (pow a 3) (pow b 3) (pow c 3) (* a b c)) 4))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ a b c) -1) (pow (+ (* (/ 5 2) (pow a 3)) (* (/ 5 2) (pow b 3)) (* (/ 5 2) (pow c 3)) (* (/ 3 2) a b c)) 2)) (* (pow (+ (pow (+ (* 5 (pow a 2)) (* b c)) (/ 4 3)) (pow (+ (* 5 (pow b 2)) (* a c)) (/ 4 3)) (pow (+ (* 5 (pow c 2)) (* a b)) (/ 4 3))) (/ 3 2)) (pow (+ (* (pow (+ a b) 2) (pow (+ a c) 2)) (* (pow (+ a b) 2) (pow (+ b c) 2)) (* (pow (+ a c) 2) (pow (+ b c) 2))) (/ -1 2)) (+ (* (/ -1 4) (pow a 3)) (* (/ -1 4) (pow b 3)) (* (/ -1 4) (pow c 3)) (* (/ -1 4) a b c)))) 0)))
(check-sat)
(get-model)
(exit)