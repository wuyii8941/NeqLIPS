(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (pow a 2) (pow b 2) (pow c 2)) 12))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 6 (pow b 3)) (* 6 (pow c 3)) (* (pow (* 9 (pow (* 8 a (pow 3 (/ 1 2)) (pow (+ (pow a 2) (pow b 2) (pow c 2)) (/ 1 2))) a) (pow (+ b c) 8) (pow (+ (pow a 2) (pow b 2) (pow c 2)) 2)) (pow (+ 4 a) -1)) (+ -4 (* -1 a))) (* 12 b (pow c 2)) (* 12 c (pow b 2)) (* 18 b (pow a 2)) (* 18 c (pow a 2))) 0)))
(check-sat)
(get-model)
(exit)