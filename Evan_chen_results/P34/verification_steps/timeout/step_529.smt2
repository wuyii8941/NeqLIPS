(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (pow a 2) (pow b 2) (pow c 2)) 12))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 12 (pow b 3)) (* -16 (pow a 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* -16 (pow b 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* -16 (pow c 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* 6 c (pow (+ b c) 2)) (* 12 c (+ (pow a 2) (pow c 2))) (* 24 c (pow a 2)) (* 24 c (pow b 2)) (* 36 b (pow a 2))) 0)))
(check-sat)
(get-model)
(exit)