(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ (pow a 2) (pow b 2) (pow c 2)) 12))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 9 c) (* 9 (pow c 3)) (* 12 (pow b 3)) (* 12 a (pow c 2))) -1) (pow (+ (* 9 (pow c 3)) (* 12 (pow b 3)) (* 9 b c) (* 12 a (pow c 2))) 2)) (* -8 (pow a 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* -8 (pow b 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* -8 (pow c 2) (pow (+ (* 3 (pow a 2)) (* 3 (pow b 2)) (* 3 (pow c 2))) (/ 1 2))) (* 12 c (pow a 2)) (* 18 b (pow a 2))) 0)))
(check-sat)
(get-model)
(exit)