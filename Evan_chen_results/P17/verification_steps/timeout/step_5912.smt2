(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 90 c (pow (+ (* (/ 1 2) a) (* (/ 1 2) b)) 2)) (* 100 (pow b 3) (pow c 2)) (* 140 (pow a 2) (pow b 3)) (* 140 (pow b 2) (pow c 3)) (* 380 (pow a 3) (pow c 2))) -1) (pow (+ (* 90 c (pow (+ (* (/ 1 2) a) (* (/ 1 2) b)) 3)) (* 100 (pow b 3) (pow c 2)) (* 140 (pow a 2) (pow b 3)) (* 140 (pow b 2) (pow c 3)) (* 380 (pow a 3) (pow c 2))) 2)) (* -760 a (pow c 4)) (* -760 b (pow a 4)) (* -745 c (pow b 4)) (* -152 a (pow b 4)) (* -152 b (pow c 4)) (* -140 (pow a 2) (pow c 3)) (* -140 (pow a 3) (pow b 2)) (* -137 c (pow a 4)) (* 672 a b (pow c 3)) (* 732 a c (pow b 3)) (* 732 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)