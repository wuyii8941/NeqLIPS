(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1 (pow (+ (* 4384 c (pow a 2)) (* 4480 (pow a 2) (pow c 3)) (* 4480 (pow a 3) (pow b 2))) -1) (pow (+ (* 4384 c (pow a 3)) (* 4480 (pow a 2) (pow c 3)) (* 4480 (pow a 3) (pow b 2))) 2)) (* -24320 a (pow c 4)) (* -24320 b (pow a 4)) (* -23840 c (pow b 4)) (* -4864 a (pow b 4)) (* -4864 b (pow c 4)) (* 180 c (pow (+ a b) 4)) (* 3200 (pow b 3) (pow c 2)) (* 4480 (pow a 2) (pow b 3)) (* 4480 (pow b 2) (pow c 3)) (* 12160 (pow a 3) (pow c 2)) (* 21504 a b (pow c 3)) (* 23424 a c (pow b 3)) (* 23424 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)