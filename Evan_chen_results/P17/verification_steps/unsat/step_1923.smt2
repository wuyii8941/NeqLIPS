(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -48640 a (pow c 4)) (* -48640 b (pow a 4)) (* -47320 c (pow b 4)) (* -9728 a (pow b 4)) (* -9728 b (pow c 4)) (* -8960 (pow a 2) (pow c 3)) (* -8960 (pow a 3) (pow b 2)) (* -8408 c (pow a 4)) (* 8960 (pow a 2) (pow b 3)) (* 8960 (pow b 2) (pow c 3)) (* 24320 (pow a 3) (pow c 2)) (* 2160 c (pow a 2) (pow b 2)) (* 3200 c (pow b 3) (+ 1 (pow c 2))) (* 43008 a b (pow c 3)) (* 48288 a c (pow b 3)) (* 48288 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)