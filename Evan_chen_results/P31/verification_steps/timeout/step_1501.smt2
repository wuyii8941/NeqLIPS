(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 324 c (pow a 2)) (* 960 (pow b 3) (pow c 2)) (* 1344 (pow a 2) (pow b 3)) (* 1344 (pow b 2) (pow c 3)) (* 3648 (pow a 3) (pow c 2)) (* 3584 a b (pow c 3))) -1) (pow (+ (* 960 (pow b 3) (pow c 2)) (* 1344 (pow a 2) (pow b 3)) (* 1344 (pow b 2) (pow c 3)) (* 3648 (pow a 3) (pow c 2)) (* 324 b c (pow a 2)) (* 3584 a b (pow c 3))) 2)) (* -4416 a (pow c 4)) (* -4416 b (pow a 4)) (* -4218 c (pow b 4)) (* -1472 a (pow b 4)) (* -1472 b (pow c 4)) (* -1344 (pow a 2) (pow c 3)) (* -1344 (pow a 3) (pow b 2)) (* -1274 c (pow a 4)) (* 4376 a c (pow b 3)) (* 4376 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)